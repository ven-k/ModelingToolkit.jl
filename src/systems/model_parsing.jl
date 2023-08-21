struct Model{F, S}
    f::F
    structure::S
    isconnector::Bool
end
(m::Model)(args...; kw...) = m.f(args...; kw...)

for f in (:connector, :mtkmodel)
    @eval begin
        macro $f(name::Symbol, body)
            esc($(Symbol(f, :_macro))(__module__, name, body))
        end
    end
end

@inline is_kwarg(::Symbol) = false
@inline is_kwarg(e::Expr) = (e.head == :parameters)

function connector_macro(mod, name, body)
    if !Meta.isexpr(body, :block)
        err = """
        connector body must be a block! It should be in the form of
        ```
        @connector Pin begin
            v(t) = 1
            (i(t) = 1), [connect = Flow]
        end
        ```
        """
        error(err)
    end
    vs = []
    kwargs = []
    icon = Ref{Union{String, URI}}()
    dict = Dict{Symbol, Any}()
    dict[:kwargs] = Dict{Symbol, Any}()
    expr = Expr(:block)
    for arg in body.args
        arg isa LineNumberNode && continue
        if arg.head == :macrocall && arg.args[1] == Symbol("@icon")
            parse_icon!(icon, dict, dict, arg.args[end])
            continue
        end
        parse_variable_arg!(expr, vs, dict, mod, arg, :variables, kwargs)
    end
    iv = get(dict, :independent_variable, nothing)
    if iv === nothing
        error("$name doesn't have a independent variable")
    end
    gui_metadata = isassigned(icon) ? GUIMetadata(GlobalRef(mod, name), icon[]) :
                   GUIMetadata(GlobalRef(mod, name))

    quote
        $name = $Model((; name, $(kwargs...)) -> begin
                $expr
                var"#___sys___" = $ODESystem($(Equation[]), $iv, [$(vs...)], $([]);
                    name, gui_metadata = $gui_metadata)
                $Setfield.@set!(var"#___sys___".connector_type=$connector_type(var"#___sys___"))
            end, $dict, true)
    end
end

function parse_variable_def!(dict, mod, arg, varclass, kwargs, def = nothing)
    metatypes = [(:connection_type, VariableConnectType),
        (:description, VariableDescription),
        (:unit, VariableUnit),
        (:bounds, VariableBounds),
        (:noise, VariableNoiseType),
        (:input, VariableInput),
        (:output, VariableOutput),
        (:irreducible, VariableIrreducible),
        (:state_priority, VariableStatePriority),
        (:misc, VariableMisc),
        (:disturbance, VariableDisturbance),
        (:tunable, VariableTunable),
        (:dist, VariableDistribution),
        (:binary, VariableBinary),
        (:integer, VariableInteger)]

    arg isa LineNumberNode && return
    MLStyle.@match arg begin
        a::Symbol => begin
            push!(kwargs, Expr(:kw, a, nothing))
            var = generate_var!(dict, a, varclass)
            dict[:kwargs][getname(var)] = def
            (var, nothing)
        end
        Expr(:call, a, b) => begin
            push!(kwargs, Expr(:kw, a, nothing))
            var = generate_var!(dict, a, b, varclass)
            dict[:kwargs][getname(var)] = def
            (var, nothing)
        end
        Expr(:(=), a, b) => begin
            Base.remove_linenums!(b)
            def, meta = parse_default(mod, b)
            var, _ = parse_variable_def!(dict, mod, a, varclass, kwargs, def)
            dict[varclass][getname(var)][:default] = def
            if meta !== nothing
                for (type, key) in metatypes
                    if (mt = get(meta, key, nothing)) !== nothing
                        key == VariableConnectType && (mt = nameof(mt))
                        dict[varclass][getname(var)][type] = mt
                    end
                end
                var = set_var_metadata(var, meta)
            end
            (var, def)
        end
        Expr(:tuple, a, b) => begin
            var, def = parse_variable_def!(dict, mod, a, varclass, kwargs)
            meta = parse_metadata(mod, b)
            if meta !== nothing
                for (type, key) in metatypes
                    if (mt = get(meta, key, nothing)) !== nothing
                        key == VariableConnectType && (mt = nameof(mt))
                        dict[varclass][getname(var)][type] = mt
                    end
                end
                var = set_var_metadata(var, meta)
            end
            (set_var_metadata(var, meta), def)
        end
        _ => error("$arg cannot be parsed")
    end
end

function generate_var(a, varclass)
    var = Symbolics.variable(a)
    if varclass == :parameters
        var = toparam(var)
    end
    var
end

function generate_var!(dict, a, varclass)
    #var = generate_var(Symbol("#", a), varclass)
    var = generate_var(a, varclass)
    vd = get!(dict, varclass) do
        Dict{Symbol, Dict{Symbol, Any}}()
    end
    vd[a] = Dict{Symbol, Any}()
    var
end

function generate_var!(dict, a, b, varclass)
    iv = generate_var(b, :variables)
    prev_iv = get!(dict, :independent_variable) do
        iv
    end
    @assert isequal(iv, prev_iv)
    vd = get!(dict, varclass) do
        Dict{Symbol, Dict{Symbol, Any}}()
    end
    vd[a] = Dict{Symbol, Any}()
    var = Symbolics.variable(a, T = SymbolicUtils.FnType{Tuple{Real}, Real})(iv)
    if varclass == :parameters
        var = toparam(var)
    end
    var
end

function parse_default(mod, a)
    a = Base.remove_linenums!(deepcopy(a))
    MLStyle.@match a begin
        Expr(:block, x) => parse_default(mod, x)
        Expr(:tuple, x, y) => begin
            def, _ = parse_default(mod, x)
            meta = parse_metadata(mod, y)
            (def, meta)
        end
        ::Symbol || ::Number => (a, nothing)
        Expr(:call, a...) => begin
            def = parse_default.(Ref(mod), a)
            expr = Expr(:call)
            for (d, _) in def
                push!(expr.args, d)
            end
            (expr, nothing)
        end
        Expr(:if, condition::Expr, x, y) => begin
            if condition.args[1] in (:(==), :(<), :(>))
                op = compare_op(condition.args[1])
                expr = Expr(:call)
                push!(expr.args, op)
                for cond in condition.args[2:end]
                    cond isa Symbol ? push!(expr.args, :($getdefault($cond))) :
                    push!(expr.args, cond)
                end
                a.args[1] = expr
            end
            (a, nothing)
        end
        Expr(:if, condition::Bool, x, y) => begin
            xarg = x isa Symbol ? :($getdefault($x)) : x
            yarg = y isa Symbol ? :($getdefault($y)) : y
            condition ? (xarg, nothing) : (yarg, nothing)

        end
        Expr(:if, condition::Symbol, x, y) => begin
            xarg = x isa Symbol ? :($getdefault($x)) : x
            yarg = y isa Symbol ? :($getdefault($y)) : y
            a.args[1] = :($getdefault($condition))
            a.args[2] = xarg
            a.args[3] = yarg
            (a, nothing)
        end
        _ => error("Cannot parse default $a $(typeof(a))")
    end
end

compare_op(a) = if a == :(==)
    :isequal
elseif a == :(<)
    :isless
elseif a == :(>)
    :(Base.isgreater)
end

function morph_with_default!(eq; ret_eq = deepcopy(eq))
    # Base.remove_linenums!(eq)
    # @info 22 eq
    # @info 223 ret_eq
    for i in 1:lastindex(eq.args)
        # @info "At start of $(eq.args[i]): the" ret_eq
        # @info "Vals" ret_eq.args[i]
        eq.args[i] isa Expr && morph_with_default!(eq.args[i]; ret_eq = ret_eq.args[i])
        eq.args[i] isa Symbol && eq.args[i] != :! && (ret_eq.args[i] = :($getdefault($(eq.args[i]))))
        # @info 229 ret_eq.args
        # @info "The arg is $(eq.args[i]) and $(ret_eq.args[i])"
        # @info "At the end of $(eq.args[i]): the" ret_eq "\n\n"
    end
    ret_eq
end

function parse_metadata(mod, a)
    MLStyle.@match a begin
        Expr(:vect, eles...) => Dict(parse_metadata(mod, e) for e in eles)
        Expr(:(=), a, b) => Symbolics.option_to_metadata_type(Val(a)) => get_var(mod, b)
        _ => error("Cannot parse metadata $a")
    end
end

function set_var_metadata(a, ms)
    for (m, v) in ms
        a = setmetadata(a, m, v)
    end
    a
end

function get_var(mod::Module, b)
    b isa Symbol ? getproperty(mod, b) : b
end

function mtkmodel_macro(mod, name, expr)
    exprs = Expr(:block)
    dict = Dict{Symbol, Any}()
    dict[:kwargs] = Dict{Symbol, Any}()
    comps = Symbol[]
    ext = Ref{Any}(nothing)
    eqs = Expr[]
    icon = Ref{Union{String, URI}}()
    vs = []
    ps = []
    kwargs = []
    push!(exprs.args, :(systems = []))
    for arg in expr.args
        arg isa LineNumberNode && continue
        if arg.head == :macrocall
            parse_model!(exprs.args, comps, ext, eqs, icon, vs, ps,
                dict, mod, arg, kwargs)
        elseif arg.head == :block
            Base.remove_linenums!(arg)
            for a in arg.args
                @info Meta.isexpr(a, :macrocall) #&& parse_model!(exprs.args, comps, ext, eqs, icon, vs, ps,
                #dict, mod, arg, kwargs) || push!(exprs.args, arg)
            end
        else
            error("$arg is not valid syntax. Expected a macro call.")
        end
    end
    iv = get(dict, :independent_variable, nothing)
    if iv === nothing
        iv = dict[:independent_variable] = variable(:t)
    end

    # push!(exprs.args, :(@info systems))
    push!(exprs.args, :(push!(systems, $(comps...))))

    gui_metadata = isassigned(icon) > 0 ? GUIMetadata(GlobalRef(mod, name), icon[]) :
                   GUIMetadata(GlobalRef(mod, name))
    # push!(expr.args, :(push!($systems, $(comps...))))
    sys = :($ODESystem($Equation[$(eqs...)], $iv, [$(vs...)], [$(ps...)];
        systems, name, gui_metadata = $gui_metadata)) #, defaults = $defaults))
    if ext[] === nothing
        push!(exprs.args, sys)
    else
        push!(exprs.args, :($extend($sys, $(ext[]))))
    end

    @info 237 "kwargs $kwargs"
    @info "expr:" exprs
    f = :($(Symbol(:__, name, :__))(; name, $(kwargs...)) = $exprs)
    :($name = $Model($f, $dict, false))
end

function parse_model!(exprs, comps, ext, eqs, icon, vs, ps, dict,
    mod, arg, kwargs)
    mname = arg.args[1]
    body = arg.args[end]
    if mname == Symbol("@components")
        parse_components!(exprs, comps, dict, body, kwargs)
    elseif mname == Symbol("@extend")
        parse_extend!(exprs, ext, dict, body, kwargs)
    elseif mname == Symbol("@variables")
        parse_variables!(exprs, vs, dict, mod, body, :variables, kwargs)
    elseif mname == Symbol("@parameters")
        parse_variables!(exprs, ps, dict, mod, body, :parameters, kwargs)
    elseif mname == Symbol("@equations")
        parse_equations!(exprs, eqs, dict, body)
    elseif mname == Symbol("@icon")
        parse_icon!(icon, dict, mod, body)
    else
        error("$mname is not handled.")
    end
end

function _parse_components!(body, kwargs)
    expr = Expr(:block)
    comps = Vector{Symbol}[]
    comp_names = []
    for arg in body.args
        arg isa LineNumberNode && continue
        MLStyle.@match arg begin
            Expr(:(=), a, b) => begin
                arg = deepcopy(arg)
                b = deepcopy(arg.args[2])

                component_args!(a, b, expr, kwargs)

                push!(b.args, Expr(:kw, :name, Meta.quot(a)))
                arg.args[2] = b

                push!(expr.args, arg)
                push!(comp_names, a)
                push!(comps, [a, b.args[1]])
            end
            _ => @info 333 "Couldn't parse the component body: $arg"
        end
    end
    return comp_names, comps, expr
end

#=
function handle_if!(condition, x)
    ifexpr = Expr(:if)
    handle_if_block!(ifexpr, x, kwargs, condition)
    push!(exprs, ifexpr)
end

function handle_if!(condition, x, y)
    ifexpr = Expr(:if)
    handle_if_block!(ifexpr, x, kwargs, condition)
    handle_if_block!(ifexpr, y, kwargs, nothing)
    push!(exprs, ifexpr)
end
=#

# this was handle_if_block
function handle_if!(ifexpr, x, kwargs, condition = nothing)
    @info 370 ifexpr
    # push!(ifexpr.args, :($substitute_defaults($condition)))
    if condition isa Symbol
        push!(ifexpr.args, :($getdefault($condition)))
    elseif condition isa Num
        push!(ifexpr.args, :($substitute_defaults($condition)))
    elseif condition isa Expr
        push!(ifexpr.args, :($morph_with_default!($condition)))
    else
        @info "Don't know what to do with $(typeof(condition))"
    end
    comp_names, comps, expr_vec = _parse_components!(x, kwargs)
    push_conditional_component!(ifexpr, expr_vec, comp_names)
    # @info 379 ifexpr
    comps
end

function handle_if_y!(ifexpr, y, kwargs)
    Base.remove_linenums!(y)
    if Meta.isexpr(y, :elseif)
        comps = [:elseif, y.args[1]]
        elseifexpr = Expr(:elseif)
        push!(comps, handle_if!(elseifexpr, y.args[2], kwargs, y.args[1]))
        push!(comps, handle_if_y!(elseifexpr, y.args[3], kwargs))

        push!(ifexpr.args, elseifexpr)
        (comps...,)
    else
        comp_names, comps, expr_vec = _parse_components!(y, kwargs)
        push_conditional_component!(ifexpr, expr_vec, comp_names)
        comps
    end
end

function substitute_defaults(eq)
    varlist = get_variables(eq)
    substitute(eq, Dict(varlist .=> getdefault.(varlist)))
end

function push_conditional_component!(ifexpr, expr_vec, comp_names)
    blk = Expr(:block)
    # @info 365 expr_vec

    push!(blk.args, :($(expr_vec.args...)))
    push!(blk.args, :($push!(systems, $(comp_names...))))
    # @info 366 blk
    push!(ifexpr.args, blk)
end

function parse_components!(exprs, cs, dict, compbody, kwargs)
    dict[:components] = []
    Base.remove_linenums!(compbody)
    for arg in compbody.args
        MLStyle.@match arg begin
            Expr(:if, condition, x) => begin
            # comp_names, comps, expr_vec = _parse_components!(x, kwargs)
                ifexpr = Expr(:if)
                comps = handle_if!(ifexpr, x, kwargs, condition)
                push!(exprs, ifexpr)
                push!(dict[:components], (:if, condition, comps, []))
            end
            Expr(:if, condition, x, y) => begin
                ifexpr = Expr(:if)
                comps = handle_if!(ifexpr, x, kwargs, condition)
                ycomps = handle_if_y!(ifexpr, y, kwargs)
                # @info 482 ycomps
                push!(exprs, ifexpr)
                push!(dict[:components], (:if, condition, comps, ycomps))
            end
            Expr(:(=), a, b) => begin
                comp_names, comps, expr_vec = _parse_components!(:(begin $arg end), kwargs)
                push!(cs, comp_names...)
                push!(dict[:components], comps...)
                push!(exprs, expr_vec.args...)
            end
            _ => @info "410 Couldn't parse the component body $arg"
        end
    end
end

function _rename(compname, varname)
    compname = Symbol(compname, :__, varname)
end

function component_args!(a, b, expr, kwargs)
    # Whenever `b` is a function call, skip the first arg aka the function name.
    # Whenver it is a kwargs list, include it.
    start = b.head == :call ? 2 : 1
    for i in start:lastindex(b.args)
        arg = b.args[i]
        arg isa LineNumberNode && continue
        MLStyle.@match arg begin
            x::Symbol || Expr(:kw, x) => begin
                _v = _rename(a, x)
                b.args[i] = Expr(:kw, x, _v)
                push!(kwargs, Expr(:kw, _v, nothing))
            end
            Expr(:parameters, x...) => begin
                component_args!(a, arg, expr, kwargs)
            end
            Expr(:kw, x) => begin
                _v = _rename(a, x)
                b.args[i] = Expr(:kw, x, _v)
                push!(kwargs, _v, nothing)
            end
            Expr(:kw, x, y::Number) => begin
                _v = _rename(a, x)
                b.args[i] = Expr(:kw, x, _v)
                push!(kwargs, Expr(:kw, _v, y))
            end
            Expr(:kw, x, y) => begin
                _v = _rename(a, x)
                push!(expr.args, :($_v = $y))
                def = Expr(:kw)
                push!(def.args, x)
                push!(def.args, :($getdefault($_v)))
                b.args[i] = def
                # b.args[i] = Expr(:kw, x, _v)
                push!(kwargs, Expr(:kw, _v, nothing))
            end
            _ => error("Could not parse $arg of component $a")
        end
    end
end

function parse_extend!(exprs, ext, dict, body, kwargs)
    expr = Expr(:block)
    push!(exprs, expr)
    body = deepcopy(body)
    MLStyle.@match body begin
        Expr(:(=), a, b) => begin
            vars = nothing
            if Meta.isexpr(b, :(=))
                vars = a
                if !Meta.isexpr(vars, :tuple)
                    error("`@extend` destructuring only takes an tuple as LHS. Got $body")
                end
                a, b = b.args
                @info 398  vars a b
                # parse and work on b

                component_args!(a, b, expr, kwargs)

                vars, a, b
            end
            ext[] = a
            push!(b.args, Expr(:kw, :name, Meta.quot(a)))
            dict[:extend] = [Symbol.(vars.args), a, b.args[1]]
            push!(expr.args, :($a = $b))
            if vars !== nothing
                push!(expr.args, :(@unpack $vars = $a))
            end
        end
        _ => error("`@extend` only takes an assignment expression. Got $body")
    end
end

function parse_variable_arg!(expr, vs, dict, mod, arg, varclass, kwargs)
    vv, def = parse_variable_def!(dict, mod, arg, varclass, kwargs)
    v = Num(vv)
    name = getname(v)
    push!(vs, name)
    push!(expr.args,
        :($name = $name === nothing ? $setdefault($vv, $def) : $setdefault($vv, $name)))
end

function parse_variables!(exprs, vs, dict, mod, body, varclass, kwargs)
    expr = Expr(:block)
    push!(exprs, expr)
    for arg in body.args
        arg isa LineNumberNode && continue
        parse_variable_arg!(expr, vs, dict, mod, arg, varclass, kwargs)
    end
end

function parse_equations!(exprs, eqs, dict, body)
    for arg in body.args
        arg isa LineNumberNode && continue
        push!(eqs, arg)
    end
    # TODO: does this work with TOML?
    dict[:equations] = readable_code.(eqs)
end

function parse_icon!(icon, dict, mod, body::String)
    icon_dir = get(ENV, "MTK_ICONS_DIR", joinpath(DEPOT_PATH[1], "mtk_icons"))
    dict[:icon] = icon[] = if isfile(body)
        URI("file:///" * abspath(body))
    elseif (iconpath = joinpath(icon_dir, body); isfile(iconpath))
        URI("file:///" * abspath(iconpath))
    elseif try
        Base.isvalid(URI(body))
    catch e
        false
    end
        URI(body)
    else
        error("$body is not a valid icon")
    end
end

function parse_icon!(icon, dict, mod, body::Expr)
    _icon = body.args[end]
    dict[:icon] = icon[] = MLStyle.@match _icon begin
        ::Symbol => get_var(mod, _icon)
        ::String => _icon
        Expr(:call, read, a...) => eval(_icon)
        _ => error("$_icon isn't a valid icon")
    end
end
