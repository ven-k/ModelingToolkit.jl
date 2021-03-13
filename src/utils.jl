function make_operation(@nospecialize(op), args)
    if op === (*)
        args = filter(!_isone, args)
        if isempty(args)
            return 1
        end
    elseif op === (+)
        args = filter(!_iszero, args)
        if isempty(args)
            return 0
        end
    end
    return op(args...)
end

function detime_dvs(op)
    if !istree(op)
        op
    elseif operation(op) isa Sym
        Sym{Real}(nameof(operation(op)))
    else
        similarterm(op, operation(op),detime_dvs.(arguments(op)))
    end
end

function retime_dvs(op::Sym,dvs,iv)
    Sym{FnType{Tuple{symtype(iv)}, Real}}(nameof(op))(iv)
end

function retime_dvs(op, dvs, iv)
    istree(op) ?
        similarterm(op, operation(op), retime_dvs.(arguments(op),(dvs,),(iv,))) :
        op
end

modified_states!(mstates, e::Equation, statelist=nothing) = get_variables!(mstates, e.lhs, statelist)

macro showarr(x)
    n = string(x)
    quote
        y = $(esc(x))
        println($n, " = ", summary(y))
        Base.print_array(stdout, y)
        println()
        y
    end
end

@deprecate substitute_expr!(expr,s) substitute(expr,s)

function states_to_sym(states::Set)
    function _states_to_sym(O)
        if O isa Equation
            Expr(:(=), _states_to_sym(O.lhs), _states_to_sym(O.rhs))
        elseif istree(O)
            op = operation(O)
            args = arguments(O)
            if op isa Sym
                O in states && return tosymbol(O)
                # dependent variables
                return build_expr(:call, Any[nameof(op); _states_to_sym.(args)])
            else
                canonical, O = canonicalexpr(O)
                return canonical ? O : build_expr(:call, Any[op; _states_to_sym.(args)])
            end
        elseif O isa Num
            return _states_to_sym(value(O))
        else
            return toexpr(O)
        end
    end
end
states_to_sym(states) = states_to_sym(Set(states))

"""
    toparam(s::Sym) -> Sym{<:Parameter}

Maps the variable to a paramter.
"""
toparam(s::Sym) = Sym{Parameter{symtype(s)}}(s.name)
toparam(s::Sym{<:Parameter}) = s

"""
    tovar(s::Sym) -> Sym{Real}
    tovar(s::Sym{<:Parameter}) -> Sym{Real}

Maps the variable to a state.
"""
tovar(s::Sym{<:Parameter}) = Sym{symtype(s)}(s.name)
tovar(s::Sym) = s

function lower_mapnames(umap::AbstractArray{T}) where {T<:Pair}
    T[value(k) => value(v) for (k, v) in umap]
end
function lower_mapnames(umap::AbstractArray{T},name) where {T<:Pair}
    T[lower_varname(value(k), name) => value(v) for (k, v) in umap]
end
function lower_mapnames(umap::NTuple{N,T}) where {N,T<:Pair}
    ntuple(i->value(umap[i][1]) => value(umap[i][2]),N)
end
function lower_mapnames(umap::NTuple{N,T},name) where {N,T<:Pair}
    ntuple(i->lower_varname(value(umap[i][1]), name) => value(umap[i][2]),N)
end

lower_mapnames(umap::AbstractArray) = umap # Ambiguity
lower_mapnames(umap::AbstractArray,name) = umap
lower_mapnames(umap::Tuple) = umap
lower_mapnames(umap::Tuple, name) = umap