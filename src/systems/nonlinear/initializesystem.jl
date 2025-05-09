"""
$(TYPEDSIGNATURES)

Generate `NonlinearSystem` which initializes a problem from specified initial conditions of an `AbstractTimeDependentSystem`.
"""
function generate_initializesystem(sys::AbstractTimeDependentSystem;
        u0map = Dict(),
        pmap = Dict(),
        initialization_eqs = [],
        guesses = Dict(),
        default_dd_guess = Bool(0),
        algebraic_only = false,
        check_units = true, check_defguess = false,
        name = nameof(sys), extra_metadata = (;), kwargs...)
    eqs = equations(sys)
    if !(eqs isa Vector{Equation})
        eqs = Equation[x for x in eqs if x isa Equation]
    end
    trueobs, eqs = unhack_observed(observed(sys), eqs)
    # remove any observed equations that directly or indirectly contain
    # delayed unknowns
    isempty(trueobs) || filter_delay_equations_variables!(sys, trueobs)
    vars = unique([unknowns(sys); getfield.(trueobs, :lhs)])
    vars_set = Set(vars) # for efficient in-lookup

    eqs_ics = Equation[]
    defs = copy(defaults(sys)) # copy so we don't modify sys.defaults
    additional_guesses = anydict(guesses)
    additional_initialization_eqs = Vector{Equation}(initialization_eqs)
    guesses = merge(get_guesses(sys), additional_guesses)
    idxs_diff = isdiffeq.(eqs)

    # PREPROCESSING
    u0map = copy(anydict(u0map))
    pmap = anydict(pmap)
    initsys_preprocessing!(u0map, defs)

    # 1) Use algebraic equations of system as initialization constraints
    idxs_alge = .!idxs_diff
    append!(eqs_ics, eqs[idxs_alge]) # start equation list with algebraic equations

    eqs_diff = eqs[idxs_diff]
    D = Differential(get_iv(sys))
    diffmap = merge(
        Dict(eq.lhs => eq.rhs for eq in eqs_diff),
        Dict(D(eq.lhs) => D(eq.rhs) for eq in trueobs)
    )

    if has_schedule(sys) && (schedule = get_schedule(sys); !isnothing(schedule))
        # 2) process dummy derivatives and u0map into initialization system
        # prepare map for dummy derivative substitution
        for x in filter(x -> !isnothing(x[1]), schedule.dummy_sub)
            # set dummy derivatives to default_dd_guess unless specified
            push!(defs, x[1] => get(guesses, x[1], default_dd_guess))
        end
        function process_u0map_with_dummysubs(y, x)
            y = get(schedule.dummy_sub, y, y)
            y = fixpoint_sub(y, diffmap)
            # If we have `D(x) ~ x` and provide [D(x) => x, x => 1.0] to `u0map`, then
            # without this condition `defs` would get `x => x` instead of retaining
            # `x => 1.0`.
            isequal(y, x) && return
            if y ∈ vars_set
                # variables specified in u0 overrides defaults
                push!(defs, y => x)
            elseif y isa Symbolics.Arr
                # TODO: don't scalarize arrays
                merge!(defs, Dict(scalarize(y .=> x)))
            elseif y isa Symbolics.BasicSymbolic
                # y is a derivative expression expanded; add it to the initialization equations
                push!(eqs_ics, y ~ x)
            else
                error("Initialization expression $y is currently not supported. If its a higher order derivative expression, then only the dummy derivative expressions are supported.")
            end
        end
        for (y, x) in u0map
            if Symbolics.isarraysymbolic(y)
                process_u0map_with_dummysubs.(collect(y), collect(x))
            else
                process_u0map_with_dummysubs(y, x)
            end
        end
    else
        # 2) System doesn't have a schedule, so dummy derivatives don't exist/aren't handled (SDESystem)
        for (k, v) in u0map
            defs[k] = v
        end
    end

    # 3) process other variables
    for var in vars
        if var ∈ keys(defs)
            push!(eqs_ics, var ~ defs[var])
        elseif var ∈ keys(guesses)
            push!(defs, var => guesses[var])
        elseif check_defguess
            error("Invalid setup: variable $(var) has no default value or initial guess")
        end
    end

    # 4) process explicitly provided initialization equations
    if !algebraic_only
        initialization_eqs = [get_initialization_eqs(sys); initialization_eqs]
        for eq in initialization_eqs
            eq = fixpoint_sub(eq, diffmap) # expand dummy derivatives
            push!(eqs_ics, eq)
        end
    end

    # 5) process parameters as initialization unknowns
    paramsubs = setup_parameter_initialization!(
        sys, pmap, defs, guesses, eqs_ics; check_defguess)

    # 6) parameter dependencies become equations, their LHS become unknowns
    # non-numeric dependent parameters stay as parameter dependencies
    new_parameter_deps = solve_parameter_dependencies!(
        sys, paramsubs, eqs_ics, defs, guesses)

    # 7) handle values provided for dependent parameters similar to values for observed variables
    handle_dependent_parameter_constraints!(sys, pmap, eqs_ics, paramsubs)

    # parameters do not include ones that became initialization unknowns
    pars = Vector{SymbolicParam}(filter(
        p -> !haskey(paramsubs, p), parameters(sys; initial_parameters = true)))
    push!(pars, get_iv(sys))

    # 8) use observed equations for guesses of observed variables if not provided
    for eq in trueobs
        haskey(defs, eq.lhs) && continue
        any(x -> isequal(default_toterm(x), eq.lhs), keys(defs)) && continue

        defs[eq.lhs] = eq.rhs
    end
    append!(eqs_ics, trueobs)

    vars = [vars; collect(values(paramsubs))]

    # even if `p => tovar(p)` is in `paramsubs`, `isparameter(p[1]) === true` after substitution
    # so add scalarized versions as well
    scalarize_varmap!(paramsubs)

    eqs_ics = Symbolics.substitute.(eqs_ics, (paramsubs,))
    for k in keys(defs)
        defs[k] = substitute(defs[k], paramsubs)
    end
    meta = InitializationSystemMetadata(
        anydict(u0map), anydict(pmap), additional_guesses,
        additional_initialization_eqs, extra_metadata, nothing)
    return NonlinearSystem(eqs_ics,
        vars,
        pars;
        defaults = defs,
        checks = check_units,
        parameter_dependencies = new_parameter_deps,
        name,
        metadata = meta,
        kwargs...)
end

"""
$(TYPEDSIGNATURES)

Generate `NonlinearSystem` which initializes a problem from specified initial conditions of an `AbstractTimeDependentSystem`.
"""
function generate_initializesystem(sys::AbstractTimeIndependentSystem;
        u0map = Dict(),
        pmap = Dict(),
        initialization_eqs = [],
        guesses = Dict(),
        algebraic_only = false,
        check_units = true, check_defguess = false,
        name = nameof(sys), extra_metadata = (;), kwargs...)
    eqs = equations(sys)
    trueobs, eqs = unhack_observed(observed(sys), eqs)
    vars = unique([unknowns(sys); getfield.(trueobs, :lhs)])
    vars_set = Set(vars) # for efficient in-lookup

    eqs_ics = Equation[]
    defs = copy(defaults(sys)) # copy so we don't modify sys.defaults
    additional_guesses = anydict(guesses)
    additional_initialization_eqs = Vector{Equation}(initialization_eqs)
    guesses = merge(get_guesses(sys), additional_guesses)

    # PREPROCESSING
    u0map = copy(anydict(u0map))
    pmap = anydict(pmap)
    initsys_preprocessing!(u0map, defs)

    # Calculate valid `Initial` parameters. These are unknowns for
    # which constant initial values were provided. By this point,
    # they have been separated into `x => Initial(x)` in `u0map`
    # and `Initial(x) => val` in `pmap`.
    valid_initial_parameters = Set{BasicSymbolic}()
    for (k, v) in u0map
        isequal(Initial(k), v) || continue
        push!(valid_initial_parameters, v)
    end

    # get the initialization equations
    if !algebraic_only
        initialization_eqs = [get_initialization_eqs(sys); initialization_eqs]
    end

    # only include initialization equations where all the involved `Initial`
    # parameters are valid.
    vs = Set()
    initialization_eqs = filter(initialization_eqs) do eq
        empty!(vs)
        vars!(vs, eq; op = Initial)
        non_params = filter(!isparameter, vs)
        # error if non-parameters are present in the initialization equations
        if !isempty(non_params)
            throw(UnknownsInTimeIndependentInitializationError(eq, non_params))
        end
        filter!(x -> iscall(x) && isinitial(x), vs)
        invalid_initials = setdiff(vs, valid_initial_parameters)
        return isempty(invalid_initials)
    end

    append!(eqs_ics, initialization_eqs)

    # process parameters as initialization unknowns
    paramsubs = setup_parameter_initialization!(
        sys, pmap, defs, guesses, eqs_ics; check_defguess)

    # parameter dependencies become equations, their LHS become unknowns
    # non-numeric dependent parameters stay as parameter dependencies
    new_parameter_deps = solve_parameter_dependencies!(
        sys, paramsubs, eqs_ics, defs, guesses)

    # handle values provided for dependent parameters similar to values for observed variables
    handle_dependent_parameter_constraints!(sys, pmap, eqs_ics, paramsubs)

    # parameters do not include ones that became initialization unknowns
    pars = Vector{SymbolicParam}(filter(
        p -> !haskey(paramsubs, p), parameters(sys; initial_parameters = true)))
    vars = collect(values(paramsubs))

    # even if `p => tovar(p)` is in `paramsubs`, `isparameter(p[1]) === true` after substitution
    # so add scalarized versions as well
    scalarize_varmap!(paramsubs)

    eqs_ics = Symbolics.substitute.(eqs_ics, (paramsubs,))
    for k in keys(defs)
        defs[k] = substitute(defs[k], paramsubs)
    end
    meta = InitializationSystemMetadata(
        anydict(u0map), anydict(pmap), additional_guesses,
        additional_initialization_eqs, extra_metadata, nothing)
    return NonlinearSystem(eqs_ics,
        vars,
        pars;
        defaults = defs,
        checks = check_units,
        parameter_dependencies = new_parameter_deps,
        name,
        metadata = meta,
        kwargs...)
end

"""
    $(TYPEDSIGNATURES)

Preprocessing step for initialization. Currently removes key `k` from `defs` and `u0map`
if `k => nothing` is present in `u0map`.
"""
function initsys_preprocessing!(u0map::AbstractDict, defs::AbstractDict)
    for (k, v) in u0map
        v === nothing || continue
        delete!(defs, k)
    end
    filter_missing_values!(u0map)
end

"""
    $(TYPEDSIGNATURES)

Update `defs` and `eqs_ics` appropriately for parameter initialization. Return a dictionary
mapping solvable parameters to their `tovar` variants.
"""
function setup_parameter_initialization!(
        sys::AbstractSystem, pmap::AbstractDict, defs::AbstractDict,
        guesses::AbstractDict, eqs_ics::Vector{Equation}; check_defguess = false)
    paramsubs = Dict()
    for p in parameters(sys)
        if is_parameter_solvable(p, pmap, defs, guesses)
            # If either of them are `missing` the parameter is an unknown
            # But if the parameter is passed a value, use that as an additional
            # equation in the system
            _val1 = get_possibly_array_fallback_singletons(pmap, p)
            _val2 = get_possibly_array_fallback_singletons(defs, p)
            _val3 = get_possibly_array_fallback_singletons(guesses, p)
            varp = tovar(p)
            paramsubs[p] = varp
            # Has a default of `missing`, and (either an equation using the value passed to `ODEProblem` or a guess)
            if _val2 === missing
                if _val1 !== nothing && _val1 !== missing
                    push!(eqs_ics, varp ~ _val1)
                    push!(defs, varp => _val1)
                elseif _val3 !== nothing
                    # assuming an equation exists (either via algebraic equations or initialization_eqs)
                    push!(defs, varp => _val3)
                elseif check_defguess
                    error("Invalid setup: parameter $(p) has no default value, initial value, or guess")
                end
                # `missing` passed to `ODEProblem`, and (either an equation using default or a guess)
            elseif _val1 === missing
                if _val2 !== nothing && _val2 !== missing
                    push!(eqs_ics, varp ~ _val2)
                    push!(defs, varp => _val2)
                elseif _val3 !== nothing
                    push!(defs, varp => _val3)
                elseif check_defguess
                    error("Invalid setup: parameter $(p) has no default value, initial value, or guess")
                end
                # given a symbolic value to ODEProblem
            elseif symbolic_type(_val1) != NotSymbolic() || is_array_of_symbolics(_val1)
                push!(eqs_ics, varp ~ _val1)
                push!(defs, varp => _val3)
                # No value passed to `ODEProblem`, but a default and a guess are present
                # _val2 !== missing is implied by it falling this far in the elseif chain
            elseif _val1 === nothing && _val2 !== nothing
                push!(eqs_ics, varp ~ _val2)
                push!(defs, varp => _val3)
            else
                # _val1 !== missing and _val1 !== nothing, so a value was provided to ODEProblem
                # This would mean `is_parameter_solvable` returned `false`, so we never end up
                # here
                error("This should never be reached")
            end
        end
    end

    return paramsubs
end

"""
    $(TYPEDSIGNATURES)

Add appropriate parameter dependencies as initialization equations. Return the new list of
parameter dependencies for the initialization system.
"""
function solve_parameter_dependencies!(sys::AbstractSystem, paramsubs::AbstractDict,
        eqs_ics::Vector{Equation}, defs::AbstractDict, guesses::AbstractDict)
    new_parameter_deps = Equation[]
    for eq in parameter_dependencies(sys)
        if !is_variable_floatingpoint(eq.lhs)
            push!(new_parameter_deps, eq)
            continue
        end
        varp = tovar(eq.lhs)
        paramsubs[eq.lhs] = varp
        push!(eqs_ics, eq)
        guessval = get(guesses, eq.lhs, eq.rhs)
        push!(defs, varp => guessval)
    end

    return new_parameter_deps
end

"""
    $(TYPEDSIGNATURES)

Turn values provided for parameter dependencies into initialization equations.
"""
function handle_dependent_parameter_constraints!(sys::AbstractSystem, pmap::AbstractDict,
        eqs_ics::Vector{Equation}, paramsubs::AbstractDict)
    for (k, v) in merge(defaults(sys), pmap)
        if is_variable_floatingpoint(k) && has_parameter_dependency_with_lhs(sys, k)
            push!(eqs_ics, paramsubs[k] ~ v)
        end
    end

    return nothing
end

"""
    $(TYPEDSIGNATURES)

Get a new symbolic variable of the same type and size as `sym`, which is a parameter.
"""
function get_initial_value_parameter(sym)
    sym = default_toterm(unwrap(sym))
    name = hasname(sym) ? getname(sym) : Symbol(sym)
    if iscall(sym) && operation(sym) === getindex
        name = Symbol(name, :_, join(arguments(sym)[2:end], "_"))
    end
    name = Symbol(name, :ₘₜₖ_₀)
    newvar = unwrap(similar_variable(sym, name; use_gensym = false))
    return toparam(newvar)
end

"""
    $(TYPEDSIGNATURES)

Given `sys` and a list of observed equations `trueobs`, remove all the equations that
directly or indirectly contain a delayed unknown of `sys`.
"""
function filter_delay_equations_variables!(sys::AbstractSystem, trueobs::Vector{Equation})
    is_time_dependent(sys) || return trueobs
    banned_vars = Set()
    idxs_to_remove = Int[]
    for (i, eq) in enumerate(trueobs)
        _has_delays(sys, eq.rhs, banned_vars) || continue
        push!(idxs_to_remove, i)
        push!(banned_vars, eq.lhs)
    end
    return deleteat!(trueobs, idxs_to_remove)
end

"""
    $(TYPEDSIGNATURES)

Check if the expression `ex` contains a delayed unknown of `sys` or a term in
`banned`.
"""
function _has_delays(sys::AbstractSystem, ex, banned)
    ex = unwrap(ex)
    ex in banned && return true
    if symbolic_type(ex) == NotSymbolic()
        if is_array_of_symbolics(ex)
            return any(x -> _has_delays(sys, x, banned), ex)
        end
        return false
    end
    iscall(ex) || return false
    op = operation(ex)
    args = arguments(ex)
    if iscalledparameter(ex)
        return any(x -> _has_delays(sys, x, banned), args)
    end
    if issym(op) && length(args) == 1 && is_variable(sys, op(get_iv(sys))) &&
       iscall(args[1]) && get_iv(sys) in vars(args[1])
        return true
    end
    return any(x -> _has_delays(sys, x, banned), args)
end

struct ReconstructInitializeprob
    getter::Any
    setter::Any
end

function ReconstructInitializeprob(
        srcsys::AbstractSystem, dstsys::AbstractSystem)
    syms = reduce(
        vcat, reorder_parameters(dstsys, parameters(dstsys));
        init = [])
    getter = getu(srcsys, syms)
    setter = setp_oop(dstsys, syms)
    return ReconstructInitializeprob(getter, setter)
end

function (rip::ReconstructInitializeprob)(srcvalp, dstvalp)
    newp = rip.setter(dstvalp, rip.getter(srcvalp))
    if state_values(dstvalp) === nothing
        return nothing, newp
    end
    srcu0 = state_values(srcvalp)
    T = srcu0 === nothing || isempty(srcu0) ? Union{} : eltype(srcu0)
    if parameter_values(dstvalp) isa MTKParameters
        if !isempty(newp.tunable)
            T = promote_type(eltype(newp.tunable), T)
        end
    elseif !isempty(newp)
        T = promote_type(eltype(newp), T)
    end
    if T == eltype(state_values(dstvalp))
        u0 = state_values(dstvalp)
    elseif T != Union{}
        u0 = T.(state_values(dstvalp))
    end
    buf, repack, alias = SciMLStructures.canonicalize(SciMLStructures.Tunable(), newp)
    if eltype(buf) != T
        newbuf = similar(buf, T)
        copyto!(newbuf, buf)
        newp = repack(newbuf)
    end
    buf, repack, alias = SciMLStructures.canonicalize(SciMLStructures.Initials(), newp)
    if eltype(buf) != T
        newbuf = similar(buf, T)
        copyto!(newbuf, buf)
        newp = repack(newbuf)
    end
    return u0, newp
end

struct InitializationSystemMetadata
    u0map::Dict{Any, Any}
    pmap::Dict{Any, Any}
    additional_guesses::Dict{Any, Any}
    additional_initialization_eqs::Vector{Equation}
    extra_metadata::NamedTuple
    oop_reconstruct_u0_p::Union{Nothing, ReconstructInitializeprob}
end

function get_possibly_array_fallback_singletons(varmap, p)
    if haskey(varmap, p)
        return varmap[p]
    end
    if symbolic_type(p) == ArraySymbolic()
        is_sized_array_symbolic(p) || return nothing
        scal = collect(p)
        if all(x -> haskey(varmap, x), scal)
            res = [varmap[x] for x in scal]
            if any(x -> x === nothing, res)
                return nothing
            elseif any(x -> x === missing, res)
                return missing
            end
            return res
        end
    elseif iscall(p) && operation(p) == getindex
        arrp = arguments(p)[1]
        val = get_possibly_array_fallback_singletons(varmap, arrp)
        if val === nothing
            return nothing
        elseif val === missing
            return missing
        else
            return val
        end
    end
    return nothing
end

function is_parameter_solvable(p, pmap, defs, guesses)
    p = unwrap(p)
    is_variable_floatingpoint(p) || return false
    _val1 = pmap isa AbstractDict ? get_possibly_array_fallback_singletons(pmap, p) :
            nothing
    _val2 = get_possibly_array_fallback_singletons(defs, p)
    _val3 = get_possibly_array_fallback_singletons(guesses, p)
    # either (missing is a default or was passed to the ODEProblem) or (nothing was passed to
    # the ODEProblem and it has a default and a guess)
    return ((_val1 === missing || _val2 === missing) ||
            (symbolic_type(_val1) != NotSymbolic() || is_array_of_symbolics(_val1) ||
             _val1 === nothing && _val2 !== nothing)) && _val3 !== nothing
end

function SciMLBase.remake_initialization_data(
        sys::AbstractSystem, odefn, u0, t0, p, newu0, newp)
    if u0 === missing && p === missing
        return odefn.initialization_data
    end
    if !(eltype(u0) <: Pair) && !(eltype(p) <: Pair)
        oldinitdata = odefn.initialization_data
        oldinitdata === nothing && return nothing

        oldinitprob = oldinitdata.initializeprob
        oldinitprob === nothing && return nothing
        if !SciMLBase.has_sys(oldinitprob.f) || !(oldinitprob.f.sys isa NonlinearSystem)
            return oldinitdata
        end
        oldinitsys = oldinitprob.f.sys
        meta = get_metadata(oldinitsys)
        if meta isa InitializationSystemMetadata && meta.oop_reconstruct_u0_p !== nothing
            reconstruct_fn = meta.oop_reconstruct_u0_p
        else
            reconstruct_fn = ReconstructInitializeprob(sys, oldinitsys)
        end
        # the history function doesn't matter because `reconstruct_fn` is only going to
        # update the values of parameters, which aren't time dependent. The reason it
        # is called is because `Initial` parameters are calculated from the corresponding
        # state values.
        history_fn = is_time_dependent(sys) && !is_markovian(sys) ? Returns(newu0) : nothing
        new_initu0, new_initp = reconstruct_fn(
            ProblemState(; u = newu0, p = newp, t = t0, h = history_fn), oldinitprob)
        if oldinitprob.f.resid_prototype === nothing
            newf = oldinitprob.f
        else
            newf = NonlinearFunction{
                SciMLBase.isinplace(oldinitprob.f), SciMLBase.specialization(oldinitprob.f)}(
                oldinitprob.f;
                resid_prototype = calculate_resid_prototype(
                    length(oldinitprob.f.resid_prototype), new_initu0, new_initp))
        end
        initprob = remake(oldinitprob; f = newf, u0 = new_initu0, p = new_initp)
        return SciMLBase.OverrideInitData(initprob, oldinitdata.update_initializeprob!,
            oldinitdata.initializeprobmap, oldinitdata.initializeprobpmap)
    end
    dvs = unknowns(sys)
    ps = parameters(sys)
    u0map = to_varmap(u0, dvs)
    symbols_to_symbolics!(sys, u0map)
    add_toterms!(u0map)
    pmap = to_varmap(p, ps)
    symbols_to_symbolics!(sys, pmap)
    guesses = Dict()
    defs = defaults(sys)
    cmap, cs = get_cmap(sys)
    use_scc = true
    initialization_eqs = Equation[]

    if SciMLBase.has_initializeprob(odefn)
        oldsys = odefn.initialization_data.initializeprob.f.sys
        meta = get_metadata(oldsys)
        if meta isa InitializationSystemMetadata
            u0map = merge(meta.u0map, u0map)
            pmap = merge(meta.pmap, pmap)
            merge!(guesses, meta.additional_guesses)
            use_scc = get(meta.extra_metadata, :use_scc, true)
            initialization_eqs = meta.additional_initialization_eqs
        end
    else
        # there is no initializeprob, so the original problem construction
        # had no solvable parameters and had the differential variables
        # specified in `u0map`.
        if u0 === missing
            # the user didn't pass `u0` to `remake`, so they want to retain
            # existing values. Fill the differential variables in `u0map`,
            # initialization will either be elided or solve for the algebraic
            # variables
            diff_idxs = isdiffeq.(equations(sys))
            for i in eachindex(dvs)
                diff_idxs[i] || continue
                u0map[dvs[i]] = newu0[i]
            end
        end
        # ensure all unknowns have guesses in case they weren't given one
        # and become solvable
        for i in eachindex(dvs)
            haskey(guesses, dvs[i]) && continue
            guesses[dvs[i]] = newu0[i]
        end
        if p === missing
            # the user didn't pass `p` to `remake`, so they want to retain
            # existing values. Fill all parameters in `pmap` so that none of
            # them are solvable.
            for p in ps
                pmap[p] = getp(sys, p)(newp)
            end
        end
        # all non-solvable parameters need values regardless
        for p in ps
            haskey(pmap, p) && continue
            is_parameter_solvable(p, pmap, defs, guesses) && continue
            pmap[p] = getp(sys, p)(newp)
        end
    end
    if t0 === nothing && is_time_dependent(sys)
        t0 = 0.0
    end
    filter_missing_values!(u0map)
    filter_missing_values!(pmap)

    op, missing_unknowns, missing_pars = build_operating_point!(sys,
        u0map, pmap, defs, cmap, dvs, ps)
    floatT = float_type_from_varmap(op)
    kws = maybe_build_initialization_problem(
        sys, op, u0map, pmap, t0, defs, guesses, missing_unknowns;
        use_scc, initialization_eqs, floatT, allow_incomplete = true)

    return SciMLBase.remake_initialization_data(sys, kws, newu0, t0, newp, newu0, newp)
end

function SciMLBase.late_binding_update_u0_p(
        prob, sys::AbstractSystem, u0, p, t0, newu0, newp)
    supports_initialization(sys) || return newu0, newp
    u0 === missing && return newu0, (p === missing ? copy(newp) : newp)
    # non-symbolic u0 updates initials...
    if !(eltype(u0) <: Pair)
        # if `p` is not provided or is symbolic
        p === missing || eltype(p) <: Pair || return newu0, newp
        newu0 === nothing && return newu0, newp
        all(is_parameter(sys, Initial(x)) for x in unknowns(sys)) || return newu0, newp
        newp = p === missing ? copy(newp) : newp
        initials, repack, alias = SciMLStructures.canonicalize(
            SciMLStructures.Initials(), newp)
        if eltype(initials) != eltype(newu0)
            initials = DiffEqBase.promote_u0(initials, newu0, t0)
            newp = repack(initials)
        end
        if length(newu0) != length(unknowns(sys))
            throw(ArgumentError("Expected `newu0` to be of same length as unknowns ($(length(unknowns(sys)))). Got $(typeof(newu0)) of length $(length(newu0))"))
        end
        setp(sys, Initial.(unknowns(sys)))(newp, newu0)
        return newu0, newp
    end

    newp = p === missing ? copy(newp) : newp
    newu0 = DiffEqBase.promote_u0(newu0, newp, t0)
    tunables, repack, alias = SciMLStructures.canonicalize(SciMLStructures.Tunable(), newp)
    if eltype(tunables) != eltype(newu0)
        tunables = DiffEqBase.promote_u0(tunables, newu0, t0)
        newp = repack(tunables)
    end
    initials, repack, alias = SciMLStructures.canonicalize(SciMLStructures.Initials(), newp)
    if eltype(initials) != eltype(newu0)
        initials = DiffEqBase.promote_u0(initials, newu0, t0)
        newp = repack(initials)
    end

    allsyms = all_symbols(sys)
    for (k, v) in u0
        v === nothing && continue
        (symbolic_type(v) == NotSymbolic() && !is_array_of_symbolics(v)) || continue
        if k isa Symbol
            k2 = symbol_to_symbolic(sys, k; allsyms)
            # if it is returned as-is, there is no match so skip it
            k2 === k && continue
            k = k2
        end
        is_parameter(sys, Initial(k)) || continue
        setp(sys, Initial(k))(newp, v)
    end

    return newu0, newp
end

"""
    $(TYPEDSIGNATURES)

Check if the given system is an initialization system.
"""
function is_initializesystem(sys::AbstractSystem)
    sys isa NonlinearSystem && get_metadata(sys) isa InitializationSystemMetadata
end

"""
Counteracts the CSE/array variable hacks in `symbolics_tearing.jl` so it works with
initialization.
"""
function unhack_observed(obseqs::Vector{Equation}, eqs::Vector{Equation})
    subs = Dict()
    tempvars = Set()
    rm_idxs = Int[]
    for (i, eq) in enumerate(obseqs)
        iscall(eq.rhs) || continue
        if operation(eq.rhs) == StructuralTransformations.change_origin
            push!(rm_idxs, i)
            continue
        end
        if operation(eq.rhs) == StructuralTransformations.getindex_wrapper
            var, idxs = arguments(eq.rhs)
            subs[eq.rhs] = var[idxs...]
            push!(tempvars, var)
        end
    end

    for (i, eq) in enumerate(eqs)
        iscall(eq.rhs) || continue
        if operation(eq.rhs) == StructuralTransformations.getindex_wrapper
            var, idxs = arguments(eq.rhs)
            subs[eq.rhs] = var[idxs...]
            push!(tempvars, var)
        end
    end

    for (i, eq) in enumerate(obseqs)
        if eq.lhs in tempvars
            subs[eq.lhs] = eq.rhs
            push!(rm_idxs, i)
        end
    end

    obseqs = obseqs[setdiff(eachindex(obseqs), rm_idxs)]
    obseqs = map(obseqs) do eq
        fixpoint_sub(eq.lhs, subs) ~ fixpoint_sub(eq.rhs, subs)
    end
    eqs = map(eqs) do eq
        fixpoint_sub(eq.lhs, subs) ~ fixpoint_sub(eq.rhs, subs)
    end
    return obseqs, eqs
end

function UnknownsInTimeIndependentInitializationError(eq, non_params)
    ArgumentError("""
    Initialization equations for time-independent systems can only contain parameters. \
    Found $non_params in $eq. If the equations refer to the initial guess for unknowns, \
    use the `Initial` operator.
    """)
end
