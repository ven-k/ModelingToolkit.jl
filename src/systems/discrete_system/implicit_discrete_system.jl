"""
$(TYPEDEF)
An implicit system of difference equations.
# Fields
$(FIELDS)
# Example
```
using ModelingToolkit
using ModelingToolkit: t_nounits as t
@parameters σ=28.0 ρ=10.0 β=8/3 δt=0.1
@variables x(t)=1.0 y(t)=0.0 z(t)=0.0
k = ShiftIndex(t)
eqs = [x ~ σ*(y-x(k-1)),
       y ~ x(k-1)*(ρ-z(k-1))-y,
       z ~ x(k-1)*y(k-1) - β*z]
@named ide = ImplicitDiscreteSystem(eqs,t,[x,y,z],[σ,ρ,β]; tspan = (0, 1000.0))
```
"""
struct ImplicitDiscreteSystem <: AbstractDiscreteSystem
    """
    A tag for the system. If two systems have the same tag, then they are
    structurally identical.
    """
    tag::UInt
    """The difference equations defining the discrete system."""
    eqs::Vector{Equation}
    """Independent variable."""
    iv::BasicSymbolic{Real}
    """Dependent (state) variables. Must not contain the independent variable."""
    unknowns::Vector
    """Parameter variables. Must not contain the independent variable."""
    ps::Vector
    """Time span."""
    tspan::Union{NTuple{2, Any}, Nothing}
    """Array variables."""
    var_to_name::Any
    """Observed states."""
    observed::Vector{Equation}
    """
    The name of the system
    """
    name::Symbol
    """
    A description of the system.
    """
    description::String
    """
    The internal systems. These are required to have unique names.
    """
    systems::Vector{ImplicitDiscreteSystem}
    """
    The default values to use when initial conditions and/or
    parameters are not supplied in `ImplicitDiscreteProblem`.
    """
    defaults::Dict
    """
    The guesses to use as the initial conditions for the
    initialization system.
    """
    guesses::Dict
    """
    The system for performing the initialization.
    """
    initializesystem::Union{Nothing, NonlinearSystem}
    """
    Extra equations to be enforced during the initialization sequence.
    """
    initialization_eqs::Vector{Equation}
    """
    Inject assignment statements before the evaluation of the RHS function.
    """
    preface::Any
    """
    Type of the system.
    """
    connector_type::Any
    """
    Topologically sorted parameter dependency equations, where all symbols are parameters and
    the LHS is a single parameter.
    """
    parameter_dependencies::Vector{Equation}
    """
    Metadata for the system, to be used by downstream packages.
    """
    metadata::Any
    """
    Metadata for MTK GUI.
    """
    gui_metadata::Union{Nothing, GUIMetadata}
    """
    Cache for intermediate tearing state.
    """
    tearing_state::Any
    """
    Substitutions generated by tearing.
    """
    substitutions::Any
    """
    If false, then `sys.x` no longer performs namespacing.
    """
    namespacing::Bool
    """
    If true, denotes the model will not be modified any further.
    """
    complete::Bool
    """
    Cached data for fast symbolic indexing.
    """
    index_cache::Union{Nothing, IndexCache}
    """
    The hierarchical parent system before simplification.
    """
    parent::Any
    isscheduled::Bool

    function ImplicitDiscreteSystem(tag, discreteEqs, iv, dvs, ps, tspan, var_to_name,
            observed, name, description, systems, defaults, guesses, initializesystem,
            initialization_eqs, preface, connector_type, parameter_dependencies = Equation[],
            metadata = nothing, gui_metadata = nothing,
            tearing_state = nothing, substitutions = nothing, namespacing = true,
            complete = false, index_cache = nothing, parent = nothing,
            isscheduled = false;
            checks::Union{Bool, Int} = true)
        if checks == true || (checks & CheckComponents) > 0
            check_independent_variables([iv])
            check_variables(dvs, iv)
            check_parameters(ps, iv)
            check_subsystems(systems)
        end
        if checks == true || (checks & CheckUnits) > 0
            u = __get_unit_type(dvs, ps, iv)
            check_units(u, discreteEqs)
        end
        new(tag, discreteEqs, iv, dvs, ps, tspan, var_to_name, observed, name, description,
            systems, defaults, guesses, initializesystem, initialization_eqs,
            preface, connector_type, parameter_dependencies, metadata, gui_metadata,
            tearing_state, substitutions, namespacing, complete, index_cache, parent,
            isscheduled)
    end
end

"""
    $(TYPEDSIGNATURES)

Constructs a ImplicitDiscreteSystem.
"""
function ImplicitDiscreteSystem(eqs::AbstractVector{<:Equation}, iv, dvs, ps;
        observed = Num[],
        systems = ImplicitDiscreteSystem[],
        tspan = nothing,
        name = nothing,
        description = "",
        default_u0 = Dict(),
        default_p = Dict(),
        guesses = Dict(),
        initializesystem = nothing,
        initialization_eqs = Equation[],
        defaults = _merge(Dict(default_u0), Dict(default_p)),
        preface = nothing,
        connector_type = nothing,
        parameter_dependencies = Equation[],
        metadata = nothing,
        gui_metadata = nothing,
        kwargs...)
    name === nothing &&
        throw(ArgumentError("The `name` keyword must be provided. Please consider using the `@named` macro"))
    iv′ = value(iv)
    dvs′ = value.(dvs)
    ps′ = value.(ps)
    if any(hasderiv, eqs) || any(hashold, eqs) || any(hassample, eqs) || any(hasdiff, eqs)
        error("Equations in a `ImplicitDiscreteSystem` can only have `Shift` operators.")
    end
    if !(isempty(default_u0) && isempty(default_p))
        Base.depwarn(
            "`default_u0` and `default_p` are deprecated. Use `defaults` instead.",
            :ImplicitDiscreteSystem, force = true)
    end

    # Copy equations to canonical form, but do not touch array expressions
    eqs = [wrap(eq.lhs) isa Symbolics.Arr ? eq : 0 ~ eq.rhs - eq.lhs for eq in eqs]
    defaults = Dict{Any, Any}(todict(defaults))
    guesses = Dict{Any, Any}(todict(guesses))
    var_to_name = Dict()
    process_variables!(var_to_name, defaults, guesses, dvs′)
    process_variables!(var_to_name, defaults, guesses, ps′)
    process_variables!(
        var_to_name, defaults, guesses, [eq.lhs for eq in parameter_dependencies])
    process_variables!(
        var_to_name, defaults, guesses, [eq.rhs for eq in parameter_dependencies])
    defaults = Dict{Any, Any}(value(k) => value(v)
    for (k, v) in pairs(defaults) if v !== nothing)
    guesses = Dict{Any, Any}(value(k) => value(v)
    for (k, v) in pairs(guesses) if v !== nothing)

    isempty(observed) || collect_var_to_name!(var_to_name, (eq.lhs for eq in observed))

    sysnames = nameof.(systems)
    if length(unique(sysnames)) != length(sysnames)
        throw(ArgumentError("System names must be unique."))
    end
    ImplicitDiscreteSystem(Threads.atomic_add!(SYSTEM_COUNT, UInt(1)),
        eqs, iv′, dvs′, ps′, tspan, var_to_name, observed, name, description, systems,
        defaults, guesses, initializesystem, initialization_eqs, preface, connector_type,
        parameter_dependencies, metadata, gui_metadata, kwargs...)
end

function ImplicitDiscreteSystem(eqs, iv; kwargs...)
    eqs = collect(eqs)
    diffvars = OrderedSet()
    allunknowns = OrderedSet()
    ps = OrderedSet()
    iv = value(iv)
    for eq in eqs
        collect_vars!(allunknowns, ps, eq, iv; op = Shift)
        if iscall(eq.lhs) && operation(eq.lhs) isa Shift
            isequal(iv, operation(eq.lhs).t) ||
                throw(ArgumentError("An ImplicitDiscreteSystem can only have one independent variable."))
            eq.lhs in diffvars &&
                throw(ArgumentError("The shift variable $(eq.lhs) is not unique in the system of equations."))
            push!(diffvars, eq.lhs)
        end
    end
    for eq in get(kwargs, :parameter_dependencies, Equation[])
        if eq isa Pair
            collect_vars!(allunknowns, ps, eq, iv)
        else
            collect_vars!(allunknowns, ps, eq, iv)
        end
    end
    new_ps = OrderedSet()
    for p in ps
        if iscall(p) && operation(p) === getindex
            par = arguments(p)[begin]
            if Symbolics.shape(Symbolics.unwrap(par)) !== Symbolics.Unknown() &&
               all(par[i] in ps for i in eachindex(par))
                push!(new_ps, par)
            else
                push!(new_ps, p)
            end
        else
            push!(new_ps, p)
        end
    end
    return ImplicitDiscreteSystem(eqs, iv,
        collect(allunknowns), collect(new_ps); kwargs...)
end

function ImplicitDiscreteSystem(eq::Equation, args...; kwargs...)
    ImplicitDiscreteSystem([eq], args...; kwargs...)
end

function flatten(sys::ImplicitDiscreteSystem, noeqs = false)
    systems = get_systems(sys)
    if isempty(systems)
        return sys
    else
        return ImplicitDiscreteSystem(noeqs ? Equation[] : equations(sys),
            get_iv(sys),
            unknowns(sys),
            parameters(sys),
            observed = observed(sys),
            defaults = defaults(sys),
            guesses = guesses(sys),
            initialization_eqs = initialization_equations(sys),
            name = nameof(sys),
            description = description(sys),
            metadata = get_metadata(sys),
            checks = false)
    end
end

function generate_function(
        sys::ImplicitDiscreteSystem, dvs = unknowns(sys), ps = parameters(sys); wrap_code = identity, kwargs...)
    iv = get_iv(sys)
    # Algebraic equations get shifted forward 1, to match with differential equations
    exprs = map(equations(sys)) do eq
        _iszero(eq.lhs) ? distribute_shift(Shift(iv, 1)(eq.rhs)) : (eq.rhs - eq.lhs)
    end

    # Handle observables in algebraic equations, since they are shifted
    obs = observed(sys)
    shifted_obs = Symbolics.Equation[distribute_shift(Shift(iv, 1)(eq)) for eq in obs]
    obsidxs = observed_equations_used_by(sys, exprs; obs = shifted_obs)
    extra_assignments = [Assignment(shifted_obs[i].lhs, shifted_obs[i].rhs)
                         for i in obsidxs]

    u_next = map(Shift(iv, 1), dvs)
    u = dvs
    build_function_wrapper(
        sys, exprs, u_next, u, ps..., iv; p_start = 3, extra_assignments, kwargs...)
end

function shift_u0map_forward(sys::ImplicitDiscreteSystem, u0map, defs)
    iv = get_iv(sys)
    updated = AnyDict()
    for k in collect(keys(u0map))
        v = u0map[k]
        if !((op = operation(k)) isa Shift)
            isnothing(getunshifted(k)) &&
                error("Initial conditions must be for the past state of the unknowns. Instead of providing the condition for $k, provide the condition for $(Shift(iv, -1)(k)).")

            updated[k] = v
        elseif op.steps > 0
            error("Initial conditions must be for the past state of the unknowns. Instead of providing the condition for $k, provide the condition for $(Shift(iv, -1)(only(arguments(k)))).")
        else
            updated[k] = v
        end
    end
    for var in unknowns(sys)
        op = operation(var)
        root = getunshifted(var)
        shift = getshift(var)
        isnothing(root) && continue
        (haskey(updated, Shift(iv, shift)(root)) || haskey(updated, var)) && continue
        haskey(defs, root) || error("Initial condition for $var not provided.")
        updated[var] = defs[root]
    end
    return updated
end

"""
    $(TYPEDSIGNATURES)
Generates an ImplicitDiscreteProblem from an ImplicitDiscreteSystem.
"""
function SciMLBase.ImplicitDiscreteProblem(
        sys::ImplicitDiscreteSystem, u0map = [], tspan = get_tspan(sys),
        parammap = SciMLBase.NullParameters();
        eval_module = @__MODULE__,
        eval_expression = false,
        kwargs...
)
    if !iscomplete(sys)
        error("A completed `ImplicitDiscreteSystem` is required. Call `complete` or `structural_simplify` on the system before creating a `ImplicitDiscreteProblem`.")
    end
    dvs = unknowns(sys)
    ps = parameters(sys)
    eqs = equations(sys)
    iv = get_iv(sys)

    u0map = to_varmap(u0map, dvs)
    u0map = shift_u0map_forward(sys, u0map, defaults(sys))
    f, u0, p = process_SciMLProblem(
        ImplicitDiscreteFunction, sys, u0map, parammap; eval_expression, eval_module, kwargs...)

    kwargs = filter_kwargs(kwargs)
    ImplicitDiscreteProblem(f, u0, tspan, p; kwargs...)
end

function SciMLBase.ImplicitDiscreteFunction(sys::ImplicitDiscreteSystem, args...; kwargs...)
    ImplicitDiscreteFunction{true}(sys, args...; kwargs...)
end

function SciMLBase.ImplicitDiscreteFunction{true}(
        sys::ImplicitDiscreteSystem, args...; kwargs...)
    ImplicitDiscreteFunction{true, SciMLBase.AutoSpecialize}(sys, args...; kwargs...)
end

function SciMLBase.ImplicitDiscreteFunction{false}(
        sys::ImplicitDiscreteSystem, args...; kwargs...)
    ImplicitDiscreteFunction{false, SciMLBase.FullSpecialize}(sys, args...; kwargs...)
end
function SciMLBase.ImplicitDiscreteFunction{iip, specialize}(
        sys::ImplicitDiscreteSystem,
        dvs = unknowns(sys),
        ps = parameters(sys),
        u0 = nothing;
        version = nothing,
        p = nothing,
        t = nothing,
        eval_expression = false,
        eval_module = @__MODULE__,
        analytic = nothing, cse = true,
        kwargs...) where {iip, specialize}
    if !iscomplete(sys)
        error("A completed `ImplicitDiscreteSystem` is required. Call `complete` or `structural_simplify` on the system before creating a `ImplicitDiscreteProblem`")
    end
    f_gen = generate_function(sys, dvs, ps; expression = Val{true},
        expression_module = eval_module, cse, kwargs...)
    f_oop, f_iip = eval_or_rgf.(f_gen; eval_expression, eval_module)
    f(u_next, u, p, t) = f_oop(u_next, u, p, t)
    f(resid, u_next, u, p, t) = f_iip(resid, u_next, u, p, t)

    if specialize === SciMLBase.FunctionWrapperSpecialize && iip
        if u0 === nothing || p === nothing || t === nothing
            error("u0, p, and t must be specified for FunctionWrapperSpecialize on ImplicitDiscreteFunction.")
        end
        f = SciMLBase.wrapfun_iip(f, (u0, u0, p, t))
    end

    observedfun = ObservedFunctionCache(
        sys; eval_expression, eval_module, checkbounds = get(kwargs, :checkbounds, false), cse)

    ImplicitDiscreteFunction{iip, specialize}(f;
        sys = sys,
        observed = observedfun,
        analytic = analytic,
        kwargs...)
end

"""
```julia
ImplicitDiscreteFunctionExpr{iip}(sys::ImplicitDiscreteSystem, dvs = states(sys),
                                  ps = parameters(sys);
                                  version = nothing,
                                  kwargs...) where {iip}
```

Create a Julia expression for an `ImplicitDiscreteFunction` from the [`ImplicitDiscreteSystem`](@ref).
The arguments `dvs` and `ps` are used to set the order of the dependent
variable and parameter vectors, respectively.
"""
struct ImplicitDiscreteFunctionExpr{iip} end
struct ImplicitDiscreteFunctionClosure{O, I} <: Function
    f_oop::O
    f_iip::I
end
(f::ImplicitDiscreteFunctionClosure)(u_next, u, p, t) = f.f_oop(u_next, u, p, t)
function (f::ImplicitDiscreteFunctionClosure)(resid, u_next, u, p, t)
    f.f_iip(resid, u_next, u, p, t)
end

function ImplicitDiscreteFunctionExpr{iip}(
        sys::ImplicitDiscreteSystem, dvs = unknowns(sys),
        ps = parameters(sys), u0 = nothing;
        version = nothing, p = nothing,
        linenumbers = false,
        simplify = false,
        kwargs...) where {iip}
    f_oop, f_iip = generate_function(sys, dvs, ps; expression = Val{true}, kwargs...)

    fsym = gensym(:f)
    _f = :($fsym = $ImplicitDiscreteFunctionClosure($f_oop, $f_iip))

    ex = quote
        $_f
        ImplicitDiscreteFunction{$iip}($fsym)
    end
    !linenumbers ? Base.remove_linenums!(ex) : ex
end

function ImplicitDiscreteFunctionExpr(sys::ImplicitDiscreteSystem, args...; kwargs...)
    ImplicitDiscreteFunctionExpr{true}(sys, args...; kwargs...)
end
