"""
$(TYPEDSIGNATURES)

Generate `NonlinearSystem` which initializes an ODE problem from specified initial conditions of an `ODESystem`.
"""
function generate_initializesystem(sys::ODESystem;
        u0map = Dict(),
        name = nameof(sys),
        guesses = Dict(), check_defguess = false,
        default_dd_value = 0.0,
        kwargs...)
    sts, eqs = unknowns(sys), equations(sys)
    idxs_diff = isdiffeq.(eqs)
    idxs_alge = .!idxs_diff
    num_alge = sum(idxs_alge)

    # Start the equations list with algebraic equations
    eqs_ics = eqs[idxs_alge]
    u0 = Vector{Pair}(undef, 0)

    eqs_diff = eqs[idxs_diff]
    diffmap = Dict(getfield.(eqs_diff, :lhs) .=> getfield.(eqs_diff, :rhs))

    full_states = unique([sts; getfield.((observed(sys)), :lhs)])
    set_full_states = Set(full_states)
    guesses = todict(guesses)
    schedule = getfield(sys, :schedule)

    if schedule !== nothing
        guessmap = [x[2] => get(guesses, x[1], default_dd_value)
                    for x in schedule.dummy_sub]
        dd_guess = Dict(filter(x -> !isnothing(x[1]), guessmap))
        if u0map === nothing || isempty(u0map)
            filtered_u0 = u0map
        else
            filtered_u0 = Pair[]
            for x in u0map
                y = get(schedule.dummy_sub, x[1], x[1])
                y = get(diffmap, y, y)
                if y isa Symbolics.Arr
                    _y = collect(y)

                    # TODO: Don't scalarize arrays
                    for i in 1:length(_y)
                        push!(filtered_u0, _y[i] => x[2][i])
                    end
                elseif y isa ModelingToolkit.BasicSymbolic
                    # y is a derivative expression expanded
                    # add to the initialization equations
                    push!(eqs_ics, y ~ x[2])
                elseif y ∈ set_full_states
                    push!(filtered_u0, y => x[2])
                else
                    error("Initialization expression $y is currently not supported. If its a higher order derivative expression, then only the dummy derivative expressions are supported.")
                end
            end
            filtered_u0 = filtered_u0 isa Pair ? todict([filtered_u0]) : todict(filtered_u0)
        end
    else
        dd_guess = Dict()
        filtered_u0 = u0map
    end

    defs = merge(defaults(sys), filtered_u0)
    guesses = merge(get_guesses(sys), todict(guesses), dd_guess)

    for st in full_states
        if st ∈ keys(defs)
            def = defs[st]

            if def isa Equation
                st ∉ keys(guesses) && check_defguess &&
                    error("Invalid setup: unknown $(st) has an initial condition equation with no guess.")
                push!(eqs_ics, def)
                push!(u0, st => guesses[st])
            else
                push!(eqs_ics, st ~ def)
                push!(u0, st => def)
            end
        elseif st ∈ keys(guesses)
            push!(u0, st => guesses[st])
        elseif check_defguess
            error("Invalid setup: unknown $(st) has no default value or initial guess")
        end
    end

    pars = [parameters(sys); get_iv(sys)]
    nleqs = [eqs_ics; get_initialization_eqs(sys); observed(sys)]

    sys_nl = NonlinearSystem(nleqs,
        full_states,
        pars;
        defaults = merge(ModelingToolkit.defaults(sys), todict(u0), dd_guess),
        name,
        kwargs...)

    return sys_nl
end
