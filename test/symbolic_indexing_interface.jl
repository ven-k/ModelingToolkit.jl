using ModelingToolkit, SymbolicIndexingInterface, SciMLBase
using ModelingToolkit: t_nounits as t, D_nounits as D

@parameters a b
@variables x(t)=1.0 y(t)=2.0 xy(t)
eqs = [D(x) ~ a * y + t, D(y) ~ b * t]
@named odesys = ODESystem(eqs, t, [x, y], [a, b]; observed = [xy ~ x + y])

@test all(is_variable.((odesys,), [x, y, 1, 2, :x, :y]))
@test all(.!is_variable.((odesys,), [a, b, t, 3, 0, :a, :b]))
@test variable_index.((odesys,), [x, y, a, b, t, 1, 2, :x, :y, :a, :b]) ==
      [1, 2, nothing, nothing, nothing, 1, 2, 1, 2, nothing, nothing]
@test isequal(variable_symbols(odesys), [x, y])
@test all(is_parameter.((odesys,), [a, b, 1, 2, :a, :b]))
@test all(.!is_parameter.((odesys,), [x, y, t, 3, 0, :x, :y]))
@test parameter_index.((odesys,), [x, y, a, b, t, 1, 2, :x, :y, :a, :b]) ==
      [nothing, nothing, 1, 2, nothing, 1, 2, nothing, nothing, 1, 2]
@test isequal(parameter_symbols(odesys), [a, b])
@test all(is_independent_variable.((odesys,), [t, :t]))
@test all(.!is_independent_variable.((odesys,), [x, y, a, :x, :y, :a]))
@test isequal(independent_variable_symbols(odesys), [t])
@test is_time_dependent(odesys)
@test constant_structure(odesys)
@test !isempty(default_values(odesys))
@test default_values(odesys)[x] == 1.0
@test default_values(odesys)[y] == 2.0
@test isequal(default_values(odesys)[xy], x + y)

@named odesys = ODESystem(
    eqs, t, [x, y], [a, b]; defaults = [xy => 3.0], observed = [xy ~ x + y])
@test default_values(odesys)[xy] == 3.0

@variables x y z
@parameters σ ρ β

eqs = [0 ~ σ * (y - x),
    0 ~ x * (ρ - z) - y,
    0 ~ x * y - β * z]
@named ns = NonlinearSystem(eqs, [x, y, z], [σ, ρ, β])

@test !is_time_dependent(ns)

@parameters x
@variables u(..)
Dxx = Differential(x)^2
Dtt = Differential(t)^2
Dt = D

#2D PDE
C = 1
eq = Dtt(u(t, x)) ~ C^2 * Dxx(u(t, x))

# Initial and boundary conditions
bcs = [u(t, 0) ~ 0.0,# for all t > 0
    u(t, 1) ~ 0.0,# for all t > 0
    u(0, x) ~ x * (1.0 - x), #for all 0 < x < 1
    Dt(u(0, x)) ~ 0.0] #for all  0 < x < 1]

# Space and time domains
domains = [t ∈ (0.0, 1.0),
    x ∈ (0.0, 1.0)]

@named pde_system = PDESystem(eq, bcs, domains, [t, x], [u])

@test pde_system.ps == SciMLBase.NullParameters()
@test parameter_symbols(pde_system) == []

@parameters x
@constants h = 1
@variables u(..)
Dt = D
Dxx = Differential(x)^2
eq = Dt(u(t, x)) ~ h * Dxx(u(t, x))
bcs = [u(0, x) ~ -h * x * (x - 1) * sin(x),
    u(t, 0) ~ 0, u(t, 1) ~ 0]

domains = [t ∈ (0.0, 1.0),
    x ∈ (0.0, 1.0)]

analytic = [u(t, x) ~ -h * x * (x - 1) * sin(x) * exp(-2 * h * t)]
analytic_function = (ps, t, x) -> -ps[1] * x * (x - 1) * sin(x) * exp(-2 * ps[1] * t)

@named pdesys = PDESystem(eq, bcs, domains, [t, x], [u], [h], analytic = analytic)

@test isequal(pdesys.ps, [h])
@test isequal(parameter_symbols(pdesys), [h])
@test isequal(parameters(pdesys), [h])

# Issue#2767
using ModelingToolkit
using ModelingToolkit: t_nounits as t, D_nounits as D
using SymbolicIndexingInterface

@parameters p1[1:2]=[1.0, 2.0] p2[1:2]=[0.0, 0.0]
@variables x(t) = 0

@named sys = ODESystem(
    [D(x) ~ sum(p1) * t + sum(p2)],
    t;
)
prob = ODEProblem(complete(sys))
get_dep = @test_nowarn getu(prob, 2p1)
@test get_dep(prob) == [2.0, 4.0]

@testset "Observed functions with variables as `Symbol`s" begin
    @variables x(t) y(t) z(t)[1:2]
    @parameters p1 p2[1:2, 1:2]
    @mtkbuild sys = ODESystem([D(x) ~ x * t + p1, y ~ 2x, D(z) ~ p2 * z], t)
    prob = ODEProblem(
        sys, [x => 1.0, z => ones(2)], (0.0, 1.0), [p1 => 2.0, p2 => ones(2, 2)])
    @test getu(prob, x)(prob) == getu(prob, :x)(prob)
    @test getu(prob, [x, y])(prob) == getu(prob, [:x, :y])(prob)
    @test getu(prob, z)(prob) == getu(prob, :z)(prob)
    @test getu(prob, p1)(prob) == getu(prob, :p1)(prob)
    @test getu(prob, p2)(prob) == getu(prob, :p2)(prob)
end
