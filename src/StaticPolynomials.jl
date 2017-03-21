module StaticPolynomials

import Base: *, +, ^,
    convert, promote_rule, convert, show, isless, literal_pow,
    one, copy

export @polyvar,
       Variable,
       Monomial,
       Term,
       Polynomial

abstract type PolynomialLike end
abstract type TermLike <: PolynomialLike end
abstract type MonomialLike <: TermLike end
abstract type VariableLike <: MonomialLike end

immutable Variable{Name} <: VariableLike
end

macro polyvar(names...)
    exprs = [
        quote
            $(esc(name)) = Variable{$(esc(Expr(:quote, name)))}()
        end
        for name in names
    ]
    Expr(:block, exprs...)
end

one(v::Variable) = Monomial{tuple()}()
copy(v::Variable) = v

immutable Power{Var}
    exponent::Rational{Int}
end
Power(v::Variable) = Power{v}(1)

variable(::Power{V}) where {V} = V
exponent(p::Power) = p.exponent

immutable Monomial{Powers} <: MonomialLike
end
@generated function Monomial(v::Variable)
    :(Monomial{$((Power{(v())}(1),))}())
end

powers(::Type{Monomial{Powers}}) where {Powers} = Powers
powers(m::Monomial) = powers(typeof(m))

@generated function variables(::Type{M}) where {M <: Monomial}
    :($(variable.(powers(M))))
end

variables(m::Monomial) = variables(typeof(m))


immutable Term{Mono, T} <: TermLike
    coefficient::T
end
Term(m::M, x::T) where {M <: Monomial, T} = Term{M(), T}(x)
Term(v::Variable) = Term(Monomial(v), 1)
Term(m::Monomial) = Term(m, 1)
Term(x) = Term(Monomial{tuple()}(), x)

immutable Polynomial{Terms <: Tuple{Vararg{<:Term}}} <: PolynomialLike
    terms::Terms
end
Polynomial(t::Term) = Polynomial((t,))
Polynomial(x) = Polynomial(Term(x))

isless(::Type{Variable{N1}}, ::Type{Variable{N2}}) where {N1, N2} = N1 < N2
isless(v1::Variable, v2::Variable) = typeof(v1) < typeof(v2)

@generated function promote_rule(::Type{V1}, ::Type{V2}) where {V1 <: Variable, V2 <: Variable}
    M1 = Monomial{(Power{V1()}(1),)}()
    M2 = Monomial{(Power{V2()}(1),)}()
    if M1 < M2
        :(Polynomial{Tuple{Term{$M1, Int}, Term{$M2, Int}}})
    else
        :(Polynomial{Tuple{Term{$M2, Int}, Term{$M1, Int}}})
    end
end

@generated function promote_rule(::Type{V}, ::Type{M}) where {V <: Variable, M <: Monomial}
    

@generated function literal_pow(^, v::V, ::Type{Val{x}}) where {V <: Variable, x}
    quote
        Monomial{$((Power{V()}(x),))}()
    end
end

@generated function (*)(v1::V, v2::V) where {V <: Variable}
    quote
        Monomial{$((Power{V()}(2),))}()
    end
end

@generated function (*)(v1::V1, v2::V2) where {V1 <: Variable, V2 <: Variable}
    @assert V1 != V2
    p = Tuple(sort([Power{V1()}(1), Power{V2()}(1)]))
    quote
        Monomial{$(p)}()
    end
end

# @generated function promote_rule(::Type{Term{Monomial{P1}, T}}, ::Type{Term{Monomial{P2}, T}}) where {T, P1, P2}
#     vars = Set{Any}()
#     for v in P1
#         push!(vars, v)
#     end
#     for v in P2
#         push!(vars, v)
#     end
#     vars = Tuple(sort(collect(vars)))
#     quote
#         Term{Monomial{$(vars)}(), T}
#     end
# end
#
powers(::Type{Term{M, T}}) where {M, T} = powers(M)

function add_impl(::Type{Polynomial{Terms1}}, ::Type{Polynomial{Terms2}}) where {Terms1, Terms2}
    # TODO: accidentally quadratic
    p1 = powers.(collect(Terms1.parameters))
    p2 = powers.(collect(Terms2.parameters))
    allpowers = sort(collect(Set([p1..., p2...])))
    args = []
    for p in allpowers
        i1 = indexin([p], p1)[1]
        i2 = indexin([p], p2)[1]
        if i1 != 0 && i2 != 0
            push!(args, :(p1.terms[$i1] + p2.terms[$i2]))
        elseif i2 != 0
            push!(args, :(p2.terms[$i2]))
        else
            @assert i1 != 0
            push!(args, :(p1.terms[$i1]))
        end
    end
    args
end

@generated function +(p1::Polynomial{Terms1}, p2::Polynomial{Terms2}) where {Terms1, Terms2}
    Expr(:call, :Polynomial, Expr(:tuple, add_impl(p1, p2)...))
end

@generated function *(t1::Term{M1, T1}, t2::Term{M2, T2}) where {M1, M2, T1, T2}
    p = Any[powers(M1)...]
    for p2 in powers(M2)
        matched = false
        for (i, p1) in enumerate(powers(M1))
            if variable(p2) == variable(p1)
                p[i] = Power{variable(p[i])}(exponent(p[i]) + exponent(p2))
                matched = true
                break
            end
        end
        if !matched
            push!(p, p2)
        end
    end
    quote
        Term{Monomial{$(Tuple(sort(p)))}()}(t1.coefficient * t2.coefficient)
    end
end

(+)(t1::PolynomialLike, t2::PolynomialLike) = convert(Polynomial, t1) + convert(Polynomial, t2)
(+)(t1::Term{P, T1}, t2::Term{P, T2}) where {P, T1, T2} = Term{P}(t1.coefficient + t2.coefficient)
(+)(v1::MonomialLike, v2::MonomialLike) = Term(v1) + Term(v2)
(+)(m::TermLike, x::Number) = m + Term(x)
(+)(x::Number, m::TermLike) = Term(x) + m
(*)(x::Number, t::T) where {T <: Term} = T(x * t.coefficient)
(*)(t::T, x::Number) where {T <: Term} = T(t.coefficient * x)
(*)(x::Number, m::MonomialLike) = x * Term(m)
(*)(m::MonomialLike, x::Number) = Term(m) * x
(*)(t1::TermLike, t2::TermLike) = Term(t1) * Term(t2)
(*)(x::Number, m::Monomial) = x * Term(m)

@generated function subs(m::Term{Mono, T}, s::Pair{Variable{N}, T2}) where {Mono, T, N, T2}
    coeff = :(m.coefficient)
    remaining = []
    for p in powers(Mono)
        if variable(p) == Variable{N}()
            coeff = Expr(:call, :*, coeff, :(s.second ^ $(exponent(p))))
        else
            push!(remaining, p)
        end
    end
    if isempty(remaining)
        coeff
    else
        quote
            Term{$(Monomial{Tuple(remaining)}())}($coeff)
        end
    end
end

@generated function subs(m::Term, s::Vararg{<: Pair, N}) where {N}
    expr = :(m)
    for j in 1:N
        expr = Expr(:call, :subs, expr, :(s[$j]))
    end
    expr
end

@generated function subs(p::Polynomial{Terms}, s::Vararg{<:Pair, N}) where {N, Terms}
    Expr(:call, :+, [:(subs(p.terms[$i], s...)) for i in 1:length(Terms.parameters)]...)
end

subs(x::Number, s...) = x

(m::Polynomial)(args...) = subs(m, args...)
(m::Term)(args...) = subs(m, args...)

include("show.jl")

end
