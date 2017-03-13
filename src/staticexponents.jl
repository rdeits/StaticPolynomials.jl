module sp

import Base: *, +, ^, convert, promote_rule, convert, show, isless, literal_pow

abstract type PolynomialLike end
abstract type TermLike <: PolynomialLike end
abstract type MonomialLike <: TermLike end
abstract type PowerLike <: MonomialLike end
abstract type VariableLike <: PowerLike end

immutable Variable{Name} <: VariableLike
end

isless(v1::Variable{N1}, v2::Variable{N2}) where {N1, N2} = isless(N1, N2)
show(io::IO, v::Variable{Name}) where Name = print(io, Name)

immutable Power{Var} <: PowerLike
    exponent::Rational{Int}
end

variable(::Power{V}) where {V} = V
exponent(p::Power) = p.exponent
isless(p1::Power{V1}, p2::Power{V2}) where {V1, V2} = (V1, p1.exponent) < (V2, p2.exponent)

function show(io::IO, p::Power)
    print(io, variable(p))
    d = denominator(exponent(p))
    n = numerator(exponent(p))
    if d == 1
        if n != 1
            print(io, "^", n)
        end
    else
        print(io, "^(", exponent(p), ")")
    end
end

convert(::Type{<:Power}, v::Variable) = Power{v}(1)

immutable Monomial{Powers} <: MonomialLike
end

convert(::Type{<:Monomial}, p::Power) = Monomial{(p,)}()
convert(T::Type{<:Monomial}, p::VariableLike) = convert(T, Power(p))

function show(io::IO, m::Monomial{P}) where {P}
    for power in P
        show(io, power)
    end
end

immutable Term{Mono, T} <: TermLike
    coefficient::T
    Term{Mono}(c::T) where{Mono, T} = new{Mono, T}(c)
    Term{Mono, T}(c::T) where{Mono, T} = new{Mono, T}(c)
end

convert(::Type{<:Term}, mono::M) where {M <: Monomial} = Term{mono}(1)
convert(T::Type{<:Term}, v::PowerLike) = convert(T, Monomial(v))

function show(io::IO, t::Term{Mono, T}) where {Mono, T}
    print(io, t.coefficient, Mono)
end

immutable Polynomial{Terms <: Tuple} <: PolynomialLike
    terms::Terms
end

convert(::Type{<:Polynomial}, t::Term) = Polynomial((t,))
convert(T::Type{<:Polynomial}, m::MonomialLike) = convert(T, convert(Term, m))

function show(io::IO, p::Polynomial)
    if length(p.terms) == 0
        print(io, "0")
    else
        print(io, p.terms[1])
        for t in p.terms[2:end]
            print(io, " + ", t)
        end
    end
end

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
powers(::Monomial{P}) where {P} = P
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
    for power in powers(M2)
        i = indexin([power], p)[1]
        if i != 0
            p[i] = Power{variable(p[i])}(exponent(p[i]) + exponent(power))
        else
            push!(p, power)
        end
    end
    quote
        Term{Monomial{$(Tuple(sort(p)))}()}(t1.coefficient * t2.coefficient)
    end
end

(+)(t1::PolynomialLike, t2::PolynomialLike) = convert(Polynomial, t1) + convert(Polynomial, t2)
(+)(t1::Term{P, T1}, t2::Term{P, T2}) where {P, T1, T2} = Term{P}(t1.coefficient + t2.coefficient)
(+)(v1::MonomialLike, v2::MonomialLike) = Term(v1) + Term(v2)
(*)(x::Number, t::T) where {T <: Term} = T(x * t.coefficient)
(*)(t::T, x::Number) where {T <: Term} = T(t.coefficient * x)
(*)(x::Number, m::MonomialLike) = x * Term(m)
(*)(m::MonomialLike, x::Number) = Term(m) * x
(*)(t1::TermLike, t2::TermLike) = Term(t1) * Term(t2)
(*)(x::Number, m::Monomial) = x * Term(m)


end
