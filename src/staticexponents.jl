module sp

import Base: *, +, ^, convert, promote_rule, convert, show, isless

abstract type PolynomialLike end
abstract type TermLike <: PolynomialLike end
abstract type MonomialLike <: TermLike end
abstract type VariableLike <: MonomialLike end

immutable Variable{Name} <: VariableLike
end

isless(v1::Variable{N1}, v2::Variable{N2}) where {N1, N2} = isless(N1, N2)

show(io::IO, v::Variable{Name}) where Name = print(io, Name)

immutable Monomial{Powers} <: MonomialLike
end

convert(::Type{<:Monomial}, v::Variable) = Monomial{((v, 1),)}()

function show(io::IO, m::Monomial{P}) where {P}
    for power in P
        print(io, power[1], "^", power[2])
    end
end

immutable Term{Mono, T} <: TermLike
    coefficient::T
    Term{Mono}(c::T) where{Mono, T} = new{Mono, T}(c)
    Term{Mono, T}(c::T) where{Mono, T} = new{Mono, T}(c)
end

convert(::Type{<:Term}, mono::M) where {M <: Monomial} = Term{M()}(1)
convert(T::Type{<:Term}, v::Variable) = convert(T, Monomial(v))

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

(^)(v::Variable, ::Type{Val{x}}) where x = Monomial{((v, x),)}()
(*)(v1::Variable{Name}, v2::Variable{Name}) where Name = Monomial{((v1, 2),)}()
@generated function (*)(v1::Variable{N1}, v2::Variable{N2}) where {N1, N2}
    @assert N1 != N2
    if N1 < N2
        quote
            Monomial{((v1, 1), (v2, 1))}()
        end
    else
        quote
            Monomial{((v2, 1), (v1, 1))}()
        end
    end
end

@generated function promote_rule(::Type{Term{Monomial{P1}, T}}, ::Type{Term{Monomial{P2}, T}}) where {T, P1, P2}
    vars = Set{Any}()
    for v in P1
        push!(vars, v)
    end
    for v in P2
        push!(vars, v)
    end
    vars = Tuple(sort(collect(vars)))
    quote
        Term{Monomial{$(vars)}(), T}
    end
end

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
            p[i] = (p[i][1], p[i][2] + power[2])
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
(+)(m1::MonomialLike, m2::MonomialLike) = Term(m1) + Term(m2)
# (+)(v1::Variable, v2::Variable) = Term(Monomial(v1)) + Term(Monomial(v2))
(*)(x::Number, t::T) where {T <: Term} = T(x * t.coefficient)
(*)(t::T, x::Number) where {T <: Term} = T(t.coefficient * x)
(*)(x::Number, m::MonomialLike) = x * Term(m)
(*)(m::MonomialLike, x::Number) = Term(m) * x
(*)(t1::TermLike, t2::TermLike) = Term(t1) * Term(t2)
# (*)(x::Number, m::Monomial) = x * Term(m)


end
