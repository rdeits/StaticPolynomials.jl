module sp

using StaticArrays: SVector
import StaticArrays: push, setindex
import Base: *, +, ^, promote_rule, convert, show, isless, size, getindex

immutable QuasiStatic{N, T} <: AbstractVector{T}
    data::SVector{N, T}
    length::Int

    function QuasiStatic{N, T}() where {N, T}
        data = SVector{N, T}(ntuple(_ -> T(), Val{N}))
        new{N, T}(data, 0)
    end
    QuasiStatic{N, T}(data::SVector{N, T}, length=N) where {N, T} = new{N, T}(data, length)
end


function QuasiStatic{N}(data::SVector{M, T}) where {N, M, T}
    q = QuasiStatic{N, T}()
    for d in data
        q = push(q, d)
    end
    q
end

QuasiStatic(data::SVector{M, T}, length=M) where {M, T} = QuasiStatic{M, T}(data, length)


@inline getindex(v::QuasiStatic, i) = (@boundscheck (i >= 1 && i <= v.length) || throw(BoundsError()); v.data[i])
size(v::QuasiStatic) = (v.length,)
function push(v::QuasiStatic{N}, x) where {N}
    if v.length >= N
        error("Capacity reached")
    end
    QuasiStatic(setindex(v.data, x, v.length + 1), v.length + 1)
end

abstract type PolynomialLike end
abstract type TermLike <: PolynomialLike end
abstract type MonomialLike <: TermLike end
abstract type VariableLike <: MonomialLike end

immutable Variable{Name} <: VariableLike
end

show(io::IO, v::Variable{Name}) where Name = print(io, Name)

immutable Monomial{N, V} <: MonomialLike
    exponents::NTuple{N, Int64}
end

exponents(m::Monomial) = m.exponents
isless(m1::Monomial, m2::Monomial) = variables(m1) < variables(m2) || exponents(m1) < exponents(m2)
format_exponent(e) = e == 1 ? "" : "^$e"

function show(io::IO, m::Monomial)
    for (i, v) in enumerate(variables(m))
        if m.exponents[i] != 0
            print(io, v, format_exponent(m.exponents[i]))
        end
    end
end

variables(::Type{Monomial{N, V}}) where {N, V} = V
variables(m::Monomial) = variables(typeof(m))

convert(::Type{<:Monomial}, v::Variable{Name}) where {Name} = Monomial{1, (Name,)}((1,))

*(v1::Variable{N1}, v2::Variable{N2}) where {N1, N2} = Monomial{2, (N1, N2)}((1, 1))
*(v1::Variable{N}, v2::Variable{N}) where N = Monomial{1, (N,)}((2,))

immutable Term{T, MonomialType <: Monomial} <: TermLike
    coefficient::T
    monomial::MonomialType
end

(::Type{TermType})() where {T, N, V, TermType <: Term{T, Monomial{N, V}}} = TermType(0, Monomial{N, V}(ntuple(_ -> 0, Val{N})))

format_coefficient(c) = c == 1 ? "" : string(c)
show(io::IO, t::Term) = print(io, format_coefficient(t.coefficient), t.monomial)

convert(T::Type{<:Term}, m::Monomial) = T(1, m)
convert(T::Type{<:Term}, v::Variable) = T(Monomial(v))

@generated function convert(::Type{Term{T, Mono1}}, t::Term{T, Mono2}) where {T, Mono1, Mono2}
    args = Any[0 for v in variables(Mono1)]
    for (j, var) in enumerate(variables(Mono2))
        I = find(v -> v == var, variables(Mono1))
        if isempty(I)
            throw(InexactError())
        elseif length(I) > 1
            error("Duplicate variables in destination $Mono1")
        end
        args[I[1]] = :(t.monomial.exponents[$j])
    end
    quote
        Term{$T, $Mono1}(t.coefficient,
            Monomial{$(length(args)), $(variables(Mono1))}($(Expr(:tuple, args...))))
    end
end

immutable Polynomial{T <: Term, V <: AbstractVector{T}} <: PolynomialLike
    terms::V
end

Polynomial(terms::V) where {T <: Term, V <: AbstractVector{T}} = Polynomial{T, V}(terms)
convert(T::Type{<:Polynomial}, t::Term) = T(QuasiStatic(SVector(t)))
convert(T::Type{<:Polynomial}, m::Monomial) = T(Term(m))
convert(T::Type{<:Polynomial}, v::Variable) = T(Term(v))

# convert(T::Type{Polynomial{T, V1}}, p::Polynomial{T, V2}) where {T, V1, V2} = T(convert(V1, p.terms))

convert(T::Type{Polynomial{T1, V1}}, p::Polynomial{T2, V2}) where {T1, T2, V1, V2} = T(convert(V1, p.terms))

function show(io::IO, p::Polynomial)
    if !isempty(p.terms)
        print(io, p.terms[1])
        for i in 2:length(p.terms)
            print(io, " + ", p.terms[i])
        end
    end
end

function promote_rule(::Type{<:MonomialLike}, ::Type{<:MonomialLike})
    Monomial
end

function promote_rule(::Type{<:TermLike}, ::Type{<:TermLike})
    Term
end

@generated function promote_rule(::Type{Term{T, Mono1}}, ::Type{Term{T, Mono2}}) where {T, Mono1, Mono2}
    vars = Tuple(sort(collect(union(Set(variables(Mono1)),
                                    Set(variables(Mono2))))))
    quote
        Term{T, Monomial{$(length(vars)), $(vars)}}
    end
end

function promote_rule(::Type{<:PolynomialLike}, ::Type{<:PolynomialLike})
    Polynomial
end

@generated function promote_rule(::Type{Polynomial{T1, V1}}, ::Type{Polynomial{T2, V2}}) where {T1, T2, V1, V2}
    termtype = promote_rule(T1, T2)
    quote
        Polynomial{$termtype, Vector{$termtype}}
    end
end

function (+)(v1::Variable{Name}, v2::Variable{Name}) where {Name}
    Term(v1) + Term(v2)
end

function (+)(t1::Term{T, Mono}, t2::Term{T, Mono}) where {T, Mono}
    if t1.monomial < t2.monomial
        Polynomial(QuasiStatic(SVector(t1, t2)))
    elseif t1.monomial > t2.monomial
        Polynomial(QuasiStatic(SVector(t2, t1)))
    else
        terms = QuasiStatic{2, Term{T, Mono}}()
        terms = push(terms, Term{T, Mono}(t1.coefficient + t2.coefficient, t1.monomial))
        Polynomial(terms)
        # Polynomial([Term{T, Mono}(t1.coefficient + t2.coefficient, t1.monomial)])
    end
end

@generated function (+)(p1::Polynomial{T1, QuasiStatic{N1, T1}}, p2::Polynomial{T2, QuasiStatic{N2, T2}}) where {T1, N1, T2, N2}
    T = promote_type(T1, T2)
    Q = QuasiStatic{N1 + N2, T}
    quote
        terms = $Q()
        i1 = 1
        i2 = 1
        while i1 <= length(p1.terms) && i2 <= length(p2.terms)
            t1 = convert($T, p1.terms[i1])
            t2 = convert($T, p2.terms[i2])
            if t1.monomial < t2.monomial
                terms = push(terms, t1)
                i1 += 1
            elseif t1.monomial > t2.monomial
                terms = push(terms, t2)
                i2 += 1
            else
                terms = push(terms, $T(t1.coefficient + t2.coefficient,
                             t1.monomial))
                i1 += 1
                i2 += 1
            end
        end
        for i in i1:length(p1.terms)
            terms = push(terms, p1.terms[i])
        end
        for i in i2:length(p2.terms)
            terms = push(terms, p2.terms[i])
        end
        Polynomial(terms)
    end
end

@generated function (*)(m1::Monomial{N1, V1}, m2::Monomial{N2, V2}) where {N1, V1, N2, V2}
    vars = Tuple(sort(collect(union(Set(V1), Set(V2)))))
    args = []
    for (i, v) in enumerate(vars)
        i1 = findfirst(V1, v)
        i2 = findfirst(V2, v)
        if i1 != 0 && i2 != 0
            push!(args, :(m1.exponents[$i1] + m2.exponents[$i2]))
        elseif i1 != 0
            push!(args, :(m1.exponents[$i1]))
        else
            @assert i2 != 0
            push!(args, :(m2.exponents[$i2]))
        end
    end
    Expr(:call, :(Monomial{$(length(args)), $vars}), Expr(:tuple, args...))
end

(*)(t1::Term, t2::Term) = Term(t1.coefficient * t2.coefficient, t1.monomial * t2.monomial)
(+)(m1::Monomial, m2::Monomial) = Term(m1) + Term(m2)

(+)(t1::PolynomialLike, t2::PolynomialLike) = +(promote(t1, t2)...)
(*)(t1::TermLike, t2::TermLike) = *(promote(t1, t2)...)
*(x::Number, m::Monomial) = Term(x, m)
*(x::Number, v::Variable) = x * Monomial(v)
^(v::Variable{Name}, x::Integer) where Name = Monomial{1, (Name,)}((x,))

end
