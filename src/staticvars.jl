module sp

using StaticArrays: SVector
import Base: *, +, ^, promote_rule, convert, show, isless, size, getindex,
    one, zero

abstract type PolynomialLike end
abstract type TermLike <: PolynomialLike end
abstract type MonomialLike <: TermLike end
abstract type VariableLike <: MonomialLike end

immutable Variable{Name} <: VariableLike
end

name(::Type{Variable{Name}}) where {Name} = Name
name(v::Variable) = name(typeof(v))

immutable Monomial{N, V} <: MonomialLike
    exponents::NTuple{N, Int64}
end
Monomial{N, V}() where {N, V} = Monomial{N, V}(ntuple(_ -> 0, Val{N}))

exponents(m::Monomial) = m.exponents
variables(::Type{Monomial{N, V}}) where {N, V} = V
variables(m::Monomial) = variables(typeof(m))

immutable Term{T, MonomialType <: Monomial} <: TermLike
    coefficient::T
    monomial::MonomialType
end
Term(m::TermLike) = convert(Term, m)
Term(x::T) where {T} = Term{T, Monomial{0, tuple()}}(x, Monomial{0, tuple()}())

variables(::Type{Term{T, M}}) where {T, M} = variables(M)
variables(t::Term) = variables(typeof(t))

immutable Polynomial{T <: Term, V <: AbstractVector{T}} <: PolynomialLike
    terms::V
end
Polynomial(terms::V) where {T <: Term, V <: AbstractVector{T}} = Polynomial{T, V}(terms)

variables(::Type{<:Polynomial{T}}) where {T} = variables(T)
variables(p::Polynomial) = variables(typeof(p))


convert(::Type{<:Monomial}, v::Variable{Name}) where {Name} = Monomial{1, (Name,)}((1,))
convert(T::Type{<:Term}, m::Monomial) = T(1, m)
convert(T::Type{<:Term}, v::Variable) = convert(T, Monomial(v))
convert(T::Type{Term{T1, M1}}, x) where {T1, M1} = T(convert(T1, x), M1())
convert(T::Type{<:Polynomial}, t::Term) = T(SVector(t))
convert(T::Type{<:Polynomial}, x::TermLike) = convert(T, Term(x))
convert(T::Type{Polynomial{T1, V1}}, x) where {T1, V1} = convert(T, Term(x))
convert(T::Type{Polynomial{T1, V1}}, p::Polynomial) where {T1, V1} = T(convert(V1, p.terms))

@generated function convert(::Type{Term{T1, Mono1}}, t::Term{T2, Mono2}) where {T1, Mono1, T2, Mono2}
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
        Term{$T1, $Mono1}(convert(T1, t.coefficient),
            Monomial{$(length(args)), $(variables(Mono1))}($(Expr(:tuple, args...))))
    end
end


one(::Type{Monomial{N, V}}) where {N, V} = Monomial{N, V}()
zero(::Type{Term{T, M}}) where {T, M} = Term{T, M}(0, M())
zero(t::TermLike) = zero(typeof(t))


@generated function isless(::Variable{N1}, ::Variable{N2}) where {N1, N2}
    quote
        $(N1 < N2)
    end
end

@generated function isless(m1::Monomial{N1, V1}, m2::Monomial{N2, V2}) where {N1, V1, N2, V2}
    if V1 < V2
        :(true)
    elseif V1 > V2
        :(false)
    else
        :(exponents(m1) < exponents(m2))
    end
end

isless(t1::Term, t2::Term) = t1.monomial < t2.monomial

show(io::IO, v::Variable{Name}) where Name = print(io, Name)
function show(io::IO, t::Term)
    if t.coefficient == 0
        print(io, "0")
    elseif t.coefficient == 1
        print(io, t.monomial)
    else
        print(io, t.coefficient)
        if !all(t.monomial.exponents .== 0)
            print(io, t.monomial)
        end
    end
end

format_exponent(e) = e == 1 ? "" : "^$e"
function show(io::IO, m::Monomial)
    if all(m.exponents .== 0)
        print(io, "1")
    else
        for (i, v) in enumerate(variables(m))
            if m.exponents[i] != 0
                print(io, v, format_exponent(m.exponents[i]))
            end
        end
    end
end

function show(io::IO, p::Polynomial)
    if isempty(p.terms)
        print(io, "0")
    else
        print(io, p.terms[1])
        for i in 2:length(p.terms)
            print(io, " + ", p.terms[i])
        end
    end
end


function promote_rule(::Type{<:MonomialLike}, ::Type{<:MonomialLike})
    Monomial
end

function promote_rule(::Type{Term{T1, M}}, ::Type{Term{T2, M}}) where {T1, T2, M}
    Term{promote_type(T1, T2), M}
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
    termtype = promote_type(T1, T2)
    quote
        Polynomial{$termtype, Vector{$termtype}}
    end
end

function jointerms(terms1::AbstractArray{<:Term}, terms2::AbstractArray{<:Term})
    T = promote_type(eltype(terms1), eltype(terms2))
    terms = Vector{T}(length(terms1) + length(terms2))
    i = 1
    i1 = 1
    i2 = 1
    deletions = 0
    while i1 <= length(terms1) && i2 <= length(terms2)
        t1 = convert(T, terms1[i1])
        t2 = convert(T, terms2[i2])
        if t1.monomial < t2.monomial
            terms[i] = t1
            i1 += 1
        elseif t1.monomial > t2.monomial
            terms[i] = t2
            i2 += 1
        else
            terms[i] = Term(t1.coefficient + t2.coefficient,
                            t1.monomial)
            i1 += 1
            i2 += 1
            deletions += 1
        end
        i += 1
    end
    for j in i1:length(terms1)
        terms[i] = terms1[j]
        i += 1
    end
    for j in i2:length(terms2)
        terms[i] = terms2[j]
        i += 1
    end
    resize!(terms, length(terms) - deletions)
end

function (+)(term1::T1, term2::T2) where {T1 <: Term, T2 <: Term}
    t1, t2 = promote(term1, term2)
    if t1.monomial < t2.monomial
        Polynomial([t1, t2])
    elseif t1.monomial > t2.monomial
        Polynomial([t2, t1])
    else
        Polynomial([(t1.coefficient + t2.coefficient, t1.monomial)])
    end
end

(+)(p1::Polynomial, p2::Polynomial) = Polynomial(jointerms(p1.terms, p2.terms))
(+)(t1::TermLike, t2::TermLike) = Term(t1) + Term(t2)
(+)(t1::PolynomialLike, t2::PolynomialLike) = +(promote(t1, t2)...)
(+)(p::PolynomialLike, x::Any) = p + Polynomial(Term(x))
(+)(x::Any, p::PolynomialLike) = Polynomial(Term(x)) + p

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

(*)(t1::TermLike, t2::TermLike) = *(promote(t1, t2)...)
(*)(t1::Term, t2::Term) = Term(t1.coefficient * t2.coefficient, t1.monomial * t2.monomial)
(*)(t1::Term, m2::MonomialLike) = Term(t1.coefficient, t1.monomial * Monomial(m2))
(*)(m1::MonomialLike, t2::Term) = Term(t2.coefficient, Monomial(m1) * t2.monomial)
(*)(x::Any, t::Term) = Term(x * t.coefficient, t.monomial)
(*)(t::Term, x::Any) = Term(t.coefficient * x, t.monomial)
(*)(t::TermLike, x::Any) = Term(t) * x
(*)(x::Any, t::TermLike) = x * Term(t)
(*)(t::TermLike) = t
(*)(v1::Variable{N1}, v2::Variable{N2}) where {N1, N2} = Monomial{2, (N1, N2)}((1, 1))
(*)(v1::Variable{N}, v2::Variable{N}) where N = Monomial{1, (N,)}((2,))

^(v::Variable{Name}, x::Integer) where Name = Monomial{1, (Name,)}((x,))

@inline subs(v::Variable{Name}, s::Pair{Variable{Name}}) where {Name} = s.second
@inline subs(v::Variable{N1}, s::Pair{Variable{N2}}) where {N1, N2} = v

@generated function subs(v::Variable, s::NTuple{N, Pair{<:Variable}}) where {N}
    expr = :(v)
    for (i, p) in enumerate(s.parameters)
        varname = name(p.parameters[1])
        if varname == name(v)
            expr = :(s[$i].second)
        end
    end
    expr
end

@generated function subs(m::Monomial{N, V}, s::NTuple{M, Pair{<:Variable}}) where {N, V, M}
    args = Expr[]
    for (i, varname) in enumerate(V)
        push!(args, :(subs(Variable{$(Expr(:quote, varname))}(), s) ^ m.exponents[$i]))
    end
    Expr(:call, :(*), args...)
end

function subs(t::Term, s::NTuple{N, Pair{<:Variable}}) where {N}
    t.coefficient * subs(t.monomial, s)
end

function remaining_variables(p::Type{<:Polynomial}, s::Type{<:NTuple{N, Pair{<:Variable}}}) where N
    subs_vars = Set{Symbol}([name(p.parameters[1]) for p in s.parameters])
    poly_vars = Set{Symbol}(collect(variables(p)))
    setdiff(poly_vars, subs_vars)
end

function subs_complete(p::Polynomial{Term{T, M}}, s::NTuple{N, Pair{<:Variable}}) where {T, M, N}
    result = zero(Base.promote_op(+, T, T))
    for term in p.terms
        result += subs(term, s)
    end
    result
end

function subs_partial(p::Polynomial, s::NTuple{N, Pair{<:Variable}}) where N
    newterms = [subs(t, s) for t in p.terms]
    sort!(newterms)
    Polynomial(newterms)
end


@generated function subs(p::Polynomial, s::NTuple{N, Pair{<:Variable}}) where N
    v = remaining_variables(p, s)
    if isempty(v)
        quote
            subs_complete(p, s)
        end
    else
        quote
            subs_partial(p, s)
        end
    end
end

subs(v::PolynomialLike, s::Vararg{<:Pair{<:Variable}}) = subs(v, s)
subs(x, s::Vararg{Pair{<:Variable}}) = x

(::Polynomial)(s::Vararg{Pair{<:Variable}}) = subs(p, s...)
(::Term)(s::Vararg{Pair{<:Variable}}) = subs(p, s...)
(::Monomial)(s::Vararg{Pair{<:Variable}}) = subs(p, s...)

end # module
