show(io::IO, v::Variable{Name}) where Name = print(io, Name)

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

function show(io::IO, m::Monomial{P}) where {P}
    for power in P
        show(io, power)
    end
end

function show(io::IO, t::Term{Mono, T}) where {Mono, T}
    print(io, t.coefficient, Mono)
end

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
