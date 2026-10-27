# Round 27 (H.34.2): solve the symmetry-reduced Hermitian SOS (h27_export.py JSON) with Clarabel.jl, in Float64 or BigFloat.
# usage: julia h27_solve.jl problem.json BITS out.json   (BITS = 0 for Float64, else BigFloat precision in bits)
# Maximises gamma; writes gamma, status and every Gram block Q (real and imaginary parts as decimal strings) to out.json.
using Clarabel, SparseArrays, LinearAlgebra, JSON3, GenericLinearAlgebra
pjs, bits, outf = ARGS[1], parse(Int, ARGS[2]), ARGS[3]
if bits > 0; setprecision(BigFloat, bits); end
T = bits > 0 ? BigFloat : Float64
D = JSON3.read(read(pjs, String)); println("read"); flush(stdout)
rat(s) = (p = split(String(s), "/"); length(p) == 1 ? T(parse(BigInt, p[1])) : T(parse(BigInt, p[1])) / T(parse(BigInt, p[2])))
nb = [length(b.basis) for b in D.blocks]; m = 2 .* nb; sv = m .* (m .+ 1) .÷ 2
off = cumsum([1; sv[1:end-1]]) .+ 1           # x[1] = gamma
nx = 1 + sum(sv); r2 = 1 / sqrt(T(2))
function sidx(bi, i, j)                         # 0-based (i,j) in block bi -> (x index, coefficient)
    i, j = min(i, j), max(i, j)
    return off[bi] + j * (j + 1) ÷ 2 + i, (i == j ? one(T) : r2)
end
I_ = Int[]; J_ = Int[]; V_ = T[]; b = T[]
for (ri, row) in enumerate(D.rows)
    acc = Dict{Int,T}()
    for t in row.terms
        bi, r, s = t[1] + 1, t[2], t[3]; n = nb[bi]
        pairs = row.part == "re" ? ((r, s, 1), (n + r, n + s, 1)) : ((n + r, s, 1), (r, n + s, -1))
        for (i, j, sg) in pairs
            k, cf = sidx(bi, i, j); acc[k] = get(acc, k, zero(T)) + sg * cf
        end
    end
    nv = rat(row.nv); if nv != 0; acc[1] = nv; end
    for (k, v) in acc; if v != 0; push!(I_, ri); push!(J_, k); push!(V_, v); end; end
    push!(b, rat(row.rhs))
end
m0 = length(D.rows)
for k in 2:nx; push!(I_, m0 + k - 1); push!(J_, k); push!(V_, -one(T)); end
A = sparse(I_, J_, V_, m0 + nx - 1, nx); bb = [b; zeros(T, nx - 1)]
q = zeros(T, nx); q[1] = -one(T); P = spzeros(T, nx, nx)
cones = Clarabel.SupportedCone[Clarabel.ZeroConeT(m0); [Clarabel.PSDTriangleConeT(mm) for mm in m]...]
tol = bits > 0 ? T(10)^(-round(Int, bits * 0.30103 * 0.6)) : 1e-10
st = Clarabel.Settings{T}(verbose=true, chordal_decomposition_enable=false, presolve_enable=false, max_iter=500, tol_gap_abs=tol, tol_gap_rel=tol, tol_feas=tol, tol_ktratio=tol,
     static_regularization_constant = bits > 0 ? tol^2 : 1e-8, iterative_refinement_abstol = bits > 0 ? tol^2 : 1e-12,
     iterative_refinement_reltol = bits > 0 ? tol^2 : 1e-13, iterative_refinement_max_iter=20)
println("assembled: rows $(m0) vars $(nx) nnz $(nnz(A))"); flush(stdout)
solver = Clarabel.Solver{T}(); Clarabel.setup!(solver, P, q, A, bb, cones, st)
t0 = time(); sol = Clarabel.solve!(solver)
g = sol.x[1]; println("RESULT orbit $(D.orbit) bits $bits status $(sol.status) gamma* = $(Float64(g)) ($(string(g)[1:min(end,40)])) time $(round(time()-t0,digits=1))s")
Qs = []; mins = Float64[]; gaps = []
for bi in eachindex(nb)
    n = nb[bi]; X = zeros(T, m[bi], m[bi])
    for j in 0:m[bi]-1, i in 0:j
        k, cf = sidx(bi, i, j); X[i+1, j+1] = sol.x[k] * cf; X[j+1, i+1] = X[i+1, j+1]
    end
    Qr = X[1:n, 1:n] + X[n+1:end, n+1:end]; Qi = X[n+1:end, 1:n] - X[1:n, n+1:end]
    ev = sort(real(GenericLinearAlgebra.eigvals(Hermitian(Complex{T}.(Qr, Qi)))))
    push!(mins, Float64(ev[1])); push!(gaps, Float64.(ev))
    push!(Qs, Dict("re" => [string(x) for x in vec(Qr)], "im" => [string(x) for x in vec(Qi)], "n" => n))
end
println("min eigenvalue over blocks: ", minimum(mins))
allev = sort(vcat(gaps...)); println("log10 |eigenvalue| histogram (all blocks): ",
    [(e, count(x -> (x == 0 ? -400 : floor(Int, log10(abs(x)))) == e, allev)) for e in -120:2 if count(x -> (x == 0 ? -400 : floor(Int, log10(abs(x)))) == e, allev) > 0])
open(outf, "w") do io; JSON3.write(io, Dict("orbit" => D.orbit, "bits" => bits, "gamma" => string(g), "status" => string(sol.status), "Q" => Qs, "evals" => [[string(x) for x in e] for e in gaps])); end
