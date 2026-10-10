# Appendix D (draft): the physics route to "purifiable classical process => mixture of process functions"

Status labels: **[proved]**, **[conjecture]**, **[gap]**. Nothing here proves the conjecture; it is still open.

Setting. A purification of a classical process W (diagonal; equivalently a stochastic map p(i|o) on the joint
classical inputs i and outputs o of the parties) is a unitary V : P (x) O -> F (x) I together with a fixed source
state |psi> in P such that (i) W = Tr_F of the Choi vector of V(|psi> (x) .), and (ii) for every choice of local
operations (unitaries with ancillas) the induced map P (x) ancillas -> F (x) ancillas is unitary (AFNB 2017).
Write  V|psi, o> = sum_i |i> (x) |v_{o,i}>  with  v_{o,i} in F.

**Lemma D.1 [proved].**  <v_{o',i'} | v_{o,i}> = delta_{o o'} delta_{i i'} p(i|o).
Proof. The Choi matrix of the induced channel O -> I is  sum_{o,o'} |o><o'| (x) Tr_F[ V|psi,o><psi,o'|V^dagger ],
whose ((o,i),(o',i')) entry is <v_{o',i'}|v_{o,i}>. W is diagonal with diagonal entries p(i|o). QED.
Consequence: the sink holds a perfect record of the pair (o,i): the normalised vectors f_{o,i} = v_{o,i}/sqrt(p(i|o))
(over the support of W) are orthonormal, so dim F >= |supp W| = rank W = r (the same r as in AFNB Thm 4).
Checked numerically on the source-sink lift of Lugano (code/stochastic/physics/lemma_d1_check.py).

**Lemma D.2 [proved; negative].** Conditions (i)-(ii) restricted to the source state |psi> impose nothing beyond
W being a classical process. For classical deterministic interventions with input copies, o = f(i) (+) a with the
input i copied to a private ancilla, the output for ancilla value a is sum_i |i>_anc (x) sqrt(p(i|f(i)+a)) f_{f(i)+a, i};
by D.1 these are orthogonal for a != a' and have total norm sum_i p(i|f(i)+a) = 1 (logical consistency).
Hence any non-purifiability (e.g. E_ex1, orbits 7 and 50) must come from the action of V on source states
orthogonal to |psi>. Any proof of the conjecture must use those states. This is where proposal (2) breaks down:
the "which-function" label lambda cannot come from a basis of the span of |psi> alone.

**Where proposal (2) fails [gap].** The intended argument: under each intervention the global map is a generalised
permutation conditioned on a source label lambda; expanding |psi> = sum_lambda c_lambda |lambda> gives
W = sum |c_lambda|^2 W_{w_lambda}. Three gaps:
 (a) Unitarity under local unitaries does not obviously make V, restricted to classical party inputs, a generalised
     permutation. D.1 gives orthogonality only for the fixed |psi>, and only after tracing the party wires through W.
 (b) Even when it holds for each intervention f separately, the label lambda may depend on f (no single basis of P
     works for all f). Ruling this out is exactly the noncontextuality-type step that is missing.
 (c) Coherences in |psi> across labels: they vanish from W by D.1, but they constrain V on psi-perp, see (b).

**Conjecture D.3.** If V purifies a classical process, there is an orthonormal basis {lambda} of P such that
V|lambda, o> = phase * |w_lambda(o)> (x) |g_lambda(o)> for functions w_lambda, with g_lambda injective on outputs.
D.3 implies the conjecture: each w_lambda must then be a process function, since V must stay unitary under classical
interventions restricted to the source state |lambda>, and by Baumeler-Wolf that means a unique fixed point.
D.3 holds for our source-sink lifts. It has not been tested on the non-permutation purifications found by the
optimiser (Lugano, App. C); that test is the next step. A counterexample to D.3 that is still a mixture would refute
only D.3, not the conjecture.

## D.4 Conjecture D.3 is false (update, Oct 10 2026) [proved, exact counterexample]

Write G_{i,o} = V_o^dagger (Pi_i (x) 1_F) V_o on P, where V_o|s> = V|s,o>. D.3 is equivalent to: all G_{i,o} are
projectors that commute pairwise (their common eigenbasis is the label basis lambda). Counterexample: a causally
ordered circuit (code/stochastic/physics/d3_counterexample.py). Party A has trivial input and output oA. The source is
P = m (x) a. Apply H^{oA} to m, CNOT m -> a, send m to B's input, and route (oA, oB, a) to the sink. V is a
permutation-and-Hadamard circuit of unitaries in a fixed causal order, so it is a valid unitary process. With
psi = |00> the process is classical: p(iB|oA=0) = delta_{iB,0} and p(iB|oA=1) = 1/2. Lemma D.1 holds: W is diagonal.
W is a mixture of process functions (w_lambda(oA) = lambda*oA). But the G's are Z-projectors for oA=0 and
X-projectors for oA=1. They do not commute (commutator norm 1/2), so no source basis works. Restricting to psi does
not help either: psi = |00> is an eigenvector of the oA=0 projectors only.

Consequence. Gap (b) is real. Even for causal processes, the "which-function" randomness is generated contextually,
by measuring the quantum source in a basis that depends on earlier outputs. So no argument that extracts a single
classical label from the source can work, and unitarity under all local unitaries does not force one. The mixture
conclusion still holds here for a different reason: every causally ordered classical process is a mixture of causal
deterministic ones. A proof of "purifiable => mixture of process functions" therefore has to show directly that
W lies in conv(PF), for example that purifiability implies every facet inequality of the PF polytope. It cannot go
through a source-label decomposition. Status: the conjecture is open; D.3 is refuted; no counterexample to the
conjecture itself.

## D.5 The hull route (Oct 10 2026)

**Proposition D.5 [proved]: validity under quantum-controlled interventions is automatic, so it cannot be the
criterion.** Let W be any classical process, including E_ex1 and all 49 open orbits. Let the parties apply arbitrary
local instruments, coherently controlled by a shared ancilla that may be entangled across parties. Then the
probabilities are normalised. Reason: W is diagonal, so it dephases every party's input and output. The effective
intervention is then a classical joint behaviour q(o|i) produced from a shared quantum state by local operations, so
q is non-signalling. Every non-signalling behaviour is an affine (not necessarily convex) combination of local
deterministic ones. The normalisation sum_{i,o} p(i|o) q(o|i) is affine in q and equals 1 on every local
deterministic q (logical consistency), so it equals 1 for all such q. Positivity is termwise. So the proposed test
"valid under quantum-controlled interventions" holds for every classical process. It cannot separate E_ex1 from PF
mixtures, and step (3) of the plan is moot. Purifiability is strictly stronger only because of its unitarity
(reversibility) requirement.

**Proposition D.6 [proved, sketch]: classical-reversible purifiability <=> mixture of PFs.** Call W
classically purifiable if it is the marginal, for a random source value lambda, of a classical reversible process: a
bijection (lambda, o) -> (i, sink) that stays a bijection P -> F under every deterministic local intervention.
For a fixed lambda this is a deterministic process. Bijectivity of the composite map under every intervention f
forces exactly one consistent execution: zero leaves the source value with no image, and two collide by counting.
So each w_lambda is a process function (Baumeler-Wolf 2016), and W = sum_lambda p(lambda) W_{w_lambda}. The converse
is the source-sink construction with a random source. Hence **the conjecture is equivalent to: a classical process
that is quantum-purifiable is already classically purifiable.** D.4 shows the quantum purification itself need not be
classical (its labels are contextual), so this has to be argued at the level of W.

**Facets of the PF hull [computation].** The 744 process functions (3 parties, binary) span a 37-dimensional affine
space. Facet enumeration results are recorded below. Each facet that some open orbit violates is a candidate
inequality that purifiability would have to imply.
Full facet enumeration was not done: pycddlib does not build on the box, and 744 vertices in dimension 37 may have
very many facets. Instead, sep.py finds by LP a separating inequality of the PF hull (box-normalised, |f| <= 1):
E_ex1 and orbit 7 violate one by 6.0, orbit 8 by 4.0, and a PF mixture by 0, as expected. These inequalities are not
reduced modulo the affine hull or by symmetry, so their supports carry no meaning yet. **No inequality has been
derived from purifiability. The conjecture remains open.** Next steps: enumerate facets with lrs/normaliz or by
symmetry-adapted LP, then try to derive one facet class from Theorem 4 (isotropy) together with Lemma D.1.

## D.7 Facets of the PF hull: partial (Oct 10 2026)

Tools. lrslib 7.3 builds from source with gcc (no make, no GMP on the box; hybrid 64/128-bit plus built-in MP
arithmetic). normaliz and PANDA were not installed: there is no make/cmake, conda or sudo on the box. The full
enumeration with lrs (744 vertices in the 37-dim span, `facets/pf.ext`) produced no output in 5 minutes, not even
from `estimates`, because the input is highly degenerate. **No facet count or runtime estimate yet.** A double
description or symmetry-exploiting code (normaliz, PANDA with the 384-element symmetry group) on a rented
multi-core CPU is the natural next step; its cost is unknown until a short benchmark is run.

Facets found by polar LP (`facets/facetlp.py`). Each LP optimum was checked to be a facet: its tight PFs have affine
rank 36. Facets are classified up to the 384 symmetries (party permutations and input/output relabelings; all 384
preserve the PF set). Over E_ex1 and the 51 sampled non-deterministic vertex orbits, the optimal separating facets
fall into **8 classes**. Class 0 (418 tight PFs) is violated by E_ex1 and 24 orbits, including orbit 8. Class 2 (418)
covers orbits 7, 50 and 15 others; classes 1, 3-7 cover the rest. The class-0 facet, written with joint inputs i and
outputs o (bits of parties A, B, C):

    p(000|000) <= p(000|001) + p(010|001) + p(000|100) + p(010|110) + p(011|111)

E_ex1 gives 1/2 > 0. Combinatorial content for a process function w: if w(000) = 000, then w(001) is 000 or 010,
or w(100) = 000, or w(110) = 010, or w(111) = 011.

**Derivation from purifiability: not achieved.** A natural attempt: use Lemma D.1 to read p(i|o) as squared norms of
orthogonal sink vectors, then try to show the class-0 inequality follows from unitarity under suitable superpositions
of the five interventions involved. This has not been carried through and is not claimed.

### D.7 update: complete facet list (normaliz, Oct 10 2026)

Run: normaliz 3.8.9 (`-c -x=32`) on a rented 32-core vast.ai CPU instance, about 1.9 h, about $0.27 in total; the
instance was then destroyed. Input `facets/pf.in` (744 PFs in 37 independent coordinates of p(i|o); all test points
lie in the same affine span). Output `facets/pf.out.gz`.

**The 3-party binary PF hull has exactly 29,344 facets, in 93 orbits** under the 384-element symmetry group
(`facets/classify.py`, `classes_full.json`). Orbit sizes: 384 (66 orbits), 192 (17), 128 (2), 96 (5), 64 (3).
The 8 LP classes of D.7 are all among them: LP classes 0, 1, 2 are full orbits 82, 83, 84 (418 tight PFs);
classes 3-6 are orbits 42, 38, 37, 41 (238); class 7 is orbit 91 (436).

Violations. E_ex1 violates 24 of the 93 facet orbits, orbit 7 violates 53, orbit 8 violates 41, and every test point
violates at least one. **Facet orbit 82, the class-0 inequality of D.7
p(000|000) <= p(000|001)+p(010|001)+p(000|100)+p(010|110)+p(011|111), is violated by E_ex1 and by all 51 sampled
non-deterministic vertex orbits** (by some member of the facet's orbit). So this single inequality class separates
every sampled non-deterministic vertex from the PF hull. Proving it from purifiability is the natural next target.
Status: facet list exact (normaliz); the derivation from purifiability is open.
