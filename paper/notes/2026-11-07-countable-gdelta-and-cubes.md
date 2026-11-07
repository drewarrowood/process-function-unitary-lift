# Countable G-delta sets and coordinate-box thinness

7 November 2026. Integrated as `lean/PFUL/CountableGDelta.lean` (L-291–L-300) and `lean/PFUL/CubeThin.lean` (L-301–L-303). Axioms: propext, Classical.choice, Quot.sound. No sorry. The general Baire-one question is not solved.

## 1. Countable G-delta exceptional sets

**Theorem.** If F : {0,1}^ℕ → {0,1}^ℕ is exclusive, S is countable and Gδ, and F(x) = c off S, then F has a unique fixed point (L-294, L-300). No Cantor–Bendixson rank or Baire class is assumed. Arbitrary values on such an S, constant elsewhere, are automatically Baire class 1 (L-298). This is a larger regularity subcase of the Baire-one problem, not a solution of it.

Gδ is a property of the set S. It is not a statement about the coordinate fibers {x | F(x)_k ≠ c_k}.

**Structural theorem (L-292).** If F is exclusive, equals c off a countable S, and has no fixed point, then some y differs from c infinitely often and every finite corner of the box

    K(c, y) = {t : t_k = c_k whenever y_k = c_k}

lies in S. No closedness or definability of S is used. The finite corners are the points of K(c, y) that differ finitely from c. Each such corner equals a point of some prefix box K(c, x_n), by resetting the other coordinates of a late prefix solution to c (L-291). It is not merely a limit of such points.

K(c, y) is a perfect compact infinite Boolean product, and its finite corners are dense. If S were Gδ, S ∩ K(c, y) would be a countable dense Gδ in that product, which Baire category forbids (L-293): a countable union of singletons cannot cover a dense Gδ, because singleton interiors are empty. Hence a fixed-point-free countably supported exclusive map has a non-Gδ actual exceptional set {F ≠ c} (L-295). That statement does not assume Baire class 1.

Closedness is not silently dropped. It is replaced, for this theorem, by Gδ plus category. There are countable Gδ sets with uncountable closure, so passing to the closure need not reduce the theorem to the closed case.

**Illustration, not a Lean declaration.** For each n and each binary word w of length n, take the point whose even coordinates are w followed by zeros and whose odd coordinates have exactly the nth marker on. These points form a countable discrete set S. Its closure is S together with the perfect set of points with all odd coordinates zero. S is open in that closure, hence Gδ in this metrizable space. This construction is not formalized.

## 2. Exact Baire-one criterion on an arbitrary countable exceptional set

For F constant off a countable S, with A_k = {x : F(x)_k ≠ c_k} and E = {x : F(x) ≠ c} = ⋃_k A_k,

    F is Baire one  ↔  every A_k is Gδ

(L-299). Countability is used in the reverse direction. Each A_k of a countably supported map is already Fσ. The forward direction reads a Boolean fiber of a pointwise limit of continuous maps as a Gδ (L-296, L-297). The reverse direction approximates each coordinate by the countable-Gδ theorem (L-298) and reassembles the coordinates.

A hypothetical fixed-point-free Baire-one map constant outside a countable set must therefore satisfy all of the following:

* its exceptional set E is countable and is not Gδ (the first half needs no Baire class);
* E contains every finite corner of some infinite coordinate box (again no Baire class);
* each A_k is a countable Gδ;
* the union E fails to be Gδ.

A countable union of Gδ sets need not be Gδ, so these facts do not settle exclusive Baire one on an arbitrary countable exceptional set. zfcF remains the warning that an arbitrary countable S does not make F Baire one by itself. The unrestricted Baire-one question is open.

## 3. Closed sets with no infinite coordinate box

S is coordinate-box thin when every full coordinate box inside S has finitely many free coordinates. Countability implies box thinness (L-301). If S is closed and box-thin, an exclusive F constant off S has a fixed point, with no countability hypothesis (L-302). Equivalently, a closed exceptional set for a fixed-point-free exclusive map contains an infinite-dimensional coordinate box (L-303). This abstracts the two uses of countability in the closed proof: output defects and the limiting input defect are both finite because an infinite box cannot sit in S, and closedness still supplies the limit box.

**Illustration, not a Lean declaration.** Tie coordinates in pairs (2n, 2n+1) for n ≥ 1, and leave coordinates 0 and 1 free. The resulting closed set is uncountable. Any coordinate box inside it frees at most coordinates 0 and 1. The padded set P of L-284 is not box-thin: it contains the infinite even-coordinate cube.

## 4. What is used, and what is not claimed

* Boolean alphabets only. No general-alphabet extension is claimed.
* Countability excludes uncountable boxes and, in the Gδ theorem, feeds the category contradiction.
* Closedness promotes finite prefix boxes to a full limit box. The Gδ theorem replaces that step. It does not discard it in the closed theorem.
* Constancy off S supplies box closure. There is no replacement for arbitrary Baire-one exclusive maps.
* Baire class 1 gives the coordinate Gδ criterion. It does not make the union E a Gδ.
