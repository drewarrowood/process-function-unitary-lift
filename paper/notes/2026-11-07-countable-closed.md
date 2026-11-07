# Countable-closed conjecture: the downward-box argument

Date: 7 November 2026. Integrated as `lean/PFUL/CountableClosed.lean`, labels L-286–L-290.
Axioms: propext, Classical.choice, Quot.sound. No sorry.

## Result

Let X = {0,1}^ℕ with the product topology. Suppose F : X → X is exclusive: for every distinct s, t, some coordinate k satisfies s_k ≠ t_k and F(s)_k = F(t)_k. Let c ∈ X and let S ⊆ X be countable and closed. If F(x) = c for x ∉ S, then F has a unique fixed point, and that point differs from c in only finitely many coordinates.

There is no extra Baire-class, continuity-on-S, Cantor–Bendixson rank, or bounded-support assumption. This settles the countable-closed conjecture. It does not settle the general Baire-one question.

## The argument

For u, v ∈ X write B(u, v) for the full coordinate box between them: t ∈ B(u, v) if t_k = u_k wherever u_k = v_k. The box-closure lemma says that, for s ∈ S,

    {t : every changed coordinate k has F(s)_k ≠ c_k} ⊆ S.

Assume F has no fixed point. The finite-prefix solutions x_n satisfy x_n(k) = c_k for k ≥ n and F(x_n)(k) = x_n(k) for k < n. Each x_n lies in S: otherwise F(x_n) = c, the prefix equations force x_n = c, and x_n is a fixed point. The whole box B(c, x_n) lies in S, because every coordinate changed from x_n into that box is below n and satisfies F(x_n)_k = x_n(k) ≠ c_k.

Take a convergent subsequence x_{n_j} → y. Closedness gives B(c, y) ⊆ S. For t ∈ B(c, y), define t_j(k) = c_k if t_k = c_k and x_{n_j}(k) otherwise. Then t_j ∈ B(c, x_{n_j}) ⊆ S and t_j → t, so t ∈ S (`cluster_box_subset_of_prefix_fixed`, L-287). If y differed from c at infinitely many coordinates, B(c, y) would contain a copy of Cantor space, contradicting countability (`finite_diff_of_countable_box`, L-286). Thus y differs finitely from c.

A countable compact set can contain finite-support points converging to an infinite-support point. What it cannot contain is this forced family of boxes and their limits. Countability does not imply closedness: the finite-support set of zfcF is countable and not closed.

The finite-defect lemma gives that F(y) differs finitely from c. Choose N so that both y and F(y) agree with c beyond N. For a late n_j ≥ N whose prefix below N equals that of y, exclusivity forces x_{n_j} = y, and the prefix equations give F(y) = y (`exists_fixed_of_const_off_countable_closed`, L-288). Uniqueness is exclusivity on two fixed points (L-289). The fixed point differs finitely from c (L-290).

## Sharpness

* Closedness alone is not enough: `pad zfcF` is constant off a perfect nowhere-dense closed set and has no fixed point (L-284).
* Countability alone is not enough: zfcF is constant off the countable non-closed set of finite-support sequences.
* The general exclusive Baire-class-1 question remains open.
