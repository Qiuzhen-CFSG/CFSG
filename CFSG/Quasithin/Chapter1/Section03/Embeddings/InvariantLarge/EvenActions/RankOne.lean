module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.RankOne.Tori
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.RankOne.Permuting
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing

/-!
# The rank-one cyclicity step in Proposition 1.3.4

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, printed p.511
(PDF p.528), Lemma A.3.15(5), pp.50–51 (PDF pp.61–62), and Remark A.2.4, p.33.

The raw source configuration has finite SQTK J, F*(J) = D nonabelian simple,
S Sylow₂(J), a prime p > 3, B ≤ D a p-subgroup, and BS = SB. In case (5),
D is defined over the field of order 2^n, n > 1; B ≤ FH in Aut(D), F is a
cyclic field subgroup of order f dividing n, H is an F-invariant Cartan of
N_I(S ∩ D), and I is the inner-diagonal part of FBD = HBD.

Here a stronger argument proves the required cyclicity from the base
group-theoretic hypotheses alone. Restrict S to the normal group D. The
permuting product B(S ∩ D) is proper, since a nonabelian simple group cannot
have only 2 and p as prime divisors. Concrete rank-one geometry puts this
product in N_D(S ∩ D). A fixed coset conjugates B into the concrete cyclic
torus of that Borel. Thus no extra Cartan containment or field/inner-diagonal
disjointness premise remains to discharge. The raw field–Cartan hypotheses
may be retained in the source application, but are unnecessary for this
stronger rank-one conclusion. No assertion identifying the given H is made.

All three alternatives contain actual model isomorphisms. For PSU₃(2^n)
the matrix field has order (2^n)^2 and its involution is the 2^n-power map.
Simplicity is inherited from D; no model order or simplicity certification
is needed. The parent development owns the classification branch assembly.
-/

@[expose] public section

open Subgroup
open scoped Pointwise

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.RankOne

/-- The three actual rank-one carriers in Remark A.2.4, with their defining
field degree. This predicate includes multiplicative equivalences. -/
def IsBinaryRankOne (D : Type*) [Group D] (n : ℕ) : Prop :=
  ClassicalGroup.IsPSL D 2 (2 ^ n) ∨ ClassicalGroup.IsPSU D 3 (2 ^ n) ∨
    ∃ m : ℕ, n = 2 * m + 1 ∧
      Nonempty (D ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)

private theorem model_sylow_facts {D : Type*} [Group D] [Finite D]
    {n : ℕ} (hn : 1 < n) (hmodel : IsBinaryRankOne D n) (T : Sylow 2 D) :
    ChapterF.Source.RankOneSylowFacts T := by
  rcases hmodel with h | h | ⟨m, _, ⟨e⟩⟩
  · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
    exact ChapterF.Source.rankOneSylowFacts_of_equiv T e
      (ChapterF.Source.rankOneSylowFacts_psl2 F n (by omega) hF _)
  · obtain ⟨F, _, _, J, hF, hconj, ⟨e⟩⟩ := h
    exact ChapterF.Source.rankOneSylowFacts_of_equiv T e
      (ChapterF.Source.rankOneSylowFacts_psu3 J n (by omega) hF hconj _)
  · exact ChapterF.Source.rankOneSylowFacts_of_equiv T e
      (ChapterF.Source.suzuki_rankOneSylowFacts m _)

/-- In a nonabelian simple binary rank-one group, an odd p-subgroup
permuting with a Sylow two-subgroup is cyclic. Borel and torus containment
are proved from permutability and the concrete model geometry. -/
theorem isCyclic_of_permuting {D : Type*} [Group D] [Finite D] [IsSimpleGroup D]
    (hna : ¬ IsMulCommutative D) {n p : ℕ} [Fact p.Prime]
    (hn : 1 < n) (hmodel : IsBinaryRankOne D n) (hp : p ≠ 2)
    (T : Sylow 2 D) (B : Subgroup D) (hB : IsPGroup p B)
    (hperm : (B : Set D) * (T : Set D) = (T : Set D) * (B : Set D)) :
    IsCyclic B := by
  have hBN := permuting_le_normalizer hna T (model_sylow_facts hn hmodel T) hp B hB hperm
  rcases hmodel with h | h | ⟨m, hnm, ⟨e⟩⟩
  · exact psl2_normalizer_isCyclic (by omega) h hp T B hB hBN
  · exact psu3_normalizer_isCyclic (by omega) h hp T B hB hBN
  · exact suzuki_normalizer_isCyclic (by omega) e hp T B hB hBN

private theorem permuting_restrict {J : Type*} [Group J] (B S D : Subgroup J)
    (hBD : B ≤ D)
    (hperm : (B : Set J) * (S : Set J) = (S : Set J) * (B : Set J)) :
    (B.subgroupOf D : Set D) * (S.subgroupOf D : Set D) =
      (S.subgroupOf D : Set D) * (B.subgroupOf D : Set D) := by
  apply Set.Subset.antisymm
  · rintro x ⟨b, hb, s, hs, rfl⟩
    have hx : (b : J) * (s : J) ∈ (S : Set J) * (B : Set J) :=
      hperm ▸ Set.mul_mem_mul hb hs
    obtain ⟨s', hs', b', hb', he⟩ := hx
    change s' * b' = (b : J) * (s : J) at he
    have hsD : s' ∈ D := by
      have hh : s' * b' ∈ D := by rw [he]; exact D.mul_mem b.property s.property
      simpa only [mul_inv_cancel_right] using D.mul_mem hh (D.inv_mem (hBD hb'))
    exact ⟨⟨s', hsD⟩, hs', ⟨b', hBD hb'⟩, hb', Subtype.ext he⟩
  · rintro x ⟨s, hs, b, hb, rfl⟩
    have hx : (s : J) * (b : J) ∈ (B : Set J) * (S : Set J) :=
      hperm.symm ▸ Set.mul_mem_mul hs hb
    obtain ⟨b', hb', s', hs', he⟩ := hx
    change b' * s' = (s : J) * (b : J) at he
    have hsD : s' ∈ D := by
      have hh : b' * s' ∈ D := by rw [he]; exact D.mul_mem s.property b.property
      simpa only [inv_mul_cancel_left] using D.mul_mem (D.inv_mem (hBD hb')) hh
    exact ⟨⟨b', hBD hb'⟩, hb', ⟨s', hsD⟩, hs', Subtype.ext he⟩

/-- Ambient form of the rank-one step: the Sylow subgroup restricts to
the actual normal simple subgroup D, and BS = SB restricts with it. -/
theorem isCyclic_of_simple_normal {J : Type*} [Group J] [Finite J]
    (D : Subgroup J) [D.Normal] [IsSimpleGroup D]
    (hna : ¬ IsMulCommutative D) {n p : ℕ} [Fact p.Prime]
    (hn : 1 < n) (hmodel : IsBinaryRankOne D n) (hp : 3 < p)
    (S : Sylow 2 J) (B : Subgroup J) (hB : IsPGroup p B) (hBD : B ≤ D)
    (hperm : (B : Set J) * (S : Set J) = (S : Set J) * (B : Set J)) :
    IsCyclic B := by
  obtain ⟨T, hT⟩ := S.exists_subgroupOf_eq_of_normal D
  have hm := permuting_restrict B (S : Subgroup J) D hBD hperm
  have hmp : (B.subgroupOf D : Set D) * (T : Set D) =
      (T : Set D) * (B.subgroupOf D : Set D) := by
    change (B.subgroupOf D : Set D) * ((T : Subgroup D) : Set D) =
      ((T : Subgroup D) : Set D) * (B.subgroupOf D : Set D)
    rwa [hT]
  exact (subgroupOfEquivOfLe hBD).isCyclic.mp
    (isCyclic_of_permuting hna hn hmodel (by omega) T (B.subgroupOf D)
      hB.comap_subtype hmp)

/-- The conclusion required in A.3.15(5)'s rank-one branches of 1.3.4.
Normality is derived from the actual equality F*(J) = D. This stronger
theorem uses no additional field–Cartan or SQTK consequences. -/
theorem isCyclic_of_generalizedFitting {J : Type*} [Group J] [Finite J]
    (D : Subgroup J) [IsSimpleGroup D]
    (hD : Theory.GroupTheory.generalizedFitting J = D)
    (hna : ¬ IsMulCommutative D) {n p : ℕ} [Fact p.Prime]
    (hn : 1 < n) (hmodel : IsBinaryRankOne D n) (hp : 3 < p)
    (S : Sylow 2 J) (B : Subgroup J) (hB : IsPGroup p B) (hBD : B ≤ D)
    (hperm : (B : Set J) * (S : Set J) = (S : Set J) * (B : Set J)) :
    IsCyclic B := by
  let : D.Normal := hD ▸ Theory.GroupTheory.generalizedFitting_normal
  exact isCyclic_of_simple_normal D hna hn hmodel hp S B hB hBD hperm

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.RankOne
