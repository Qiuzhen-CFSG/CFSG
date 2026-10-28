module

public import Theory.SpecificGroups.G2Even.TwoRank.UnipotentBound
public import Theory.AtlasPort.LinearGroups.G2.LieParabolicSetup
public import Theory.AtlasPort.LinearGroups.G2.Perfectness
public import Theory.GroupTheory.PrimeRankSylow

/-!
# Two-rank of the actual even-field G₂ model

The three commuting root groups attain the bound q³ proved from the six-root
Sylow coordinates. Thus G₂(2ⁿ) has two-rank 3n. Over fields of order greater
than two, the existing torus-commutator perfectness theorem identifies its
genuine derived subgroup with the whole octonion model.

No automorphism-rank bound is asserted here. In particular, the full group
at q=2 is not identified with its proper derived subgroup.

Source: Aschbacher–Smith, rank table on printed p.356, field pairs in
16.1.7(3a), p.1172, and rank inspection in 16.3.9, p.1180.
-/

public section

namespace Atlas.G2.EvenTwoRank
open Theory.GroupTheory
variable (F : Type*) [Field F] [Finite F]

/-- Exact two-rank of the full octonion automorphism model. This calculation
also holds at q=2, where the full model is not perfect. -/
theorem two_rank {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    primeRank 2 (Model F) = 3 * n := by
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  apply le_antisymm
  · rw [(LieParabolicSetup.sylow (F := F)).primeRank_eq]
    change primeRank 2 (unipotent (K := F)) ≤ _
    apply (primeRank_le_iff_elementary_card_le _).mpr
    intro A hA
    have h := unipotent_elementary_card_le A hA
    simpa only [hF, ← pow_mul, Nat.mul_comm n 3] using h
  · exact rank_ge F hF

/-- Perfectness supplies a genuine equivalence from the derived subgroup,
without replacing the derived group by a family label. -/
noncomputable def derivedEquiv (hq : 2 < Nat.card F) :
    commutator (Model F) ≃* Model F := by
  let : Group.IsPerfect (Model F) := isPerfect hq
  exact (MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top).trans Subgroup.topEquiv

omit [Field F] [Finite F] in
private theorem card_gt_two {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    2 < Nat.card F := by
  rw [hF]
  have h := Nat.pow_le_pow_right (by decide : 0 < 2) hn
  norm_num at h
  omega

/-- Exact two-rank of the genuine derived group at the ordinary endpoints. -/
theorem derived_two_rank {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    primeRank 2 (commutator (Model F)) = 3 * n := by
  rw [primeRank_equiv 2 (derivedEquiv F (card_gt_two F hn hF))]
  exact two_rank F hF

/-- Transport of the entire automorphism group through the proved
identification of the derived and full models. -/
noncomputable def derivedAutEquiv {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    MulAut (commutator (Model F)) ≃* MulAut (Model F) :=
  MulAut.congr (derivedEquiv F (card_gt_two F hn hF))

end Atlas.G2.EvenTwoRank
