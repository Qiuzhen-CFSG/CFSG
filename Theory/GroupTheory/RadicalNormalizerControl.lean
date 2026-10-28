module

public import Theory.PGroupCore
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Control of p-subgroups by a radical subgroup

If a finite p-subgroup R contains the p-core of its normalizer, every
p-subgroup normalized by that normalizer lies in R. In particular the
ambient p-core lies in R. This includes the usual case R = O_p(N_G(R)).

Intersect the other p-subgroup S with N_G(R). This is a normal p-subgroup
of the normalizer, hence lies in R. The product RS is a p-group in which
R is self-normalizing, so the nilpotent normalizer condition gives RS = R.

Source: Aschbacher--Smith, The Classification of Quasithin Groups,
combined manuscript (1 March 2004), Lemma C.2.1, printed p.144.
The same normalizer argument for the ambient p-core is used in
`Theory.GroupTheory.AbelianNormalizerCore`.
-/

open scoped Pointwise

namespace Subgroup

/-- A p-subgroup normalized by the normalizer of a radical p-subgroup
is contained in that radical subgroup. The hypothesis only needs one
inclusion in the radical equality. -/
public theorem le_of_normalizer_le_normalizer_of_pCore_normalizer_le {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (R S : Subgroup G) (hR : IsPGroup p R) (hS : IsPGroup p S)
    (hrad : (pCore p (normalizer (R : Set G))).map
      (normalizer (R : Set G)).subtype ≤ R)
    (hSN : normalizer (R : Set G) ≤ normalizer (S : Set G)) : S ≤ R := by
  let N := normalizer (R : Set G)
  have hSNnormal : (S.subgroupOf N).Normal :=
    normal_subgroupOf_of_le_normalizer hSN
  have hSNcore : S.subgroupOf N ≤ pCore p N :=
    le_sSup ⟨hSNnormal, hS.comap_subtype⟩
  have hSNle : S ⊓ N ≤ R := by
    intro s hs
    exact hrad (mem_map_of_mem N.subtype
      (hSNcore (show (⟨s, hs.2⟩ : N) ∈ S.subgroupOf N from hs.1)))
  have hRS : R ≤ normalizer (S : Set G) := le_normalizer.trans hSN
  let J := R ⊔ S
  have hJ : IsPGroup p J := hR.to_sup_of_normal_right' hS hRS
  let _ : Group.IsNilpotent J := hJ.isNilpotent
  have hself : normalizer (R.subgroupOf J : Set J) = R.subgroupOf J := by
    apply le_antisymm ?_ le_normalizer
    intro x hx
    have hxN : (x : G) ∈ N := by
      rw [← subgroupOf_normalizer_eq (show R ≤ J from le_sup_left)] at hx
      exact hx
    have hxprod : (x : G) ∈ (R : Set G) * (S : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right R S hRS]
      exact x.property
    obtain ⟨r, hr, s, hs, hrs⟩ := hxprod
    change r * s = (x : G) at hrs
    have hsN : s ∈ N := by
      have hrsN : r * s ∈ N := hrs.symm ▸ hxN
      simpa only [← mul_assoc, inv_mul_cancel, one_mul] using
        N.mul_mem (N.inv_mem (le_normalizer hr)) hrsN
    change (x : G) ∈ R
    exact hrs ▸ R.mul_mem hr (hSNle ⟨hs, hsN⟩)
  have htop : R.subgroupOf J = ⊤ :=
    (normalizerCondition_iff_only_full_group_self_normalizing.mp
      (Group.normalizerCondition_of_isNilpotent (G := J))) _ hself
  exact le_sup_right.trans (subgroupOf_eq_top.mp htop)


/-- Every radical p-subgroup contains the ambient p-core. -/
public theorem pCore_le_of_pCore_normalizer_le
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (R : Subgroup G) (hR : IsPGroup p R)
    (hrad : (pCore p (normalizer (R : Set G))).map
      (normalizer (R : Set G)).subtype ≤ R) : pCore p G ≤ R :=
  le_of_normalizer_le_normalizer_of_pCore_normalizer_le R (pCore p G)
    hR pCore_isPGroup hrad le_normalizer_of_normal

end Subgroup
