module

public import Theory.GroupTheory.SolvableRadical
public import Theory.PGroupCore
public import Mathlib.GroupTheory.Rank

/-!
# Kernels in a radical with normal Sylow subgroup

If a normal subgroup has a normal Sylow p-subgroup, each of its p-subgroups
lies in the ambient p-core. Consequently a p-subgroup has the same kernel
modulo the solvable radical and modulo the p-core whenever the radical has
a normal Sylow p-subgroup. The two actual quotient images are isomorphic.

This is the elementary kernel comparison used in Aschbacher--Smith,
E.1.2(E2) and E.1.5, printed p.210. It does not assert a rank bound or any
local subgroup classification.
-/

public section

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Normal Sylow subgroups of normal subgroups contain all the relevant
p-subgroups and lie in the ambient p-core. -/
theorem le_pCore_of_normalSylow {p : ℕ} [Fact p.Prime]
    {N P : Subgroup G} [N.Normal]
    (hN : ∃ S : Sylow p N, (S : Subgroup N).Normal)
    (hP : IsPGroup p P) (hPN : P ≤ N) : P ≤ pCore p G := by
  obtain ⟨S, hS⟩ := hN
  let _ : (S : Subgroup N).Characteristic := S.characteristic_of_normal hS
  have hsn : ((S : Subgroup N).map N.subtype).Normal := inferInstance
  have hle : P.subgroupOf N ≤ (S : Subgroup N) := by
    let _ := hS
    have hpg := hP.comap_of_injective N.subtype N.subtype_injective
    obtain ⟨U, hU⟩ := hpg.exists_le_sylow
    have hSU : S = U := by
      apply Sylow.ext
      exact (S.is_maximal' U.isPGroup' (S.isPGroup'.le_sylow_of_normal U)).symm
    simpa only [hSU, subgroupOf] using hU
  calc
    P = (P.subgroupOf N).map N.subtype := (map_subgroupOf_eq_of_le hPN).symm
    _ ≤ (S : Subgroup N).map N.subtype := map_mono hle
    _ ≤ pCore p G := le_sSup ⟨hsn, S.isPGroup'.map N.subtype⟩

/-- The radical and p-core cut out the same kernel on every p-subgroup. -/
theorem inf_solvableRadical_eq_inf_pCore {p : ℕ} [Fact p.Prime]
    (A : Subgroup G) (hA : IsPGroup p A)
    (hR : ∃ S : Sylow p (solvableRadical G),
      (S : Subgroup (solvableRadical G)).Normal) :
    A ⊓ solvableRadical G = A ⊓ pCore p G := by
  apply le_antisymm
  · exact le_inf inf_le_left (le_pCore_of_normalSylow hR hA.to_inf_left inf_le_right)
  · have hcore : pCore p G ≤ solvableRadical G := by
      let _ := (pCore_isPGroup (p := p) (G := G)).isNilpotent
      exact le_solvableRadical _ inferInstance inferInstance
    exact inf_le_inf_left A hcore

omit [Finite G] in
/-- Equal intersections give an isomorphism of the actual quotient images,
through the two first-isomorphism-theorem maps from A. -/
noncomputable def quotientImageEquivOfInfEq (A N R : Subgroup G)
    [N.Normal] [R.Normal] (h : A ⊓ N = A ⊓ R) :
    A.map (QuotientGroup.mk' N) ≃* A.map (QuotientGroup.mk' R) := by
  let f := (QuotientGroup.mk' N).comp A.subtype
  let g := (QuotientGroup.mk' R).comp A.subtype
  have hk : f.ker = g.ker := by
    ext x
    change (QuotientGroup.mk' N) x.val = 1 ↔ (QuotientGroup.mk' R) x.val = 1
    have hx := SetLike.ext_iff.mp h x.val
    have hm : x.val ∈ N ↔ x.val ∈ R := by
      simpa only [mem_inf, x.property, true_and] using hx
    exact (QuotientGroup.eq_one_iff x.val).trans
      (hm.trans (QuotientGroup.eq_one_iff x.val).symm)
  have hf : f.range = A.map (QuotientGroup.mk' N) := by
    rw [MonoidHom.range_comp, range_subtype]
  have hg : g.range = A.map (QuotientGroup.mk' R) := by
    rw [MonoidHom.range_comp, range_subtype]
  exact (MulEquiv.subgroupCongr hf).symm.trans
    ((QuotientGroup.quotientKerEquivRange f).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hk).trans
        ((QuotientGroup.quotientKerEquivRange g).trans (MulEquiv.subgroupCongr hg))))

/-- Generator ranks agree for these literal quotient images. -/
theorem rank_quotientImage_eq_of_inf_eq (A N R : Subgroup G)
    [N.Normal] [R.Normal] (h : A ⊓ N = A ⊓ R) :
    Group.rank (A.map (QuotientGroup.mk' N)) =
      Group.rank (A.map (QuotientGroup.mk' R)) :=
  Group.rank_congr (quotientImageEquivOfInfEq A N R h)

end Subgroup
