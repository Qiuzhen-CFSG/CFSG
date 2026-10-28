module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.Support
public import Theory.GroupAction.NormalPChiefSeries.Linear
public import Theory.ElementaryAbelian.Injective

/-!
# A short subnormal group moves at most one chief interval

If a short subnormal group K moves a normal elementary subgroup A, then
[A,K] is its entire intrinsic block layer U(K). Every larger normal
elementary subgroup is therefore centralized modulo A. Applying this to
the upper term of the earlier of two chief intervals shows that K cannot
move both intervals. The intervals remain those of the original ambient
group; they need not be chief after restriction to K.

This uses the short-group commutator support theorem without assuming a
split central kernel or any bound on the order of the block. It supplies
the block exclusions in Aschbacher--Smith 15.2.8, printed pp.1109--1110,
from C.1.7--8 and C.1.27, printed pp.123 and 133.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC
open NoncentralChiefRefinement
variable {D : Type*} [Group D] [Finite D] {U : Subgroup D} [U.Normal]
  [IsElementaryAbelian 2 U]

omit [Finite D] in
private theorem factor_fixed_of_commutator_le (s : SeriesOn U) (K : Subgroup D)
    (i : Fin s.series.length) (hc : ⁅(s.upper i).val,K⁆ ≤ (s.lower i).val) :
    ∀ k : K, ∀ v, s.factorRepresentation i (k : D) v = v := by
  intro k v
  apply Additive.toMul.injective
  change s.action i (k : D) v.toMul = v.toMul
  obtain ⟨b,hb⟩ := QuotientGroup.mk'_surjective
    ((s.lower i).val.subgroupOf (s.upper i).val) v.toMul
  rw [←hb,s.action_mk]
  apply QuotientGroup.eq_iff_div_mem.mpr
  change (k : D) * (b : D) * (k : D)⁻¹ / (b : D) ∈ (s.lower i).val
  have hm := hc (show ⁅(k : D),(b : D)⁆ ∈ ⁅(s.upper i).val,K⁆ from by
    rw [commutator_comm]
    exact commutator_mem_commutator k.property b.property)
  simpa only [commutatorElement_def,div_eq_mul_inv] using hm

/-- A short subnormal group moves at most one original chief interval of a
normal elementary subgroup, including after restriction of its action. -/
theorem IsBlock.moved_factor_unique (K : Subgroup D) (hK : IsBlock K)
    (s : SeriesOn U) (i j : Fin s.series.length)
    (hi : ∃ k : K, ∃ v, s.factorRepresentation i (k : D) v ≠ v)
    (hj : ∃ k : K, ∃ v, s.factorRepresentation j (k : D) v ≠ v) : i = j := by
  have ordered (a b : Fin s.series.length) (hab : a < b)
      (ha : ∃ k : K, ∃ v, s.factorRepresentation a (k : D) v ≠ v)
      (hb : ∃ k : K, ∃ v, s.factorRepresentation b (k : D) v ≠ v) : False := by
    let A := (s.upper a).val
    let : A.Normal := (s.upper a).property
    let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_injective
      (inclusion (s.upper_le a)) (inclusion_injective _)
    have hne : ⁅A,K⁆ ≠ ⊥ := by
      intro he
      obtain ⟨k,v,hv⟩ := ha
      exact hv (factor_fixed_of_commutator_le s K a (he ▸ bot_le) k v)
    have he := RankOne.ChiProduct.SelectedRankOne.blockU_eq_nontrivial_normal_module_commutator
      K A hK hne
    have hfull : ⁅U,K⁆ ≤ A :=
      (commutator_le_core_commutator_of_isSubnormal K U hK.subnormal hK.short.twoPerfect
        (IsElementaryAbelian.isPGroup 2 U) le_normalizer_of_normal).trans
          (he.le.trans (commutator_le_left A K))
    have hab' : (s.upper a).val ≤ (s.lower b).val :=
      s.series.strictMono.monotone (show a.succ ≤ b.castSucc from by
        apply Fin.le_iff_val_le_val.mpr
        exact hab)
    obtain ⟨k,v,hv⟩ := hb
    exact hv (factor_fixed_of_commutator_le s K b
      ((commutator_mono (s.upper_le b) le_rfl).trans (hfull.trans hab')) k v)
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact ordered i j hlt hi hj
  · exact ordered j i hlt hj hi

end CFSG.Quasithin.ChapterC
