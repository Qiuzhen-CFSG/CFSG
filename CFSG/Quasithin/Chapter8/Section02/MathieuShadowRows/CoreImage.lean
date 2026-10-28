module
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.CodeRotation
public import CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Elementary
public import Theory.ElementaryAbelian.BinaryQuotientRank
public import Mathlib.GroupTheory.FixedPointFree
public import Theory.GroupTheory.TwoByThreeDisplacement

/-!
# Fixed-point-free core sections in the original code pair

Surjectivity of the commutator map for a fixed-point-free section
automorphism lifts through the literal kernel U. The actual cubic actor
on P/U will place P inside the original parabolic two-core. For a selected
degree-one pair this identifies the original intersection V ∩ O₂(H) and
proves that the image of V in H/O₂(H) has order two.

Source: Aschbacher--Smith 8.2.8(5) and 8.2.9(3), printed pp.719--720,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
open Normalizer.SmallOvergroups Offenders.Parabolic Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G]

theorem section_le_commutator_sup_of_fixedFree
    (K P U R : Subgroup G) [(U.subgroupOf P).Normal]
    (hKP : K ≤ normalizer (P : Set G)) (hKU : K ≤ normalizer (U : Set G))
    (z : K) (hz : z.val ∈ R)
    (hf : ∀ w, sectionAction K P U hKP hKU z w = w → w = 1) :
    P ≤ ⁅P,R⁆ ⊔ U := by
  let q := QuotientGroup.mk' (U.subgroupOf P)
  let α := (sectionAction K P U hKP hKU z).toMonoidHom
  have hfree : MonoidHom.FixedPointFree α := hf
  intro x hx
  let xP : P := ⟨x,hx⟩
  obtain ⟨y,hy⟩ := hfree.commutatorMap_surjective (q xP)
  obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (U.subgroupOf P) y
  let zb : P := P.normalizerMonoidHom (inclusion hKP z) b
  have hzq : α (q b) = q zb := rfl
  change q b / α (q b) = q xP at hy
  rw [hzq,←map_div] at hy
  let w := b / zb
  have hw : w.val ∈ ⁅P,R⁆ := by
    have he : w.val = ⁅b.val,z.val⁆ := by
      change b.val / (z.val * b.val * z.val⁻¹) = ⁅b.val,z.val⁆
      simp only [commutatorElement_def,div_eq_mul_inv,mul_inv_rev,inv_inv,mul_assoc]
    rw [he]
    exact commutator_mem_commutator b.property hz
  have hxw : x / w.val ∈ U := by
    have hh : xP / w ∈ q.ker := by
      change q (xP / w) = 1
      rw [map_div,hy,div_self']
    change xP / w ∈ (QuotientGroup.mk' (U.subgroupOf P)).ker at hh
    rw [QuotientGroup.ker_mk'] at hh
    exact hh
  have hh := (⁅P,R⁆ ⊔ U).mul_mem (mem_sup_right hxw) (mem_sup_left hw)
  simpa only [div_mul_cancel] using hh

/-- Core containment preserves the original pair intersection and gives the
literal order-two image of V in H/O₂(H). -/
theorem selected_one_image_two_of_core_le
    {V H M I : Subgroup G} {T : Sylow 2 G} [IsElementaryAbelian 2 V]
    {i : I} {S : Sylow 2 I} (s : Selected H T M V I 1 i S)
    (hc : I.pCoreIn 2 ≤ H.pCoreIn 2) :
    V ⊓ I.pCoreIn 2 = V ⊓ H.pCoreIn 2 ∧
      Nat.card ((V.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) = 2 := by
  have hVI : V ≤ I := s.generate ▸ le_sup_left
  have hIH := s.family.le_ambient
  have hVH := hVI.trans hIH
  have he : V ⊓ I.pCoreIn 2 = V ⊓ H.pCoreIn 2 := by
    apply le_antisymm (inf_le_inf_left V hc)
    exact le_inf inf_le_left ((le_inf inf_le_right (inf_le_left.trans hVI)).trans
      (pCoreIn_inf_le_of_normalizes (hIH.trans H.le_normalizer)))
  refine ⟨he,?_⟩
  have hi : (V ⊓ I.pCoreIn 2).relIndex V = 2 := by
    have hr := (quotient_rank_eq_core_corank I V hVI).symm.trans s.rank_eq
    change Nat.log 2 ((V ⊓ I.pCoreIn 2).relIndex V) = 1 at hr
    rw [log_relIndex_eq_quotient_finrank] at hr
    rw [relIndex_eq_two_pow_quotient_finrank,hr,pow_one]
  rw [←relIndex_ker,QuotientGroup.ker_mk']
  have hmap := relIndex_map_map_of_injective (pCore 2 H) (V.subgroupOf H)
    H.subtype_injective
  rw [map_subgroupOf_eq_of_le hVH] at hmap
  rw [←hmap,←inf_relIndex_left]
  change (V ⊓ H.pCoreIn 2).relIndex V = 2
  rwa [←he]

end CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
