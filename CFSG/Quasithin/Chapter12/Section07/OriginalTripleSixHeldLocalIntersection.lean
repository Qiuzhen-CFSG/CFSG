module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldComponentNormalizer
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointOrdinaryBlockCore
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# The actual overlap of the two original Held local groups

The literal U-normalizer inside B is Lt, while its full ambient normalizer
is M. Hence B meets M, and also K, exactly in Lt. Since the original scalar
residual X lies in K and normalizes B, the projective extension B X meets
both M and K exactly in Lt X. No Sylow comparison or affine actor choice
is required for these equalities.

Source: Aschbacher--Smith12.7.7, original local configuration on p.841.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The same original residual and scalar residual give the exact common
subgroup on both sides of the source projective extension. -/
theorem original_tripleSix_held_local_intersections
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (hB : let H := centralizer ({(t : G)} : Set G)
      let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
      IsComponent H ((conjugateSpanBy Lt H).subgroupOf H))
    (hcenter :
      let Lt := (pResidual 2 (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G)).map
        (K ⊓ centralizer ({(t : G)} : Set G)).subtype
      centerIn (conjugateSpanBy Lt (centralizer ({(t : G)} : Set G))) = tripleSixPoint D a t)
    (e :
      let Lt := (pResidual 2 (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G)).map
        (K ⊓ centralizer ({(t : G)} : Set G)).subtype
      let B := conjugateSpanBy Lt (centralizer ({(t : G)} : Set G))
      B ⧸ center B ≃* Matrix.PSL3Four.PSL) :
    let H := centralizer ({(t : G)} : Set G)
    let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
    let B := conjugateSpanBy Lt H
    let X := tripleSixScalarResidual K
    let M := normalizer (K : Set G)
    B ⊓ M = Lt ∧ B ⊓ K = Lt ∧
      (B ⊔ X) ⊓ M = Lt ⊔ X ∧ (B ⊔ X) ⊓ K = Lt ⊔ X := by
  let H := centralizer ({(t : G)} : Set G)
  let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
  let B := conjugateSpanBy Lt H
  let X := tripleSixScalarResidual K
  let M := normalizer (K : Set G)
  have hLK : Lt ≤ K := (map_subtype_le _).trans inf_le_left
  have hLB : Lt ≤ B := le_conjugateSpanBy Lt H
  have hUB : U ≤ B :=
    (tripleSixPointCentralizerResidual_commutator D a t ht heven).2.trans hLB
  obtain ⟨hLt,_,_⟩ := tripleSixPointResidual_ordinary_block_core D a t ht heven hcenter e
  obtain ⟨_,_,_,hUM,_⟩ := original_tripleSix_held_core_recovery
    h structural D a t ht heven hB hcenter e
  change Lt = (normalizer (U.subgroupOf B : Set B)).map B.subtype at hLt
  have hBM : B ⊓ M = Lt := by
    rw [hLt,←subgroupOf_normalizer_eq hUB,subgroupOf_map_subtype, hUM,inf_comm]
  have hBK : B ⊓ K = Lt := le_antisymm
    ((inf_le_inf_left B K.le_normalizer).trans_eq hBM) (le_inf hLB hLK)
  obtain ⟨_,_,_,hXN⟩ := original_tripleSix_held_component_normalizer
    h structural D a t ht heven hB hcenter e
  have hXK : X ≤ K := map_subtype_le _
  have overlap (N : Subgroup G) (hXN' : X ≤ N) (hBN : B ⊓ N = Lt) :
      (B ⊔ X) ⊓ N = Lt ⊔ X := by
    apply le_antisymm
    · rintro g ⟨hg,hgN⟩
      have hprod : g ∈ (B : Set G) * (X : Set G) := by
        rw [←coe_mul_of_right_le_normalizer_left B X hXN]
        exact hg
      obtain ⟨b,hb,x,hx,hbx⟩ := hprod
      have hbN : b ∈ N := by
        have hm := N.mul_mem hgN (N.inv_mem (hXN' hx))
        rw [←hbx,mul_inv_cancel_right] at hm
        exact hm
      have hbL : b ∈ Lt := hBN ▸ (show b ∈ B ⊓ N from ⟨hb,hbN⟩)
      rw [←hbx]
      exact (Lt ⊔ X).mul_mem ((show Lt ≤ Lt ⊔ X from le_sup_left) hbL) ((show X ≤ Lt ⊔ X from le_sup_right) hx)
    · apply sup_le
      · exact le_inf (hLB.trans le_sup_left) (hBN.symm ▸ inf_le_right)
      · exact le_inf le_sup_right hXN'
  exact ⟨hBM,hBK,overlap M (hXK.trans K.le_normalizer) hBM,overlap K hXK hBK⟩

end CFSG.Quasithin.Chapter12.Section07
