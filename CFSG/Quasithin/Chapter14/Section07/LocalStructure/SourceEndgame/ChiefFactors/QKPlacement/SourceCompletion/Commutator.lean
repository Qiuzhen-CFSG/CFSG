module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.QKPlacement.SourceCompletion.Root
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.SourceGeneration.Algebra

/-!
# The actual commutator containment in14.7.71(3)

The marked root equality gives Q≤SQ_H. Modulo S, its L₁-commutator
therefore lies in Q_K∩Q, hence in C_H(U)S by the proved reverse product.
The already proved centralizer step makes the second L₁-commutator lie
in S. Two-perfect commutator idempotence removes the second commutator,
and normal generation by L₁ propagates the bound to L. This retains the
original subgroups and avoids a separate global chief-series restriction.

Source: Aschbacher–Smith,14.7.71(3),printed p.1075.
-/

public section
noncomputable section
open Subgroup Representation
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.QKPlacement.SourceCompletion
open Chapter12.Section08 CriticalFusion.Source SteinbergRecognition
open CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)
  (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
  (c : CriticalPath (L := L) F) (e : Earlier d c) (mark : UpperMarking d)
include d structural c e mark

private theorem Q_le_span_sup_core : Q T L ≤ S F L ⊔ F.H.pCoreIn 2 := by
  have hQ : ((Q T L).subgroupOf F.H).map d.qH =
      ((S F L).subgroupOf F.H).map d.qH := by
    have hr : ((S F L).subgroupOf F.H).map d.qH =
        Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements.root d.naturalQuotient :=
      root_image d structural c e mark
    rw [hr]
    have hm (A : Subgroup G) : (star F A).map d.model.toMonoidHom =
        (A.subgroupOf F.H).map d.qH := by
      rw [CriticalFusion.Source.star, map_map]
      rfl
    rw [← hm, e.images.image_eq, hm]
    exact mark
  intro q hq
  let qH : F.H := ⟨q, Q_le_H F hq⟩
  have hm : d.qH qH ∈ ((S F L).subgroupOf F.H).map d.qH :=
    hQ ▸ mem_map_of_mem d.qH hq
  obtain ⟨s, hs, he⟩ := hm
  have hk : (s⁻¹ * qH : F.H) ∈ d.qH.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, he, inv_mul_cancel]
  rw [d.qH_ker] at hk
  have hp := (S F L ⊔ F.H.pCoreIn 2).mul_mem (mem_sup_left hs)
    (mem_sup_right hk)
  change (s : G) * ((s : G)⁻¹ * q) ∈ S F L ⊔ F.H.pCoreIn 2 at hp
  simpa only [mul_inv_cancel_left] using hp

/-- The source product and actual root image force the full original Q-L bound. -/
theorem commutator_Q_L_le_S (b : QKDualCoordinates d) : ⁅Q T L,L⁆ ≤ S F L := by
  have hSQ := S_le_Q d structural e.separation
  have hQT : Q T L ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)).trans_eq
      (map_subgroupOf_eq_of_le le_sup_right)
  have hQHT : F.H.pCoreIn 2 ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow F.H (T.subtype (F.invariant 1))).trans_eq
      (map_subgroupOf_eq_of_le (F.invariant 1))
  have hTN : (T : Subgroup G) ≤ normalizer (S F L : Set G) :=
    T_normalizes_S d (d.natural.sylow_normalizes structural)
  have hTSQK : (T : Subgroup G) ≤ normalizer ((S F L ⊔ QK F : Subgroup G) : Set G) :=
    (le_inf hTN ((F.invariant 1).trans b.qSection.normalized)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hL₁N : F.Li L 1 ≤ normalizer (S F L : Set G) :=
    ((F.Li_le L 1).trans inf_le_left).trans L_normalizes_S
  have hfirst : ⁅Q T L,F.Li L 1⁆ ≤ S F L ⊔ QK F := by
    let P := commutatorPreimage (T : Subgroup G) (F.Li L 1) (S F L ⊔ QK F)
    have hsP : S F L ≤ P := le_commutatorPreimage (hSQ.trans hQT)
      ((le_normalizer_iff_commutator_le_left.mp hL₁N).trans le_sup_left)
    have hqP : F.H.pCoreIn 2 ≤ P := le_commutatorPreimage hQHT
      ((commutator_mono le_rfl L₁_le_K).trans (le_sup_left.trans le_sup_right))
    have hQP : Q T L ≤ P := (Q_le_span_sup_core d structural c e mark).trans (sup_le hsP hqP)
    exact (commutator_mono hQP le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ hTSQK)
  have hLQ : L ≤ normalizer (Q T L : Set G) :=
    le_sup_left.trans ((L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hinQ : ⁅Q T L,F.Li L 1⁆ ≤ Q T L :=
    le_normalizer_iff_commutator_le_left.mp (((F.Li_le L 1).trans inf_le_left).trans hLQ)
  have hfirstC : ⁅Q T L,F.Li L 1⁆ ≤ S F L ⊔ C F := by
    intro x hx
    have hm : x ∈ ((S F L : Set G) * (QK F : Set G)) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _
        (((QK_le_QH d e.sectionCentralizer).trans hQHT).trans hTN)]
      exact hfirst hx
    obtain ⟨s, hs, q, hq, he⟩ := hm
    have hqQ : q ∈ Q T L := by
      have hh := (Q T L).mul_mem ((Q T L).inv_mem (hSQ hs)) (hinQ hx)
      rw [← he, inv_mul_cancel_left] at hh
      exact hh
    have hp : q ∈ (S F L ⊓ QK F) ⊔ C F :=
      (reverse_product d structural c e mark b) ▸ (show q ∈ QK F ⊓ Q T L from ⟨hq,hqQ⟩)
    exact he ▸ mul_mem (mem_sup_left hs)
      ((show (S F L ⊓ QK F) ⊔ C F ≤ S F L ⊔ C F from sup_le_sup inf_le_left le_rfl) hp)
  have hsecond : ⁅S F L ⊔ C F,F.Li L 1⁆ ≤ S F L := by
    let P := commutatorPreimage (T : Subgroup G) (F.Li L 1) (S F L)
    have hsP : S F L ≤ P := le_commutatorPreimage (hSQ.trans hQT)
      (le_normalizer_iff_commutator_le_left.mp hL₁N)
    have hcP : C F ≤ P := le_commutatorPreimage ((C_le_QH d e.sectionCentralizer).trans hQHT)
      (by rw [commutator_comm]; exact ((commutator_mono L₁_le_K le_rfl).trans
        (centralizer_commutator d c e)).trans U_le_S)
    exact (commutator_mono (sup_le hsP hcP) le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ hTN)
  have hperfect : IsPPerfect 2 (F.Li L 1) := by
    change IsPPerfect 2 ((pResidual 2 (L ⊓ F.Gi 1 : Subgroup G)).map (L ⊓ F.Gi 1).subtype)
    exact isPPerfect_embedded_pResidual 2 (L ⊓ F.Gi 1)
  have hidem := commutator_isPPerfect_idempotent (F.Li L 1) (Q T L) hperfect
    (isPGroup_pCoreIn 2 _) (((F.Li_le L 1).trans inf_le_left).trans hLQ)
  have hpoint : ⁅Q T L,F.Li L 1⁆ ≤ S F L :=
    hidem.symm.le.trans ((commutator_mono hfirstC le_rfl).trans hsecond)
  let P := commutatorPreimage L (Q T L) (S F L)
  have hLP : L ≤ normalizer (P : Set G) :=
    commutatorPreimage_normalized _ _ _ _ L_normalizes_S L.le_normalizer hLQ L_normalizes_S
  have h₁P : F.Li L 1 ≤ P := le_commutatorPreimage ((F.Li_le L 1).trans inf_le_left)
    (by rwa [commutator_comm])
  have hle : L ≤ P := (SourceGeneration.point_residual_normal_span d).symm.le.trans
    (conjugateSpanBy_le h₁P hLP)
  rw [commutator_comm]
  exact (commutator_mono hle le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ L_normalizes_S)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.QKPlacement.SourceCompletion
