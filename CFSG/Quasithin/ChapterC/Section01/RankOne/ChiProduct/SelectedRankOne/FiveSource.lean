module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.FiveComponent
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.QuasisimpleFiveMarker
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.FivePairControl
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.UniformPair
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.FiveBlockSource.SylowMarking
/-!
# The covered symmetric-five branch of C.1.26

The original minimal-parabolic action selects the actual residual A₅
component. The uniform C.1.18 pair then enters the proved C.1.23 source
on that same component and covered module. Characteristic-normalizer
control excludes the central and normal pair alternatives, leaving the
actual outside A₅ block with original Thompson movement and support.

Source: Aschbacher–Smith C.1.23 and C.1.26, pp.129–130,132.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB Chapter1.Section02 GlaubermanNiles FiveBlockSource
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The actual covered S₅ action produces the outside moved A₅ block. -/
theorem covered_five_outside_moved_chi
    {C : GroupClass.{u}} (h36 : A36Input C) (hG : IsSQTK C G)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* Equiv.Perm (Fin 5)) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set G))
    (p : Additive U →ₗ[ZMod 2] BinaryPermutation.core (Fin 5)) (hp : Function.Surjective p)
    (he : ∀ g v, p (NormalElementaryQuotient.representation U q hq hk g v) =
      BinaryPermutation.coreRepresentation (Fin 5) g (p v))
    (hfix : ∀ v, p v = 0 → ∀ g ∈ alternatingGroup (Fin 5),
      NormalElementaryQuotient.representation U q hq hk g v = v)
    (hfit : generalizedFitting G = pCore 2 G)
    (M : Subgroup G) (hcpu : (T : Subgroup G).characteristicNormalizerClosure ≤ M) (hM : M ≠ ⊤) :
    ¬ pResidual 2 G ≤ M ∧ IsChiBlockIn (pResidual 2 G) ∧
      pResidual 2 G = ⁅pResidual 2 G,elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
      (blockU (pResidual 2 G)).map (pResidual 2 G).subtype = ⁅U,pResidual 2 G⁆ ∧
      (blockU (pResidual 2 G)).map (pResidual 2 G).subtype ≤ U := by
  have hTne : (T : Subgroup G) ≠ ⊥ := by
    intro hz
    apply hP.2
    rw [hz]
    exact le_normalizer_of_normal
  have hTM : (T : Subgroup G) ≤ M := T.toSubgroup.le_normalizer.trans
    ((normalizer_le_characteristicNormalizerClosure_self (T : Subgroup G) hTne).trans hcpu)
  have hout : ¬ pResidual 2 G ≤ M := by
    intro hx
    exact hM (top_unique ((pResidual_sup_sylow_eq_top T).symm.le.trans (sup_le hx hTM)))
  obtain ⟨D,hD⟩ := exists_baumann_universal_pair.{u,u} (T : Subgroup G) T.isPGroup' hTne
  obtain ⟨hc,⟨eL⟩⟩ := symmetric_five_residual_component h36 hG T hP U hU hJ q hq hk
  have him : (pResidual 2 G).map q = alternatingGroup (Fin 5) := by
    rw [map_pResidual_of_surjective 2 q hq,Equiv.Perm.twoResidual_eq_alternating]
  have h := source_conclusion T hfit (pResidual 2 G) hc (pResidual_sup_sylow_eq_top T)
    eL U q hq hk him p hp he hfix hJ D hD (firstAmbient (T : Subgroup G) D)
      inf_le_left inf_le_right
  rcases h with hc | hn | ⟨hb,ha,hm,hs,hU'⟩
  · have hnorm : normalizer (firstAmbient (T : Subgroup G) D : Set G) = ⊤ := by
      let : (firstAmbient (T : Subgroup G) D).Normal := ⟨fun x hx g => by
        rw [mem_center_iff.mp (hc hx) g,mul_inv_cancel_right]
        exact hx⟩
      exact normalizer_eq_top _
    have hh := (firstAmbient_normalizer_le_control (T : Subgroup G) T.isPGroup' D).trans hcpu
    rw [hnorm] at hh
    exact (hM (top_unique hh)).elim
  · let := D.second_characteristic
    let : (D.second.map (baumann (T : Subgroup G)).subtype).Normal := hn
    have hh := (characteristic_baumann_normalizer_le_control (T : Subgroup G)
      D.second D.second_ne_bot).trans hcpu
    rw [normalizer_eq_top] at hh
    exact (hM (top_unique hh)).elim
  · exact ⟨hout,⟨hb,Or.inr ⟨5,by decide,ha⟩⟩,hm,hs,hU'⟩
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
