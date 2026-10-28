module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.FiveSource
/-!
# The covered five-point branch with its given residual component

The actual residual C-component and its A₅ quotient replace the universal
component classification premise. Apply C.1.23 to the genuine covered natural
projection and the uniform characteristic pair. Proper characteristic-normalizer
control excludes the central and normal alternatives, leaving the short block.
The second theorem obtains that projection from the original B.6.9 moved section.
Source: Aschbacher–Smith C.1.23 and C.1.26, pp.130,132.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.FivePointCharacteristic
open ChapterB Chapter1.Section02 GlaubermanNiles FiveBlockSource ChapterB.QuasisimpleSource
open ChiProduct.SelectedRankOne
universe u v
variable {G : Type u} [Group G] [Finite G]
attribute [local instance] RankOneBaumann.semilinear_moved_elementary
theorem covered_five_of_residual
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* Equiv.Perm (Fin 5)) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set G))
    (p : Additive U →ₗ[ZMod 2] BinaryPermutation.core (Fin 5)) (hp : Function.Surjective p)
    (he : ∀ g v, p (NormalElementaryQuotient.representation U q hq hk g v) =
      BinaryPermutation.coreRepresentation (Fin 5) g (p v))
    (hfix : ∀ v, p v = 0 → ∀ g ∈ alternatingGroup (Fin 5),
      NormalElementaryQuotient.representation U q hq hk g v = v)
    (hfit : generalizedFitting G = pCore 2 G)
    (hc : (pResidual 2 G).IsCComponent)
    (eL : ((pResidual 2 G) ⧸ pCore 2 (pResidual 2 G)) ≃* alternatingGroup (Fin 5))
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
variable {H : Type v} [Group H] [Finite H]
theorem five_marked_residual
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (hqs : IsQuasisimple (generalizedFitting
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker))))
    (s : MovedSection ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype)
      (generalizedFitting (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker))))
    (e : MarkedActionEquiv s.action (offenderSubgroup s.action)
      (generalizedFitting (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)))
      (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5)))
    (hfit : generalizedFitting G = pCore 2 G)
    (hc : (pResidual 2 G).IsCComponent)
    (eL : ((pResidual 2 G) ⧸ pCore 2 (pResidual 2 G)) ≃* alternatingGroup (Fin 5))
    (M : Subgroup G) (hcpu : (T : Subgroup G).characteristicNormalizerClosure ≤ M) (hM : M ≠ ⊤) :
    ¬ pResidual 2 G ≤ M ∧ IsChiBlockIn (pResidual 2 G) ∧
      pResidual 2 G = ⁅pResidual 2 G,elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
      (blockU (pResidual 2 G)).map (pResidual 2 G).subtype = ⁅U,pResidual 2 G⁆ := by
  let W := ⁅U,pResidual 2 G⁆
  have hJW : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G) :=
    fun h => hJ (h.trans_eq (hU.centralizer_moved_eq U))
  obtain ⟨p,hp,hk,f,hf,he,hfk⟩ := ChapterB.quasisimple_five_source_marker
    T hP U hU hJ q hq hker hqs s e
  have hm : (pResidual 2 G).map p = alternatingGroup (Fin 5) := by
    rw [map_pResidual_of_surjective 2 p hp,Equiv.Perm.twoResidual_eq_alternating]
  have hfix : ∀ v, f v = 0 → ∀ g ∈ alternatingGroup (Fin 5),
      NormalElementaryQuotient.representation W p hp hk g v = v := by
    intro v hv g hg
    have hh : v ∈ fixedSpace (NormalElementaryQuotient.representation W p hp hk)
        ((pResidual 2 G).map p) := hfk ▸ hv
    exact hh ⟨g,hm.symm ▸ hg⟩
  obtain ⟨ho,hb,hmove,hs,_⟩ := covered_five_of_residual T hP W
    hJW p hp hk f hf he hfix hfit hc eL M hcpu hM
  have hi : ⁅W,pResidual 2 G⁆ = W := commutator_isPPerfect_idempotent (pResidual 2 G) U
    (isPPerfect_pResidual 2) (IsElementaryAbelian.isPGroup 2 U) le_normalizer_of_normal
  exact ⟨ho,hb,hmove,hs.trans hi⟩

end CFSG.Quasithin.ChapterC.RankOne.FivePointCharacteristic
