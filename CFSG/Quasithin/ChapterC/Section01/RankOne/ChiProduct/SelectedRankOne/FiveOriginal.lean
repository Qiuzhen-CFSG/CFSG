module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.FiveSource
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.ControlSource
/-!
# The original B.6.9 symmetric-five section gives the C.1.26 block

The existing B-layer marker supplies the actual covered action on the
original moved subgroup. Apply the proved C.1.23 source and recover support
in the original module by residual idempotence. For the canonical omega
span, characteristic two and proper control also supply reducedness and
Thompson movement; neither remains an additional source input.

Source: Aschbacher–Smith C.1.26, p.132, with B.6.9.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB Chapter1.Section02 QuasisimpleSource
universe u v
variable {G : Type u} {H : Type v} [Group G] [Finite G] [Group H] [Finite H]
attribute [local instance] RankOneBaumann.semilinear_moved_elementary

theorem quasisimple_five_outside_moved_chi_of_section
    {C : GroupClass.{u}} (h36 : A36Input C) (hG : IsSQTK C G)
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
  obtain ⟨ho,hb,hmove,hs,_⟩ := covered_five_outside_moved_chi h36 hG T hP W (hU.moved U)
    hJW p hp hk f hf he hfix hfit M hcpu hM
  have hi : ⁅W,pResidual 2 G⁆ = W := commutator_isPPerfect_idempotent (pResidual 2 G) U
    (isPPerfect_pResidual 2) (IsElementaryAbelian.isPGroup 2 U) le_normalizer_of_normal
  exact ⟨ho,hb,hmove,hs.trans hi⟩

theorem quasisimple_five_outside_of_control
    {C : GroupClass.{u}} (h36 : A36Input C) (hG : IsSQTK C G)
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
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
    (hspan : U = normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hfit : generalizedFitting G = pCore 2 G)
    (M : Subgroup G) (hcpu : (T : Subgroup G).characteristicNormalizerClosure ≤ M) (hM : M ≠ ⊤) :
    ¬ pResidual 2 G ≤ M ∧ IsChiBlockIn (pResidual 2 G) ∧
      pResidual 2 G = ⁅pResidual 2 G,elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
      (blockU (pResidual 2 G)).map (pResidual 2 G).subtype = ⁅U,pResidual 2 G⁆ := by
  have hTne : (T : Subgroup G) ≠ ⊥ := by
    intro hz
    apply hP.2
    rw [hz]
    exact le_normalizer_of_normal
  have hU : IsPReduced 2 U := hspan ▸ omegaCenter_normalClosure_reduced T
    ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hfit)
  have hJ := thompson_moves_omega_closure_of_control T hTne U hspan M hcpu hM
  exact quasisimple_five_outside_moved_chi_of_section h36 hG T hP U hU hJ q hq hker
    hqs s e hfit M hcpu hM
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
