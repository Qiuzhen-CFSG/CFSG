module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.UniformSource
public import Theory.GroupTheory.ElementaryThompsonFrattini
public import Theory.GroupTheory.ReducedNormal.SylowCenterClosure
/-!
# Thompson movement forced by characteristic-normalizer control

For the canonical orbit of the Sylow omega-center, Thompson centralization
would factor the group as the normalizer of J(T) times the module centralizer.
Both factors lie in characteristic-normalizer control. A proper control
overgroup therefore forces genuine Thompson movement. Characteristic two
also proves reducedness of the same canonical module. Applying these facts
to the actual B.6.9 section removes the local reducedness and movement inputs.

Source: Aschbacher–Smith B.2.14–15 and C.1.26–28, pp.78,132–133.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB GlaubermanNiles ChapterB.QuasisimpleSource ChapterB.SourceInduction
universe u v
variable {G : Type u} [Group G] [Finite G]
attribute [local instance] RankOneBaumann.semilinear_moved_elementary

theorem thompson_moves_omega_closure_of_control (T : Sylow 2 G)
    (hT : (T : Subgroup G) ≠ ⊥) (U : Subgroup G) [U.Normal]
    (hspan : U = normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (M : Subgroup G) (hcpu : (T : Subgroup G).characteristicNormalizerClosure ≤ M)
    (hM : M ≠ ⊤) :
    ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G) := by
  let : Nontrivial T := (nontrivial_iff_ne_bot _).mpr hT
  let Z := (omega₁ (center T) (p := 2)).map (center T).subtype
  let : (omega₁ (center T) (p := 2)).Characteristic := omega₁_characteristic _
  let : Z.Characteristic := inferInstance
  have hZ : Z ≠ ⊥ := omega_center_ne_bot T.isPGroup'
  have hZT : omegaOneCenterAmbient (T : Subgroup G) ≠ ⊥ := by
    intro hz
    exact hZ ((Z.map_eq_bot_iff_of_injective (T : Subgroup G).subtype_injective).mp hz)
  have hNZ : normalizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) ≤ M :=
    (normalizer_le_characteristicNormalizerClosure (T : Subgroup G) Z hZ).trans hcpu
  have hJne : elementaryAbelianMaxJ (T : Subgroup G) ≠ ⊥ := by
    intro hj
    apply hZT
    apply le_bot_iff.mp
    rw [←hj]
    intro z hz
    exact ((mem_omegaOneCenterAmbient_iff _ z).mp
      (omegaCenter_le_omegaCenter_maxJ (T : Subgroup G) hz)).1
  have hNJ := (normalizer_maxJ_le_characteristicNormalizerClosure (T : Subgroup G)
    (T : Subgroup G) (sSup_le fun _ hA => hA.1) le_rfl hJne).trans hcpu
  have hCU : centralizer (U : Set G) ≤ M := by
    apply le_trans _ ((Subgroup.centralizer_le_normalizer _).trans hNZ)
    apply centralizer_le
    rw [hspan]
    exact le_normalClosure
  intro hJ
  apply hM
  apply top_unique
  intro g _
  obtain ⟨n,hn,c,hc,rfl⟩ := thompson_normalizer_factorization U T hJ g
  exact M.mul_mem (hNJ hn) (hCU hc)

variable {H : Type v} [Group H] [Finite H]
theorem quasisimple_linear_outside_of_control
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (hqs : IsQuasisimple (generalizedFitting
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker))))
    (s : MovedSection ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype)
      (generalizedFitting (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker))))
    (F : BinaryField)
    (hnatural : IsLinearNatural (s.action.comp (generalizedFitting
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker))).subtype) F 2)
    (hspan : U = normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hfit : generalizedFitting G = pCore 2 G)
    (M : Subgroup G)
    (hcpu : (T : Subgroup G).characteristicNormalizerClosure ≤ M) (hM : M ≠ ⊤) :
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
  exact quasisimple_linear_outside_moved_chi_source T hP U hU hJ q hq hker
    hqs s F hnatural hspan hfit M hcpu hM
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
