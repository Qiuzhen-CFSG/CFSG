module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairedFiveFixedDisplacement
public import Theory.GroupTheory.ElementaryDisplacementCentralJoin
/-!
# Displacement on the actual Baumann center in the paired-five case

The central omega subgroup of Baum(T) is alpha(T). E.2.3 splits it as its
residual centralizer joined with C_U(J(T)). The marked fixed-plane theorem
therefore bounds each original residual-factor actor by the same nonzero
center in its original commutator module. Outside Baum(T), the action on this
actual elementary group is nontrivial.

Source: Aschbacher–Smith E.2.3(3) and 10.2.1, printed pp.216–217 and743.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB ChapterB.SourceInduction BinaryPermutation
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
private theorem normalizes_baumann_center (T : Subgroup G) {g : G} (hg : g∈T) :
    g ∈ normalizer (omegaOneCenterAmbient (baumann T) : Set G) := by
  rw [omegaCenter_baumann_eq_thompsonAlpha,mem_normalizer_iff_map_conj_eq]
  change (omegaOneCenterAmbient (elementaryAbelianMaxJ T)).map (MulAut.conj g).toMonoidHom = _
  rw [←omegaOneCenterAmbient_map_injective _ (MulAut.conj g).injective]
  congr 1
  exact mem_normalizer_iff_map_conj_eq.mp
    ((normalizer_le_normalizer_elementaryAbelianMaxJ T) (T.le_normalizer hg))

theorem paired_symmetric_baumann_center_displacement
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype))
    (c : d.MarkedProduct (naturalRepresentation (Fin 5)))
    (hexchange : letI := offenderSubgroup_normal (NormalElementaryQuotient.representation U q hq hker)
      ∃ t : T.mapSurjective hq,
        d.first.map (MulAut.conjNormal (t:H)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t:H)).toMonoidHom = d.first) :
    let Y := offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)
    ∃ v₁ v₂ : G,
      v₁ ∈ ⁅U,factorResidual q Y d.first⁆ ∧ v₁ ≠ 1 ∧
      v₂ ∈ ⁅U,factorResidual q Y d.second⁆ ∧ v₂ ≠ 1 ∧
      (∀ g ∈ (T : Subgroup G) ⊓ factorResidual q Y d.first,
        ∀ x ∈ omegaOneCenterAmbient (baumann (T : Subgroup G)),
          ⁅g,x⁆=1 ∨ ⁅g,x⁆=v₁) ∧
      (∀ g ∈ (T : Subgroup G) ⊓ factorResidual q Y d.second,
        ∀ x ∈ omegaOneCenterAmbient (baumann (T : Subgroup G)),
          ⁅g,x⁆=1 ∨ ⁅g,x⁆=v₂) := by
  let E := omegaOneCenterAmbient (baumann (T : Subgroup G))
  let F := U ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)
  let Y := offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)
  let := omegaOneCenterAmbient_elementaryAbelian (baumann (T : Subgroup G))
  have he : E=(E ⊓ centralizer (pResidual 2 G : Set G)) ⊔ F := by
    simpa only [E,F,omegaCenter_baumann_eq_thompsonAlpha] using
      (paired_alpha_and_saturation_of_symmetric_model T hP U hU hJ q hq hker d c hexchange).2.1
  have hgen := paired_residual_factors_generate T hP U hU hJ q hq hker d
  obtain ⟨v₁,v₂,hv₁,hn₁,hv₂,hn₂,h₁,h₂⟩ :=
    paired_symmetric_fixed_displacement T U hU hJ q hq hker d c hexchange
  refine ⟨v₁,v₂,hv₁,hn₁,hv₂,hn₂,?_,?_⟩
  · intro g hg x hx
    exact displacement_on_elementary_central_join E _ F (pResidual 2 G) he inf_le_right
      g v₁ (hgen ▸ mem_sup_left hg.2) (normalizes_baumann_center _ hg.1) (h₁ g hg) x hx
  · intro g hg x hx
    exact displacement_on_elementary_central_join E _ F (pResidual 2 G) he inf_le_right
      g v₂ (hgen ▸ mem_sup_right hg.2) (normalizes_baumann_center _ hg.1) (h₂ g hg) x hx

/-- Outside Baum(T), an original Sylow element moves the actual central omega group. -/
theorem exists_baumann_center_commutator_ne_one (T : Subgroup G) {g : G}
    (hg : g∈T) (hout : g∉baumann T) :
    ∃ x∈omegaOneCenterAmbient (baumann T), ⁅g,x⁆≠1 := by
  by_contra! h
  apply hout
  refine ⟨hg,?_⟩
  intro x hx
  exact (commutatorElement_eq_one_iff_mul_comm.mp
    (h x (omegaCenter_baumann_eq_thompsonAlpha T ▸ hx))).symm
end CFSG.Quasithin.ChapterE.ThompsonAction
