module
public import Theory.SpecificGroups.Rudvalis.Model.MarkedStabilizer.Centralizer
public import Theory.SpecificGroups.Rudvalis.Model.OuterStabilizer.TitsEmbedding
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.Automorphisms
public import Mathlib.GroupTheory.IndexNormal
/-!
# The full Rudvalis point stabilizer is the full binary Ree group

The marked Parrott realization gives an index-two simple Tits subgroup.
The certified trivial centralizer makes conjugation faithful. The point
stabilizer and the full Tits automorphism group both have order35942400,
so conjugation is onto. The existing marked automorphism equivalence then
identifies the actual stabilizer with ²F₄(2), rather than its derived subgroup.
Source: GLS3 Table5.3r; Aschbacher--Smith J.5.1.
-/
@[expose] public section
noncomputable section
namespace Rudvalis.MarkedStabilizer
open Subgroup OuterStabilizer.TitsEmbedding

def pointStabilizer : Subgroup Model := MulAction.stabilizer Model (0 : Fin 4060)

def atlasMap : Tits.Atlas1600Group →* Model :=
  (Tits.parrottLift assignment assignment_relations).comp
    Tits.parrottFiniteImageEquiv.symm.toMonoidHom

theorem atlasMap_generator (i : Tits.ParrottGenerator) :
    atlasMap (Tits.atlas1600ParrottAssignment i)=assignment i := by
  have h : Tits.parrottFiniteImageEquiv.symm (Tits.atlas1600ParrottAssignment i)=
      Tits.parrottGenerator i := by
    apply Tits.parrottFiniteImageEquiv.injective
    rw [MulEquiv.apply_symm_apply,Tits.parrottFiniteImageEquiv_generator]
  change Tits.parrottLift assignment assignment_relations
    (Tits.parrottFiniteImageEquiv.symm _) = _
  rw [h,Tits.parrottLift_generator]

theorem atlasMap_injective : Function.Injective atlasMap := by
  apply atlasMap.ker_eq_bot_iff.mp
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal atlasMap.ker inferInstance with h | h
  · exact h
  · have hm : Tits.atlas1600ParrottAssignment .r1∈atlasMap.ker := h ▸ mem_top _
    exact (assignment_r1_ne_one (by
      simpa only [MonoidHom.mem_ker,atlasMap_generator] using hm)).elim

theorem atlasMap_mem (x : Tits.Atlas1600Group) : atlasMap x∈pointStabilizer := by
  have hr : (Tits.parrottLift assignment assignment_relations).range≤pointStabilizer := by
    rw [Tits.parrottLift_range]
    apply (closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    exact assignment_mem_stabilizer i
  exact hr ⟨Tits.parrottFiniteImageEquiv.symm x,rfl⟩

def titsHom : Tits.Atlas1600Group →* pointStabilizer :=
  atlasMap.codRestrict pointStabilizer atlasMap_mem

theorem titsHom_injective : Function.Injective titsHom := by
  intro x y h
  exact atlasMap_injective (congrArg Subtype.val h)

def K : Subgroup pointStabilizer := titsHom.range

def atlasEquiv : Tits.Atlas1600Group ≃* K := MonoidHom.ofInjective titsHom_injective

theorem K_card : Nat.card K=17971200 :=
  (Nat.card_congr atlasEquiv.toEquiv).symm.trans Tits.atlas1600Group_card

theorem pointStabilizer_card : Nat.card pointStabilizer=35942400 :=
  stabilizer_card_of_model_card model_card

theorem K_index : K.index=2 := by
  have h := K.card_mul_index
  rw [K_card,pointStabilizer_card] at h
  omega

instance K_normal : K.Normal := normal_of_index_eq_two K_index

theorem conjNormal_injective : Function.Injective
    (MulAut.conjNormal : pointStabilizer→*MulAut K) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply (eq_bot_iff_forall _).mpr
  intro g hg
  apply Subtype.ext
  apply eq_one_of_fix_zero_of_commute_assignment g.val g.property
  intro i
  let n : K := ⟨titsHom (Tits.atlas1600ParrottAssignment i),⟨_,rfl⟩⟩
  have H := congrArg (fun f : MulAut K => (((f n : K) : pointStabilizer) : Model))
    (show (MulAut.conjNormal : pointStabilizer→*MulAut K) g=1 from hg)
  change (g:Model)*atlasMap (Tits.atlas1600ParrottAssignment i)*(g:Model)⁻¹=
    atlasMap (Tits.atlas1600ParrottAssignment i) at H
  rw [atlasMap_generator] at H
  exact (mul_inv_eq_iff_eq_mul).mp H

def conjugation : pointStabilizer →* MulAut Tits.Atlas1600Group :=
  (MulAut.congr atlasEquiv.symm).toMonoidHom.comp MulAut.conjNormal

theorem conjugation_injective : Function.Injective conjugation :=
  (MulAut.congr atlasEquiv.symm).injective.comp conjNormal_injective

theorem conjugation_bijective : Function.Bijective conjugation := by
  apply (Nat.bijective_iff_injective_and_card conjugation).mpr
  refine ⟨conjugation_injective,?_⟩
  rw [pointStabilizer_card]
  exact Tits.ExceptionalParabolics.FullRee.group_card.symm.trans
    (Nat.card_congr Tits.ExceptionalParabolics.FullRee.atlasAutEquiv.toEquiv)

/-- The actual full stabilizer, with the original conjugation action on its Tits subgroup. -/
def fullEquiv : pointStabilizer≃*ReeF4.Model 0 :=
  (MulEquiv.ofBijective conjugation conjugation_bijective).trans
    Tits.ExceptionalParabolics.FullRee.atlasAutEquiv.symm
end Rudvalis.MarkedStabilizer
