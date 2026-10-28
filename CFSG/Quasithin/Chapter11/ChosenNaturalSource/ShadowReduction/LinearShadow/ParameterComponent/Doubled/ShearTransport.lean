module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.Shears
public import CFSG.Quasithin.ChapterE.Section03.Parameters.AutomizerFF
public import Theory.GroupTheory.GeneralizedFitting.StandardComponent

/-!
# Transporting doubled shear coordinates and their coranks

An ambient equivalence carries both actor and module, their conjugation law,
and the full shear parameter range together. The two centralizer indices
are invariant under the same map. The source application uses the inverse
of the chosen conjugation to return to the original doubled marking.

Source: Aschbacher--Smith, 11.3.6, printed pp.772--773.
-/

@[expose] public noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
variable {G F : Type*} [Group G] [Field F] {A B : Subgroup G}

namespace ShearCoordinates
variable (d : ShearCoordinates A B F)

/-- Transport all conjugation and surjectivity clauses through the same
ambient equivalence. -/
def map (e : G ≃* G) : ShearCoordinates (A.map e.toMonoidHom) (B.map e.toMonoidHom) F := by
  let a := equivMapOfInjective A e.toMonoidHom e.injective
  let b := equivMapOfInjective B e.toMonoidHom e.injective
  let h : A.map e.toMonoidHom ≤ normalizer (B.map e.toMonoidHom : Set G) :=
    (map_mono d.normalized).trans (B.le_normalizer_map e.toMonoidHom)
  have he (x : A.map e.toMonoidHom) (v : B.map e.toMonoidHom) :
      b.symm ((B.map e.toMonoidHom).normalizerMonoidHom (inclusion h x) v) =
        B.normalizerMonoidHom (inclusion d.normalized (a.symm x)) (b.symm v) := by
    apply b.injective
    rw [b.apply_symm_apply]
    apply Subtype.ext
    change (x:G)*(v:G)*(x:G)⁻¹ =
      e ((a.symm x:G)*(b.symm v:G)*(a.symm x:G)⁻¹)
    rw [map_mul,map_mul,map_inv]
    have ha : e (a.symm x:G) = (x:G) := congrArg Subtype.val (a.apply_symm_apply x)
    have hb : e (b.symm v:G) = (v:G) := congrArg Subtype.val (b.apply_symm_apply v)
    rw [ha,hb]
  refine ⟨h,b.symm.trans d.coordinates,?_,?_⟩
  · intro x
    obtain ⟨p,q,hpq⟩ := d.shear_action (a.symm x)
    exact ⟨p,q,fun v => by change (d.coordinates (b.symm _)).toAdd = _; rw [he]; exact hpq _⟩
  · intro p q
    obtain ⟨x,hx⟩ := d.realizes p q
    refine ⟨a x,fun v => ?_⟩
    change (d.coordinates (b.symm _)).toAdd = _
    rw [he,a.symm_apply_apply]
    exact hx _
end ShearCoordinates

/-- Both literal centralizer coranks are unchanged by one ambient map. -/
theorem corank_centralizer_map (e : G ≃* G) :
    ChapterE.subgroupCorank (A.map e.toMonoidHom)
      (A.map e.toMonoidHom ⊓ centralizer (B.map e.toMonoidHom : Set G)) =
    ChapterE.subgroupCorank A (A ⊓ centralizer (B : Set G)) := by
  have he : centralizer (B.map e.toMonoidHom : Set G) =
      (centralizer (B : Set G)).map e.toMonoidHom := by
    simpa only [coe_map,MulEquiv.coe_toMonoidHom] using
      (Theory.GroupTheory.map_centralizer_equiv (B : Set G) e).symm
  rw [he,← Subgroup.map_inf _ _ _ e.injective,ChapterE.subgroupCorank,
    relIndex_map_map_of_injective _ _ e.injective]
  rfl
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
