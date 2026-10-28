module

public import CFSG.Quasithin.ChapterE.Section03.Parameters.Global
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Transport of actual induced conjugation groups

The induced action group of an actor A on a normalized subgroup W is the
quotient of A by its pointwise centralizer on W. Matching these kernels under
an isomorphism of actors gives an isomorphism of the actual action images.
In particular an injective ambient homomorphism preserves the induced group.

The PSU₃ center calculation uses this when transporting its matrix model and
when comparing the actions on V and its displacement. Only conjugation and
the first isomorphism theorem are needed; no model action is assumed here.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.RankOne.UnitaryAction

variable {G H : Type*} [Group G] [Group H]

private noncomputable def actorMap (W A : Subgroup G)
    (hA : A ≤ normalizer (W : Set G)) : A →* inducedAutomizer W A :=
  (W.normalizerMonoidHom.rangeRestrict.subgroupMap
    (A.subgroupOf (normalizer (W : Set G)))).comp
      (subgroupOfEquivOfLe hA).symm.toMonoidHom

private theorem actorMap_surjective (W A : Subgroup G)
    (hA : A ≤ normalizer (W : Set G)) : Function.Surjective (actorMap W A hA) :=
  (MonoidHom.subgroupMap_surjective _ _).comp (subgroupOfEquivOfLe hA).symm.surjective

private theorem actorMap_eq_one_iff (W A : Subgroup G)
    (hA : A ≤ normalizer (W : Set G)) (a : A) :
    actorMap W A hA a = 1 ↔ (a : G) ∈ centralizer (W : Set G) := by
  constructor
  · intro he
    have he' : W.normalizerMonoidHom ⟨a, hA a.property⟩ = 1 :=
      congrArg (fun z => z.val.val) he
    change (⟨a, hA a.property⟩ : normalizer (W : Set G)) ∈ W.normalizerMonoidHom.ker at he'
    rwa [normalizerMonoidHom_ker] at he'
  · intro ha
    apply Subtype.ext
    apply Subtype.ext
    change (⟨a, hA a.property⟩ : normalizer (W : Set G)) ∈ W.normalizerMonoidHom.ker
    rwa [normalizerMonoidHom_ker]

private noncomputable def actionEquiv (W A : Subgroup G) (W' A' : Subgroup H)
    (hA : A ≤ normalizer (W : Set G)) (hA' : A' ≤ normalizer (W' : Set H))
    (e : A ≃* A')
    (hc : ∀ a : A, (a : G) ∈ centralizer (W : Set G) ↔
      (e a : H) ∈ centralizer (W' : Set H)) :
    inducedAutomizer W A ≃* inducedAutomizer W' A' := by
  let f := actorMap W A hA
  let g := (actorMap W' A' hA').comp e.toMonoidHom
  have hk : f.ker = g.ker := by
    ext a
    exact (actorMap_eq_one_iff W A hA a).trans
      ((hc a).trans (actorMap_eq_one_iff W' A' hA' (e a)).symm)
  exact (QuotientGroup.quotientKerEquivOfSurjective f (actorMap_surjective W A hA)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hk).trans
      (QuotientGroup.quotientKerEquivOfSurjective g
        ((actorMap_surjective W' A' hA').comp e.surjective)))

private theorem map_normalizes (f : G →* H) {A W : Subgroup G}
    (hA : A ≤ normalizer (W : Set G)) :
    A.map f ≤ normalizer (W.map f : Set H) := by
  rintro _ ⟨a, ha, rfl⟩
  exact le_normalizer_map f (mem_map_of_mem f (hA ha))

private noncomputable def actionMapEquiv (W A : Subgroup G)
    (hA : A ≤ normalizer (W : Set G)) (f : G →* H) (hf : Function.Injective f) :
    inducedAutomizer W A ≃* inducedAutomizer (W.map f) (A.map f) := by
  apply actionEquiv W A (W.map f) (A.map f) hA (map_normalizes f hA)
    (A.equivMapOfInjective f hf)
  intro a
  constructor
  · intro ha
    apply mem_centralizer_iff.mpr
    rintro _ ⟨w, hw, rfl⟩
    exact (map_mul f _ _).symm.trans ((congrArg f (mem_centralizer_iff.mp ha w hw)).trans
      (map_mul f _ _))
  · intro ha
    apply mem_centralizer_iff.mpr
    intro w hw
    apply hf
    simpa only [map_mul, Subgroup.coe_equivMapOfInjective_apply] using
      mem_centralizer_iff.mp ha (f w) (mem_map_of_mem f hw)

/-- An actor isomorphism identifying the pointwise kernels identifies the
actual induced conjugation groups, even in different ambient groups. -/
theorem exists_actionEquiv (W A : Subgroup G) (W' A' : Subgroup H)
    (hA : A ≤ normalizer (W : Set G)) (hA' : A' ≤ normalizer (W' : Set H))
    (e : A ≃* A')
    (hc : ∀ a : A, (a : G) ∈ centralizer (W : Set G) ↔
      (e a : H) ∈ centralizer (W' : Set H)) :
    Nonempty (inducedAutomizer W A ≃* inducedAutomizer W' A') :=
  ⟨actionEquiv W A W' A' hA hA' e hc⟩

/-- Injective ambient embeddings preserve the actual induced action image. -/
theorem exists_actionMapEquiv (W A : Subgroup G)
    (hA : A ≤ normalizer (W : Set G)) (f : G →* H) (hf : Function.Injective f) :
    Nonempty (inducedAutomizer W A ≃* inducedAutomizer (W.map f) (A.map f)) :=
  ⟨actionMapEquiv W A hA f hf⟩

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.RankOne.UnitaryAction
