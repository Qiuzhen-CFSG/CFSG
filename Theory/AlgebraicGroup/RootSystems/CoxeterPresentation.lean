module

public import Theory.AlgebraicGroup.RootSystems.Coxeter

/-!
  A small, reusable part of the GLS3 §1.8.3(i) route.

  Deletion moves imply injectivity of the canonical map out of a Coxeter
  presentation.  This file packages the final assembly step: if the chosen
  word product is surjective, that injective map is promoted to a Coxeter
  system on the target.
-/

namespace Theory.AlgebraicGroup

variable {B G : Type*} [Group G]

public theorem coxeterSystem_of_word_surjective_and_deletion
    (C : CoxeterMatrix B)
    (φ : C.Group →* G)
    (wprod : List B → G)
    (hword : ∀ l : List B,
      φ (C.toCoxeterSystem.wordProd l) = wprod l)
    (hinv : ∀ l : List B,
      wprod l.reverse = (wprod l)⁻¹)
    (happend : ∀ l m : List B,
      wprod (l ++ m) = wprod l * wprod m)
    (hdel : ∀ l : List B, wprod l = 1 →
      Relation.ReflTransGen (CoxeterMove C) l [])
    (hsurj : Function.Surjective wprod) :
    ∃ cs : CoxeterSystem C G,
      ∀ i : B, CoxeterSystem.simple cs i = φ (C.simple i) := by
  have hinj : Function.Injective φ :=
    coxeterHom_injective_of_deletion C φ wprod hword hinv happend hdel
  have hφsurj : Function.Surjective φ := by
    intro g
    obtain ⟨l, hl⟩ := hsurj g
    refine ⟨C.toCoxeterSystem.wordProd l, ?_⟩
    exact (hword l).trans hl
  exact coxeterSystem_of_bijective_presentedGroup_hom C φ ⟨hinj, hφsurj⟩

end Theory.AlgebraicGroup
