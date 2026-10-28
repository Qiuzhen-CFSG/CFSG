module
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Actors normalized by a marked Borel

The detector below says that an automorphism subgroup preserving a Sylow
2-subgroup, and normalized by its inner normalizer, consists of inner
actors whenever its inner intersection is a 2-group. It transports through
the actual group equivalence, including both marked subgroups.

Source application: Aschbacher--Smith 14.6.15, printed p.1035. The binary
PSL₂ proof and the literal component-action consumer supply this property;
the definition alone asserts no classification result.
-/

@[expose] public section
open Subgroup

namespace MulAut

def BorelActorInner (C : Type*) [Group C] : Prop :=
  ∀ P : Sylow 2 C, ∀ A : Subgroup (MulAut C),
    (∀ α ∈ A, (P : Subgroup C).map α.toMonoidHom = P) →
    (normalizer (P : Set C)).map conj ≤ normalizer (A : Set _) →
    IsPGroup 2 (A ⊓ innerSubgroup C : Subgroup _) → A ≤ innerSubgroup C

theorem BorelActorInner.of_mulEquiv {C E : Type*} [Group C] [Group E]
    [Finite C] (he : BorelActorInner E) (e : C ≃* E) : BorelActorInner C := by
  intro P A hP hB hi
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let f := (congr e).toMonoidHom
  let D := A.map f
  have hQ : (Q : Subgroup E) = (P : Subgroup C).map e.toMonoidHom := rfl
  have hN : (normalizer (P : Set C)).map e.toMonoidHom = normalizer (Q : Set E) :=
    map_equiv_normalizer_eq _ e
  have hQP : ∀ β ∈ D, (Q : Subgroup E).map β.toMonoidHom = Q := by
    rintro β ⟨α,hα,rfl⟩
    change (Q : Subgroup E).map (congr e α).toMonoidHom = Q
    rw [hQ,map_map]
    have hcomp : (congr e α).toMonoidHom.comp e.toMonoidHom =
        e.toMonoidHom.comp α.toMonoidHom := by ext x; simp
    rw [hcomp,←map_map,hP α hα]
  have hconj : (normalizer (Q : Set E)).map conj =
      ((normalizer (P : Set C)).map conj).map f := by
    rw [←hN,map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    exact (congr_conj e x).symm
  have hBD : (normalizer (Q : Set E)).map conj ≤ normalizer (D : Set _) := by
    rw [hconj]
    exact (map_mono hB).trans (le_normalizer_map f)
  have hiD : IsPGroup 2 (D ⊓ innerSubgroup E : Subgroup _) := by
    have hh : (A ⊓ innerSubgroup C).map f = D ⊓ innerSubgroup E := by
      rw [Subgroup.map_inf _ _ f (congr e).injective, map_innerSubgroup_congr e]
    exact hh ▸ hi.map f
  have hD := he Q D hQP hBD hiD
  intro α hα
  have hh := hD (mem_map_of_mem f hα)
  rw [←map_innerSubgroup_congr e] at hh
  obtain ⟨β,hβ,hβα⟩ := hh
  exact (congr e).injective hβα ▸ hβ

end MulAut

