module

public import Theory.SpecificGroups.Lyons.GebhardtLocalParabolicCertificateSetup
public import Theory.GroupTheory.CosetEnumeration

/-!
# Interpreting local enumeration relators

Restrict the first sixteen literal Gebhardt relators to the first four letters.
Embedding them back gives the original words: this checks that no outer letter
occurs. Their images in the local subgroup are therefore the identity.

A signed-word enumeration input is sound once its relator words represent
members of this list and its subgroup letters are among the first three
letters. This connects proof-producing enumeration to the existing source
presentation without assuming its order or identifying it with a finite group.

Source: Gebhardt, Experimental Mathematics 9 (2000), 333–338, Section 3B.
-/

namespace Lyons.Gebhardt.LocalParabolicCertificate
@[expose] public section
open Theory.GroupTheory.CosetEnumeration

/-- Restrict local letters; the unused fifth letter is sent to the first. -/
def restrictGenerator (i : Alphabet) : Fin 4 := ⟨i.val % 4, Nat.mod_lt _ (by decide)⟩

/-- The sixteen source relators on the four-letter local alphabet. -/
def freeRelators : List (FreeGroup (Fin 4)) :=
  (parabolicRelators ++ localRelators).map (FreeGroup.map restrictGenerator)

private theorem embed_restrict_relator (r : FreeGroup Alphabet)
    (hr : r ∈ parabolicRelators ++ localRelators) :
    FreeGroup.map Fin.castSucc (FreeGroup.map restrictGenerator r) = r := by
  simp only [parabolicRelators, localRelators, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp [word, letter, conjugate, commutatorWord, equationRelator, restrictGenerator]

theorem freeRelator_eq_one (r : FreeGroup (Fin 4)) (hr : r ∈ freeRelators) :
    FreeGroup.lift generator r = 1 := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
  apply Subtype.ext
  have he : localSubgroup.subtype.comp (FreeGroup.lift generator) =
      (PresentedGroup.mk relators).comp (FreeGroup.map Fin.castSucc) := by
    ext i
    simp [generator, PresentedGroup.of]
  change (localSubgroup.subtype.comp (FreeGroup.lift generator))
    (FreeGroup.map restrictGenerator s) = 1
  rw [he, MonoidHom.comp_apply, embed_restrict_relator s hs]
  rcases List.mem_append.mp hs with hs | hs
  · exact LocalTower.parabolicRelator_eq_one s hs
  · exact LocalTower.localRelator_eq_one s hs

private theorem eval_eq_lift (w : Word (Fin 4)) :
    eval generator w = FreeGroup.lift generator (FreeGroup.mk w) := by
  rw [eval, FreeGroup.lift_mk]
  congr 1
  apply List.map_congr_left
  intro a _
  cases a with
  | mk a b => cases b <;> rfl

theorem relationWord_eq_one_of_mem (w : Word (Fin 4))
    (hw : FreeGroup.mk w ∈ freeRelators) : eval generator w = 1 := by
  rw [eval_eq_lift]
  exact freeRelator_eq_one _ hw

theorem models_of_relator_membership (input : Input (Fin 4))
    (hzero : input.reps.getD 0 [] = [])
    (hrel : ∀ w ∈ input.relators, FreeGroup.mk w ∈ freeRelators)
    (hsub : ∀ a ∈ input.subgroup, a.1.val < 3) : Models generator parabolic input where
  zero := hzero
  relators := fun w hw => relationWord_eq_one_of_mem w (hrel w hw)
  subgroup := by
    rintro ⟨a, b⟩ ha
    have h := generator_mem_parabolic a (hsub (a, b) ha)
    cases b with
    | false => exact parabolic.inv_mem h
    | true => exact h

end
end Lyons.Gebhardt.LocalParabolicCertificate
