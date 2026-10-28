module

public import Theory.SpecificGroups.SymmetricSix.Parabolics
public import Mathlib.GroupTheory.Perm.Finite
import Mathlib.Tactic

/-!
# Actual duad stabilizers as symmetric-group models

The permutations preserving `{0,1}` split along the two-letter and four-letter
blocks. In the even subgroup the first factor is uniquely determined by the
sign of the second. We construct these embeddings and use their injectivity
and the finite subgroup orders to obtain multiplicative equivalences.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, I.5,
printed pp. 419–421 (the duad parabolic used in I.5.7).
-/

@[expose] public section

namespace Theory.SpecificGroups.SymmetricSix
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

abbrev DuadProduct := Equiv.Perm (Fin 2) × Equiv.Perm (Fin 4)

def duadProductHom : DuadProduct →* S6 :=
  (Equiv.permCongrHom (finSumFinEquiv : Fin 2 ⊕ Fin 4 ≃ Fin 6)).toMonoidHom.comp
    (Equiv.Perm.sumCongrHom _ _)

instance : DecidablePred (· ∈ duadStabilizer) := fun g =>
  inferInstanceAs (Decidable ((pair 0 1).image g = pair 0 1))

theorem duadProductHom_mem : ∀ x, duadProductHom x ∈ duadStabilizer := by decide +kernel

def duadProductToStabilizer : DuadProduct →* duadStabilizer :=
  duadProductHom.codRestrict _ duadProductHom_mem

theorem duadProductHom_injective : Function.Injective duadProductHom :=
  (Equiv.permCongrHom _).injective.comp Equiv.Perm.sumCongrHom_injective

theorem duadStabilizer_card : Nat.card duadStabilizer = 48 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

noncomputable def duadProductEquiv : DuadProduct ≃* duadStabilizer :=
  MulEquiv.ofBijective duadProductToStabilizer
    ((Nat.bijective_iff_injective_and_card _).mpr ⟨fun x y h =>
      duadProductHom_injective (congrArg Subtype.val h), by
        rw [duadStabilizer_card, Nat.card_eq_fintype_card]
        decide⟩)

def signPermTwo : Equiv.Perm (Fin 4) →* Equiv.Perm (Fin 2) where
  toFun g := if g.sign = 1 then 1 else Equiv.swap 0 1
  map_one' := by decide
  map_mul' := by decide +kernel

def a6DuadModelHom : Equiv.Perm (Fin 4) →* S6 :=
  duadProductHom.comp (signPermTwo.prod (MonoidHom.id _))

theorem a6DuadModelHom_even : ∀ x, a6DuadModelHom x ∈ alternatingGroup Letter := by
  change ∀ x, (a6DuadModelHom x).sign = 1
  decide +kernel

def a6DuadModelToStabilizer : Equiv.Perm (Fin 4) →* a6DuadStabilizer :=
  (a6DuadModelHom.codRestrict _ a6DuadModelHom_even).codRestrict _
    (fun _x => duadProductHom_mem _)

instance : DecidablePred (· ∈ a6DuadStabilizer) := fun g =>
  inferInstanceAs (Decidable (g.val ∈ duadStabilizer))

theorem a6DuadStabilizer_card : Nat.card a6DuadStabilizer = 24 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

noncomputable def a6DuadModelEquiv : Equiv.Perm (Fin 4) ≃* a6DuadStabilizer :=
  MulEquiv.ofBijective a6DuadModelToStabilizer
    ((Nat.bijective_iff_injective_and_card _).mpr ⟨fun x y h => by
      have hh := duadProductHom_injective (congrArg (fun g : a6DuadStabilizer => g.val.val) h)
      exact congrArg Prod.snd hh, by
        rw [a6DuadStabilizer_card, Nat.card_eq_fintype_card]
        decide⟩)
end Theory.SpecificGroups.SymmetricSix
