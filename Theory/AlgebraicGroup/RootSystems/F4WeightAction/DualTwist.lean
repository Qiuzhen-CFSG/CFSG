module

public import Theory.AlgebraicGroup.RootSystems.F4WeightAction.Height
/-!
# Exceptional pullback on the F4 weight lattice

The exceptional characteristic-two map pulls a weight a back to
(a₃,a₂,2a₁,2a₀). This integral map is injective, squares to multiplication
by two, and exchanges the simple reflections by reversing their labels.
Simple-word generation proves that it maps each complete Weyl orbit onto
the corresponding orbit of the pulled-back weight, without a finite Weyl
matrix certificate.

Source: Steinberg (1963), §12.2, exceptional fundamental-character relations.
-/

public noncomputable section
open scoped BigOperators Matrix
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace Theory.AlgebraicGroup.StandardRootSystem.F4WeightAction
noncomputable local instance dualTwistRootsFintype : Fintype typeF4Roots := Fintype.ofFinite _
@[expose] def dualTwist : Weight →ₗ[ℤ] Weight where
  toFun a := ![a 3, a 2, 2 * a 1, 2 * a 0]
  map_add' a b := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c a := by ext i; fin_cases i <;> simp <;> ring

lemma dualTwist_square (a : Weight) : dualTwist (dualTwist a) = 2 • a := by
  ext i
  fin_cases i <;> simp [dualTwist, Matrix.cons_val_two, Matrix.cons_val_three]

lemma dualTwist_injective : Function.Injective dualTwist := by
  intro a b h
  have h2 := congrArg dualTwist h
  rw [dualTwist_square, dualTwist_square] at h2
  ext i
  have hi := congrFun h2 i
  change 2 * a i = 2 * b i at hi
  omega

lemma dualTwist_simple (i : Fin 4) (a : Weight) :
    dualTwist (representation (RootPairing.weylGroup.ofIdx typeF4RootPairing
      (typeF4SimpleRootIndex i)) a) =
    representation (RootPairing.weylGroup.ofIdx typeF4RootPairing
      (typeF4SimpleRootIndex (Fin.revPerm i))) (dualTwist a) := by
  rw [representation_simple, representation_simple]
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [dualTwist, rootWeight_simple, typeF4CartanMatrix,
      Matrix.cons_val_two, Matrix.cons_val_three, Fin.revPerm, Fin.rev] <;> ring

private noncomputable def flipSimple (j : typeF4RootPairing_base.support) :
    typeF4RootPairing_base.support :=
  typeF4RootPairing_baseEquiv (Fin.revPerm (typeF4RootPairing_baseEquiv.symm j))

private lemma flipSimple_involutive : Function.Involutive flipSimple := by
  intro j
  simp [flipSimple]

private lemma dualTwist_simpleReflection (j : typeF4RootPairing_base.support) (a : Weight) :
    dualTwist (representation (typeF4RootPairing_base.simpleReflection j) a) =
      representation (typeF4RootPairing_base.simpleReflection (flipSimple j)) (dualTwist a) := by
  obtain ⟨i, rfl⟩ := typeF4RootPairing_baseEquiv.surjective j
  simpa [flipSimple, RootPairing.Base.simpleReflection] using dualTwist_simple i a

private lemma dualTwist_word (l : List typeF4RootPairing_base.support) (a : Weight) :
    dualTwist (representation (typeF4RootPairing_base.wordProd l) a) =
      representation (typeF4RootPairing_base.wordProd (l.map flipSimple)) (dualTwist a) := by
  induction l generalizing a with
  | nil => simp
  | cons j l ih =>
    simp only [RootPairing.Base.wordProd_cons, List.map_cons, map_mul]
    change dualTwist (representation (typeF4RootPairing_base.simpleReflection j)
      (representation (typeF4RootPairing_base.wordProd l) a)) =
      representation (typeF4RootPairing_base.simpleReflection (flipSimple j))
        (representation (typeF4RootPairing_base.wordProd (l.map flipSimple)) (dualTwist a))
    rw [dualTwist_simpleReflection, ih]

lemma dualTwist_orbit (a : Weight) :
    dualTwist '' {b | ∃ w : Weyl, representation w a = b} =
      {b | ∃ w : Weyl, representation w (dualTwist a) = b} := by
  ext b
  constructor
  · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
    obtain ⟨l, _, rfl⟩ := typeF4RootPairing_base.wordLength_spec w
    exact ⟨_, (dualTwist_word l a).symm⟩
  · rintro ⟨w, rfl⟩
    obtain ⟨l, _, rfl⟩ := typeF4RootPairing_base.wordLength_spec w
    refine ⟨representation (typeF4RootPairing_base.wordProd (l.map flipSimple)) a,
      ⟨_, rfl⟩, ?_⟩
    rw [dualTwist_word, List.map_map]
    have hi : flipSimple ∘ flipSimple = id := funext flipSimple_involutive
    rw [hi, List.map_id]
end Theory.AlgebraicGroup.StandardRootSystem.F4WeightAction
