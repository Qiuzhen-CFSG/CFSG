module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.Models
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.RankOne
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.InnerRealization.Presentation
public import Theory.Representation.AbsolutelyIrreducible
public import Mathlib.RepresentationTheory.Character

/-!
# From checked Hall--Janko matrices to the literal carrier action

An exact presentation and a pair of invertible matrices satisfying its five
relations define an action of the degree-100 permutation carrier. The generator
matrices are preserved literally. A full matrix-algebra certificate then proves
absolute irreducibility, over any field and in any universe.

The final application uses the rank-one orbit-basis criterion. This discharges
carrier descent and the scalar-extension step for the large model constructors;
the finite matrix identities and the presentation injectivity remain explicit.
The latter is supplied by the separate presentation exactness development.

Source: ATLAS J2G1-P2, with conventions fixed by the imported `Presentation`;
the matrix candidates are attributed in `ModularCertificate/Source.md`.
-/

@[expose] public noncomputable section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels
open Sporadic.LeechRelated.J2
open G2FourModule.Embedding.InnerRealization
open Matrix

variable {F : Type*} [Field F] {n : ℕ}

/-- Exact comparison with the original carrier; no alternate group is substituted. -/
def carrierEquiv (hp : Function.Injective Presentation.toCarrier) :
    Presentation.UniversalGroup ≃* Carrier :=
  MulEquiv.ofBijective Presentation.toCarrier ⟨hp, Presentation.toCarrier_surjective⟩

/-- Descend the literal matrix pair through the exact five-relator presentation. -/
def action (hp : Function.Injective Presentation.toCarrier)
    (A B : (Matrix (Fin n) (Fin n) F)ˣ) (h : Presentation.Relations A B) :
    Representation F Carrier (Fin n → F) :=
  Matrix.toLinAlgEquiv'.toMonoidHom.comp <|
    (Units.coeHom _).comp <|
      (Presentation.toGroup A B h).comp (carrierEquiv hp).symm.toMonoidHom

@[simp] theorem action_a (hp : Function.Injective Presentation.toCarrier)
    (A B : (Matrix (Fin n) (Fin n) F)ˣ) (h : Presentation.Relations A B) :
    action hp A B h GeneratorPair.a = Matrix.toLin' (A : Matrix (Fin n) (Fin n) F) := by
  have he : carrierEquiv hp (PresentedGroup.of 0) = GeneratorPair.a :=
    Presentation.toCarrier_zero
  simp only [action, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← he,
    MulEquiv.symm_apply_apply, Presentation.toGroup_zero]
  rfl

@[simp] theorem action_b (hp : Function.Injective Presentation.toCarrier)
    (A B : (Matrix (Fin n) (Fin n) F)ˣ) (h : Presentation.Relations A B) :
    action hp A B h GeneratorPair.b = Matrix.toLin' (B : Matrix (Fin n) (Fin n) F) := by
  have he : carrierEquiv hp (PresentedGroup.of 1) = GeneratorPair.b :=
    Presentation.toCarrier_one
  simp only [action, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← he,
    MulEquiv.symm_apply_apply, Presentation.toGroup_one]
  rfl

/-- Matrix density transfers to the algebra of the descended action. -/
theorem action_dense (hp : Function.Injective Presentation.toCarrier)
    (A B : (Matrix (Fin n) (Fin n) F)ˣ) (h : Presentation.Relations A B)
    (hd : Algebra.adjoin F ({↑A, ↑B} : Set (Matrix (Fin n) (Fin n) F)) = ⊤) :
    Algebra.adjoin F (Set.range (action hp A B h)) = ⊤ := by
  let S := Algebra.adjoin F (Set.range (action hp A B h))
  have hle : Algebra.adjoin F ({↑A, ↑B} : Set (Matrix (Fin n) (Fin n) F)) ≤
      S.comap Matrix.toLinAlgEquiv'.toAlgHom := by
    apply Algebra.adjoin_le
    intro M hM
    rcases hM with rfl | hM
    · change Matrix.toLin' (A : Matrix (Fin n) (Fin n) F) ∈ S
      rw [← action_a hp A B h]
      exact Algebra.subset_adjoin (Set.mem_range_self GeneratorPair.a)
    · have hM' : M = ↑B := hM
      subst M
      change Matrix.toLin' (B : Matrix (Fin n) (Fin n) F) ∈ S
      rw [← action_b hp A B h]
      exact Algebra.subset_adjoin (Set.mem_range_self GeneratorPair.b)
  apply top_unique
  intro f _
  have hm : LinearMap.toMatrix' f ∈
      Algebra.adjoin F ({↑A, ↑B} : Set (Matrix (Fin n) (Fin n) F)) := by
    rw [hd]
    trivial
  have hf := hle hm
  change Matrix.toLin' (LinearMap.toMatrix' f) ∈ S at hf
  simpa only [Matrix.toLin'_toMatrix'] using hf

/-- Density proves simplicity without an algebraically closed field hypothesis. -/
theorem action_irreducible [NeZero n] (hp : Function.Injective Presentation.toCarrier)
    (A B : (Matrix (Fin n) (Fin n) F)ˣ) (h : Presentation.Relations A B)
    (hd : Algebra.adjoin F ({↑A, ↑B} : Set (Matrix (Fin n) (Fin n) F)) = ⊤) :
    IsIrreducible (action hp A B h) :=
  irreducible_of_jacobson_density_surjective _ (action_dense hp A B h hd)

/-- The same certificate gives irreducibility after arbitrary scalar extension. -/
theorem action_absolutelyIrreducible [NeZero n]
    (hp : Function.Injective Presentation.toCarrier)
    (A B : (Matrix (Fin n) (Fin n) F)ˣ) (h : Presentation.Relations A B)
    (hd : Algebra.adjoin F ({↑A, ↑B} : Set (Matrix (Fin n) (Fin n) F)) = ⊤) :
    IsAbsolutelyIrreducible (action hp A B h) := by
  let ρ := action hp A B h
  let : IsIrreducible ρ := action_irreducible hp A B h hd
  apply (isAbsolutelyIrreducible_iff_surjective ρ).mpr
  exact surjective_of_jacobson_density_surjective_rep ρ (action_dense hp A B h hd)

/-- Apply the rank-one identity and the two orbit bases to the actual carrier.
These are exactly the algebraic identities requested of the ATLAS certificates. -/
theorem action_absolutelyIrreducible_of_rankOne [NeZero n]
    (hp : Function.Injective Presentation.toCarrier)
    (A B : (Matrix (Fin n) (Fin n) F)ˣ) (h : Presentation.Relations A B)
    (v lam : Fin n → F) (P Pi Q Qi : Matrix (Fin n) (Fin n) F)
    (he : Matrix.vecMulVec v lam ∈ Algebra.adjoin F ({↑A, ↑B} : Set (Matrix (Fin n) (Fin n) F)))
    (hl : ∀ i, ∃ W ∈ Algebra.adjoin F ({↑A, ↑B} : Set (Matrix (Fin n) (Fin n) F)),
      W.mulVec v = fun k => P k i)
    (hr : ∀ j, ∃ W ∈ Algebra.adjoin F ({↑A, ↑B} : Set (Matrix (Fin n) (Fin n) F)), Matrix.vecMul lam W = Q j)
    (hP : P * Pi = 1) (hQ : Qi * Q = 1) :
    IsAbsolutelyIrreducible (action hp A B h) :=
  action_absolutelyIrreducible hp A B h (top_of_rankOne _ v lam P Pi Q Qi he hl hr hP hQ)

/-- A trace certificate on a presentation word evaluates at its literal image
in the permutation carrier, with the same multiplication convention. -/
theorem action_character_word (hp : Function.Injective Presentation.toCarrier)
    (A B : (Matrix (Fin n) (Fin n) F)ˣ) (h : Presentation.Relations A B)
    (g : Presentation.UniversalGroup) :
    (action hp A B h).character (Presentation.toCarrier g) =
      Matrix.trace (Presentation.toGroup A B h g : Matrix (Fin n) (Fin n) F) := by
  rw [Representation.character,
    LinearMap.trace_eq_matrix_trace F (Pi.basisFun F (Fin n))]
  change Matrix.trace (LinearMap.toMatrix' (action hp A B h (carrierEquiv hp g))) = _
  simp only [action, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply]
  exact congrArg Matrix.trace (LinearMap.toMatrix'_toLin' _)

/-- Unequal checked traces of the same word distinguish two descended actions.
In particular this supplies the equal-degree step for the degree-64 pair. -/
theorem actions_inequivalent_of_trace (hp : Function.Injective Presentation.toCarrier)
    (A B C D : (Matrix (Fin n) (Fin n) F)ˣ)
    (hAB : Presentation.Relations A B) (hCD : Presentation.Relations C D)
    (g : Presentation.UniversalGroup)
    (hne : Matrix.trace (Presentation.toGroup A B hAB g : Matrix (Fin n) (Fin n) F) ≠
      Matrix.trace (Presentation.toGroup C D hCD g : Matrix (Fin n) (Fin n) F)) :
    IsEmpty ((action hp A B hAB).Equiv (action hp C D hCD)) := by
  constructor
  intro e
  apply hne
  have he := congrFun (Representation.char_iso e) (Presentation.toCarrier g)
  simpa only [action_character_word] using he

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels
