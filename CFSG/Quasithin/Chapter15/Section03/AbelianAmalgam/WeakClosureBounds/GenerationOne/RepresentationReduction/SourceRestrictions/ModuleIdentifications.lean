module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SLTwoExtension


/-!
# Actual module identities for the source restriction outputs

Central quotient identifications retain the actor isomorphism and an
equivariant linear equivalence from the literal I/C_I(K). Central extension
identifications retain the invariant centralized kernel and the quotient
action, without assuming the extension splits. Their transport lemmas feed
the published Borel fixed-space calculations, including the SL₂ exception.

The diagram witness is induced by a specified element of the actual T,
using the same group identification. Movement of standard parabolic
conjugacy classes implies that this automorphism is outer. None of these
structures is asserted to exist: their construction from the source
classification alternatives remains the restriction obligation.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 15.3.65,
printed p.1152; F.9.18(4),(5), pp.325--326; B.5.1, pp.99--100.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions
open Representation Representation.BinaryOffender Subgroup

/-- The field size relevant to the Borel fixed-space computations. -/
theorem field_card_gt_two {F : Type*} {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (hf : 1 < f) : 2 < Nat.card F := by
  rw [hF]
  simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) hf

/-- The even-exponent orthogonal SL₂ alternative cannot have the source's
field order. This compares the actual defining-field cardinality, not a
free group-family tag or the vector-space dimension. -/
theorem field_card_ne_even_exponent {F : Type*} {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (hf : Odd f) (n : ℕ) : Nat.card F ≠ 2 ^ (2 * n) := by
  intro h
  have he : f = 2 * n := Nat.pow_right_injective (by decide : 2 ≤ 2) (hF.symm.trans h)
  obtain ⟨k, hk⟩ := hf
  omega


variable {D E V X : Type*} [Group D] [Group E]
    [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup X] [Module (ZMod 2) X]

/-- An actual equivariant identification of a literal central quotient with a
specified representation. This is conclusion data, not a classification theorem. -/
structure CentralQuotientIdentification
    (ρ : Representation (ZMod 2) D V) (K : Subgroup D)
    (I : Submodule (ZMod 2) V) (hI : K ≤ subspaceStabilizer ρ I)
    (σ : Representation (ZMod 2) E X) where
  groupEquiv : K ≃* E
  linearEquiv : centralQuotient ρ K I ≃ₗ[ZMod 2] X
  equivariant : ∀ g v, linearEquiv (centralQuotientRepresentation ρ K I hI g v) =
    σ (groupEquiv g) (linearEquiv v)

/-- A model calculation passes to the central quotient using the same map
for its actor and Borel. -/
theorem CentralQuotientIdentification.inf_fixedSpace_le
    {ρ : Representation (ZMod 2) D V} {K : Subgroup D}
    {I : Submodule (ZMod 2) V} {hI : K ≤ subspaceStabilizer ρ I}
    {σ : Representation (ZMod 2) E X}
    (d : CentralQuotientIdentification ρ K I hI σ)
    (B : Subgroup D) (B' : Subgroup E)
    (hB : (B.subgroupOf K).map d.groupEquiv.toMonoidHom = B')
    (hzero : fixedSpace σ B' = ⊥) : I ⊓ fixedSpace ρ B ≤ fixedSpace ρ K :=
  inf_fixedSpace_le_of_centralQuotient ρ K B I hI
    (fixedSpace_eq_bot_of_equivariant _ σ d.groupEquiv.toMonoidHom
      d.linearEquiv d.equivariant _ B' hB hzero)

/-- An actual module extension over a centralized invariant subspace. The
quotient representation and equivariance are retained; no splitting is required. -/
structure CentralExtensionIdentification
    (ρ : Representation (ZMod 2) D V) (σ : Representation (ZMod 2) E X) (φ : D →* E) where
  kernel : Subrepresentation ρ
  centralized : kernel.toSubmodule ≤ fixedSpace ρ ⊤
  linearEquiv : (V ⧸ kernel.toSubmodule) ≃ₗ[ZMod 2] X
  equivariant : ∀ g v, linearEquiv (kernel.quotientRepresentation g v) =
    σ (φ g) (linearEquiv v)

/-- Fixed spaces of the identified model control the possibly nonsplit extension. -/
theorem CentralExtensionIdentification.fixedSpace_le
    {ρ : Representation (ZMod 2) D V} {σ : Representation (ZMod 2) E X} {φ : D →* E}
    (d : CentralExtensionIdentification ρ σ φ)
    (B : Subgroup D) (B' : Subgroup E) (hB : B.map φ = B')
    (hzero : fixedSpace σ B' = ⊥) : fixedSpace ρ B ≤ fixedSpace ρ ⊤ :=
  fixedSpace_le_of_central_extension ρ d.kernel d.centralized B
    (fixedSpace_eq_bot_of_equivariant _ σ φ d.linearEquiv d.equivariant B B' hB hzero)

/-- Moving a parabolic conjugacy class is the intrinsic diagram condition.
The parabolics supplied by a model must be its two standard end-node parabolics. -/
def MovesParabolicClasses (γ : MulAut E) (P Q : Subgroup E) : Prop :=
  ¬ ((∃ x : E, P.map γ.toMonoidHom = P.map (MulAut.conj x).toMonoidHom) ∧
    (∃ x : E, Q.map γ.toMonoidHom = Q.map (MulAut.conj x).toMonoidHom))

/-- The diagram automorphism is induced by an actual normalizing element
of T and preserves the specified model Borel. The identification map is the
one used by the module, so an unrelated diagram automorphism cannot witness it. -/
structure InducedDiagramAction (K T : Subgroup D) (φ : K ≃* E)
    (B P Q : Subgroup E) where
  element : D
  mem_T : element ∈ T
  normalizes : element ∈ normalizer (K : Set D)
  automorphism : MulAut E
  induced : automorphism = MulAut.congr φ
    (K.normalizerMonoidHom ⟨element, normalizes⟩)
  borel : B.map automorphism.toMonoidHom = B
  moves : MovesParabolicClasses automorphism P Q

/-- A nontrivial induced diagram action is outer, with respect to the actual
model group. This follows from movement of parabolic conjugacy classes. -/
theorem InducedDiagramAction.outer {K T : Subgroup D} {φ : K ≃* E}
    {B P Q : Subgroup E} (d : InducedDiagramAction K T φ B P Q) :
    ¬ ∃ x : E, d.automorphism = MulAut.conj x := by
  rintro ⟨x, hx⟩
  exact d.moves ⟨⟨x, by rw [hx]⟩, ⟨x, by rw [hx]⟩⟩

/-- The SL₂ exception packaged in the exact nonsplit form consumed by the
published Borel calculation. The first central quotient and the remaining
central extension have their literal representations. -/
theorem slTwo_fixedSpace_le_of_two_identifications
    [Finite D] {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
    (ρ : Representation (ZMod 2) D V) (I : Subrepresentation ρ)
    (φ : D →* Matrix.SpecialLinearGroup (Fin 2) F)
    (d₀ : CentralExtensionIdentification I.toRepresentation
      (restrictScalars (k := ZMod 2) (specialLinearNatural (k := F) 2)) φ)
    (d₁ : CentralExtensionIdentification I.quotientRepresentation
      (restrictScalars (k := ZMod 2) (specialLinearNatural (k := F) 2)) φ)
    (B : Subgroup D) (hindex : Odd B.index)
    (hB : B.map φ = Matrix.SpecialLinearGroup.rankOneBorel F)
    (hF : 2 < Nat.card F) : fixedSpace ρ B ≤ fixedSpace ρ ⊤ :=
  slTwo_two_layer_fixed ρ B hindex I d₀.kernel d₀.centralized d₁.kernel d₁.centralized
    φ hB d₀.linearEquiv d₀.equivariant d₁.linearEquiv d₁.equivariant hF

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions
