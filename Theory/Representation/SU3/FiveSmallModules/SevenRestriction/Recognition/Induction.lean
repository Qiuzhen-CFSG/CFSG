module

public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Inputs
public import Theory.Representation.SU3.FiveSmallModules.Degrees.Induction

/-!
# Literal principal-series sections from eigenlines

Frobenius reciprocity sends a nonzero subgroup eigenvector to a surjection
from its induced character when the target is irreducible. The first
isomorphism theorem identifies the target with the quotient by the kernel
inside the top subrepresentation. This is exactly the nested subquotient
convention of `PrincipalSeriesRecognition`.

This argument is used only when an eigenline has been proved. In particular,
it makes no eigenline assertion for the degree-twenty modules.

Source: the principal-series route to Guralnick–Malle,
*Classification of 2F-modules I*, Proposition 4.3, pp.10–11.
-/

public section

namespace Representation.SU3.FiveSmallModules.SevenRestriction

variable {K G V W : Type*} [Field K] [Group G]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- An equivariant surjection gives a literal nested subquotient, with the
equivalence oriented from the specified target to the quotient action. -/
theorem subquotient_of_surjective
    {ρ : Representation K G V} {τ : Representation K G W}
    (f : ρ.IntertwiningMap τ) (hf : Function.Surjective f) :
    ∃ (S : Subrepresentation ρ) (T : Subrepresentation S.toRepresentation),
      Nonempty (τ.Equiv T.quotientRepresentation) := by
  let S : Subrepresentation ρ := ⊤
  let j : S.toRepresentation.IntertwiningMap ρ :=
    ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  let p := f.comp j
  have hp : Function.Surjective p := by
    intro w
    obtain ⟨v, rfl⟩ := hf w
    exact ⟨⟨v, by trivial⟩, rfl⟩
  refine ⟨S, p.ker, ⟨(Representation.Equiv.mk
    (p.toLinearMap.quotKerEquivOfSurjective hp) ?_).symm⟩⟩
  intro g
  apply LinearMap.ext
  intro v
  induction v using Submodule.Quotient.induction_on with
  | H v => exact LinearMap.congr_fun (p.isIntertwining' g) v

/-- A proved eigenline realizes a simple representation as an actual section
of the induced character, using Mathlib's induction convention. -/
theorem principal_series_subquotient_of_eigenline
    (B : Subgroup G) (τ : Representation K G V) [τ.IsIrreducible]
    (χ : B →* Kˣ) (v : V) (hv : v ≠ 0)
    (hχ : ∀ b : B, τ b v = (χ b : K) • v) :
    ∃ (S : Subrepresentation (ind B.subtype (scalarCharacter χ)))
      (T : Subrepresentation S.toRepresentation),
      Nonempty (τ.Equiv T.quotientRepresentation) := by
  exact subquotient_of_surjective (Degrees.inducedMap B χ τ v hχ)
    (Degrees.inducedMap_surjective B χ τ v hv hχ)

end Representation.SU3.FiveSmallModules.SevenRestriction
