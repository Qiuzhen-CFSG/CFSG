module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.Realization
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.PrincipalSpectra.SmallFactors.Cubic.NormalForm

/-!
# The actual order-seven actor for the cubic certificates

The positive word g₀³g₁g₀g₁ has order seven, checked on its literal 3×3
matrix over the existing F₂₅. Its inverse is transported through the proved
canonical group isomorphism. This is exactly the six-letter word in inverse
generators used by the quotient coordinates, not an unrelated model actor.
Source application: Guralnick–Malle, Proposition 4.3, pp.10–11;
Aschbacher–Smith K.2, printed p.453.
-/

@[expose] public section
namespace Representation.SU3.FiveSmallModules.SevenRestriction.SmallFactors.Cubic
open Degrees.CubicCalculation
open ModelFlag ModelFlag.FiniteGroup
noncomputable def positive : standardGroup fieldForm :=
  generator 0 ^ 3 * generator 1 * generator 0 * generator 1
private def raw : Matrix (Fin 3) (Fin 3) Field :=
  !![⟨4, 4⟩, ⟨1, 1⟩, ⟨3, 2⟩; ⟨0, 1⟩, ⟨3, 2⟩, ⟨0, 2⟩; ⟨4, 1⟩, ⟨1, 1⟩, ⟨3, 3⟩]
private theorem raw_agreement : FiniteGroup.rawGenerator 0 ^ 3 * FiniteGroup.rawGenerator 1 *
    FiniteGroup.rawGenerator 0 * FiniteGroup.rawGenerator 1 = raw := by decide +kernel
private theorem raw_power : raw ^ 7 = 1 := by decide +kernel
noncomputable def actor : standardGroup modelForm := word (fun a => (canonicalEquiv (generator a))⁻¹)
theorem actor_eq : actor = canonicalEquiv positive⁻¹ := by
  simp [actor, word, positive, mul_inv_rev, pow_succ, map_mul, map_inv, mul_assoc]
theorem positive_order : orderOf positive = 7 := by
  have hp : positive ^ 7 = 1 := by
    apply Subtype.ext
    apply Units.ext
    change (FiniteGroup.rawGenerator 0 ^ 3 * FiniteGroup.rawGenerator 1 *
      FiniteGroup.rawGenerator 0 * FiniteGroup.rawGenerator 1) ^ 7 = 1
    rw [raw_agreement, raw_power]
  have hn : positive ≠ 1 := by
    intro h
    have he := congrArg (fun g : standardGroup fieldForm => g.val.val) h
    apply (show raw ≠ 1 by decide +kernel)
    rw [← raw_agreement]
    exact he
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact orderOf_eq_prime_iff.mpr ⟨hp, hn⟩
theorem actor_order : orderOf actor = 7 := by
  rw [actor_eq, canonicalEquiv.orderOf_eq, orderOf_inv, positive_order]
/-- The original coordinates use precisely this actor word. -/
theorem modelCoordinates_word {K : Type*} [Field K] [CharP K 2]
    (χ : standardBorel modelForm →* Kˣ) (hn : χ ≠ 1) (hc : ∀ b, χ b ^ 3 = 1) :
    word (modelCoordinates χ hn hc).actor = actor := rfl
end Representation.SU3.FiveSmallModules.SevenRestriction.SmallFactors.Cubic
