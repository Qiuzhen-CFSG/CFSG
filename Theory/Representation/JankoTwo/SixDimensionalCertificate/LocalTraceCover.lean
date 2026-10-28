module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.TraceGeometry.OddClasses
public import Theory.Representation.PRegularTrace

/-!
# Local traces determine a characteristic-two Hall--Janko character

Equality on the marked C₅ × C₅, the cubics c and r², the septic ab, and the
mixed elements c*x^i first gives equality on every odd-order element, by the
proved literal conjugacy coverage. Simultaneous p-regular trace reduction then
compares the characters on every element of the carrier. The field need not
be algebraically closed and the representations need not be irreducible.

This is the global comparison used by the degree-six certificate for
Aschbacher--Smith K.4.5, printed p.460, and Hiss--Malle corrected Table 2.
The finite list of trace equalities remains explicit: its spectral proof and
comparison with the marked G₂(4) constituent belong to the certificate assembly.
-/

namespace Representation.JankoTwo.SixDimensionalCertificate.LocalTraceCover
open Sporadic.LeechRelated.J2 TraceGeometry

universe u v
variable {F : Type u} [Field F] {V W : Type v}
  [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]

private theorem character_eq_of_isConj
    (ρ : Representation F Carrier V) (σ : Representation F Carrier W)
    {g h : Carrier} (hc : IsConj g h) (he : ρ.character h = σ.character h) :
    ρ.character g = σ.character g := by
  obtain ⟨z, hz⟩ := isConj_iff.mp hc
  rw [← hz, ρ.char_conj, σ.char_conj] at he
  exact he

/-- The local character comparisons cover all odd-order elements of the actual
carrier, including its two classes of elements of order fifteen. -/
public theorem character_eq_on_odd_of_local
    (ρ : Representation F Carrier V) (σ : Representation F Carrier W)
    (hxy : ∀ i j : Fin 5, ρ.character (x ^ i.val * y ^ j.val) =
      σ.character (x ^ i.val * y ^ j.val))
    (hc : ρ.character c = σ.character c)
    (hr : ρ.character (r ^ 2) = σ.character (r ^ 2))
    (hab : ρ.character (GeneratorPair.a * GeneratorPair.b) =
      σ.character (GeneratorPair.a * GeneratorPair.b))
    (hcx : ∀ i : Fin 5, ρ.character (c * x ^ i.val) = σ.character (c * x ^ i.val))
    (g : Carrier) (hg : ¬2 ∣ orderOf g) : ρ.character g = σ.character g := by
  rcases odd_order_conjugacy g hg with ⟨i, j, h⟩ | h | h | h | ⟨i, h⟩
  · exact character_eq_of_isConj ρ σ h (hxy i j)
  · exact character_eq_of_isConj ρ σ h hc
  · exact character_eq_of_isConj ρ σ h hr
  · exact character_eq_of_isConj ρ σ h hab
  · exact character_eq_of_isConj ρ σ h (hcx i)

variable [FiniteDimensional F V] [FiniteDimensional F W]

/-- In characteristic two the finite local trace comparisons determine the
whole character. All conjugacy and p-regular coverage premises are discharged. -/
public theorem character_eq_of_local [CharP F 2]
    (ρ : Representation F Carrier V) (σ : Representation F Carrier W)
    (hxy : ∀ i j : Fin 5, ρ.character (x ^ i.val * y ^ j.val) =
      σ.character (x ^ i.val * y ^ j.val))
    (hc : ρ.character c = σ.character c)
    (hr : ρ.character (r ^ 2) = σ.character (r ^ 2))
    (hab : ρ.character (GeneratorPair.a * GeneratorPair.b) =
      σ.character (GeneratorPair.a * GeneratorPair.b))
    (hcx : ∀ i : Fin 5, ρ.character (c * x ^ i.val) = σ.character (c * x ^ i.val)) :
    ρ.character = σ.character := by
  funext g
  obtain ⟨h, hodd, he⟩ := exists_pRegular_same_character (F := F) 2 g
  exact (he V ρ).trans
    ((character_eq_on_odd_of_local ρ σ hxy hc hr hab hcx h hodd).trans (he W σ).symm)

end Representation.JankoTwo.SixDimensionalCertificate.LocalTraceCover
