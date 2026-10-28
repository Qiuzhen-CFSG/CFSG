module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure.Reduction
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.Universality

/-!
# Local inputs to the natural even SU₄ covering

Splitting double covers on the actual standard plane parabolic, together
with exclusion of odd-prime covering kernels, implies central closure for
any source Hermitian form. Applying `naturalCover_isUniversal_of_closed`
then gives universality of its literal natural projective covering.

The two local inputs below remain explicit. This is an assembly interface,
not yet the central-extension calculation of Aschbacher–Smith I.1.3–4,
printed pp.407–408 of `refs/quasithin.pdf`, and GLS3 §6.1. The ordinary
application excludes q = 2, whose exceptional multiplier is nontrivial.
-/

public section

open BenderSuzuki.MatrixGroups Theory.GroupTheory
open PerfectCentralCovering

namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure

universe u w
variable {F : Type u} [Field F] [Finite F]

/-- Apply the two local inputs to the actual natural projection, with its
perfectness derived from the inherited projective quasisimplicity. -/
theorem naturalCover_isUniversal_of_local_sections (J : HermitianForm 4 F)
    (n : ℕ) (hn : 2 ≤ n)
    (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    [IsQuasisimple (ProjectiveSpecialUnitaryMatrixGroup J)]
    (htwo : ∀ (E : Type u) [Group E] [Finite E] (d : Cover E (Standard J)),
      Nat.card d.toMonoidHom.ker = 2 →
        ∃ s : Plane J →* E, d.toMonoidHom.comp s = (Plane J).subtype)
    (hodd : ∀ (p : ℕ), p.Prime → p ≠ 2 →
      ∀ (E : Type u) [Group E] [Finite E] (d : Cover E (Standard J)),
        Nat.card d.toMonoidHom.ker ≠ p) :
    letI := fourEven_isPerfect J (Nat.even_pow.mpr ⟨even_two, by omega⟩) hcard hconj
    letI := natural_isQuasisimple J
    Covering.IsUniversal.{u, u, w} (naturalCover J) := by
  let := fourEven_isPerfect J (Nat.even_pow.mpr ⟨even_two, by omega⟩) hcard hconj
  apply naturalCover_isUniversal_of_closed J
  intro E _ _ c
  exact injective_of_local_sections J n (by omega) hcard hconj htwo hodd c

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure
