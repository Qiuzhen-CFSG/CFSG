module

public import Theory.Representation.QuadraticFourGroup.Recognition.Burnside.FieldCoordinates.Additive
public import Theory.Representation.QuadraticFourGroup.Recognition.Burnside.FieldCoordinates.ScalarField
public import Theory.Representation.QuadraticFourGroup.Recognition.Burnside.FieldCoordinates.ProjectiveImage

/-!
# Burnside field coordinates on the actual Sylow action

For a finite simple perfect group with an involution, whose elements all have
order two or odd order, we construct finite-field coordinates on its actual
Sylow two-subgroups. The exponent satisfies `1 < n`; every translation and
the reciprocal permutation occur in the transported conjugation action, and
the whole action image lies in `projectiveGroup (GaloisField 2 n)`.

Nonnormality supplies two distinct Sylow subgroups. Their two-point stabilizer
acts regularly and abelianly on the nonidentity root elements. `ScalarField`
constructs the field from this action, and `Additive` identifies the other
Sylow subgroups with its additive group. `ProjectiveImage` normalizes a
swapping involution to act as reciprocal and proves the image containment.
Thus `exists_sylowCoordinates` discharges the intermediate scalar premise.

Source: W. Burnside, *On a Class of Groups of Finite Order* (1900), 269–276,
especially pp. 274–276, `refs/original/burnside-1900.pdf`.
-/

namespace Representation.QuadraticFourGroup.Burnside

open Theory.GroupTheory

/-- Burnside's element-order hypotheses construct projective coordinates on
the actual Sylow action over a field of order `2 ^ n`, with `1 < n`. -/
public theorem exists_sylowCoordinates
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] [Group.IsPerfect G]
    (hG : InvolutionOddSpectrum G) (t : G) (ht : orderOf t = 2) :
    ∃ n : ℕ, 1 < n ∧ Nonempty (SylowCoordinates G (GaloisField 2 n)) := by
  let P : Sylow 2 G := Classical.choice Sylow.nonempty
  obtain ⟨Q, hQP⟩ := P.exists_ne_of_not_normal (hG.sylow_not_normal t ht P)
  obtain ⟨n, hn, ⟨C⟩⟩ := exists_scalarCoordinates hG t ht P Q hQP.symm
  exact ⟨n, hn, nonempty_sylowCoordinates_of_scalarCoordinates hG t ht P Q hQP.symm hn C⟩

end Representation.QuadraticFourGroup.Burnside
