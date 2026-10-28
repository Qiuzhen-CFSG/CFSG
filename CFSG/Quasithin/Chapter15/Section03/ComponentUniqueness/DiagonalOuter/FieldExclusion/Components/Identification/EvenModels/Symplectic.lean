module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.EvenModels.Basic
public import Theory.SpecificGroups.PSL3Two.EmbeddingObstructions
public import Theory.SpecificGroups.SymplecticFour.SevenNormalizer
public import Theory.SpecificGroups.SymplecticFour.EvenProjective

/-!
# Excluding the entire even symplectic family

PSL₃(2) contains a nonidentity seven-element conjugate to its square.
In symplectic four-space the spectrum is closed under inversion, and
squaring conjugacy would give six distinct eigenvalues. Thus the specified
component cannot even embed in PSp₄ over any finite binary field.

Source: Aschbacher--Smith, proof of 15.3.38, printed p.1137, and
Remark A.2.4, p.33. The spectral calculation is proved in SevenNormalizer;
the actual projective-to-symplectic equivalence uses the trivial center
in characteristic two.
-/

public section
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification
universe u
variable {S : Type u} [Group S] (s : SimpleInput S)
include s

/-- No even-field symplectic model contains the specified component. -/
theorem SimpleInput.not_even_symplectic {n : ℕ} :
    ¬ ClassicalGroup.IsPSp S 2 (2 ^ n) := by
  rintro ⟨F, _, _, hF, ⟨e⟩⟩
  let : CharP F 2 := EvenProjective.charTwo_of_card hF
  let d : S ≃* Sp F := e.trans EvenProjective.equiv.symm
  let j := d.toMonoidHom.comp (EvenModels.componentEmbedding s)
  have hj : Function.Injective j := d.injective.comp (EvenModels.componentEmbedding_injective s)
  obtain ⟨a, b, ha, hane, hab⟩ := Matrix.PSL3Two.exists_seven_conjugate_square
  apply SevenNormalizer.seven_not_conjugate_square (j a) (j b)
  · rw [← map_pow, ha, map_one]
  · exact fun h => hane (hj (h.trans j.map_one.symm))
  · simpa only [map_mul, map_inv, map_pow] using congrArg j hab

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification
