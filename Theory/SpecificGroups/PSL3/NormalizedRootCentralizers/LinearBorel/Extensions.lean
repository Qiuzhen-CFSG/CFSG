module

public import Theory.SpecificGroups.PSL3.NormalizedRootCentralizers.LinearBorel
public import Theory.SpecificGroups.PSL3.NormalizedRootCentralizers.ResidualAction
public import Theory.SpecificGroups.PSL3.OuterSolvable.Coverage
public import Theory.SpecificGroups.PSL3.ExtensionBorel

/-!
# Residual centralizers in the genuine nonsplit linear-three extension

The mixed extension is the full preimage of the cyclic mixed field–diagonal
subgroup under Aut(PSL₃) → Out(PSL₃). Its source `MixedData` retains 6 ∣ n;
the field-size and n > 1 assumptions retain positive binary degree. Applying
the abelian outer-diagonal quotient to D = [D,T] removes the field action on D,
so the coordinate root calculation applies through the original inner embedding.
The whole semilinear Borel is not asserted to have uniform root centralizers.

Source: Aschbacher–Smith, A.3.16–18 and proof of 13.6.6, printed pp.51–52, 927.
-/

public section

open scoped MatrixGroups
open Matrix Subgroup
open Matrix.PSL3.OuterSolvable Matrix.PSL3.LinearThree Matrix.PSL3.ExtensionBorel
open Theory.GroupTheory.AutomorphismExtensionBorel
namespace Matrix.PSL3.NormalizedRootCentralizers
variable {F : Type*} [Field F] [Finite F]

/-- The source residual calculation in the literal mixed outer preimage.
The source degree is positive and divisible by six; the extension is unchanged.
Uniformity is asserted for D = [D,T], not for its entire semilinear Borel. -/
theorem mixed_residual_uniform {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (d : MixedData F n)
    (D T : Subgroup (mixedExtension F d.coefficient d.diagonal)) (hD : ⁅D,T⁆ = D)
    (r : mixedExtension F d.coefficient d.diagonal)
    (hr : r ∈ ((center (unipotent F)).map (unipotent F).subtype).map
      (innerEmbedding (mixedExtension F d.coefficient d.diagonal)
        (inner_le_mixedExtension F d.coefficient d.diagonal)))
    (hne : r ≠ 1) :
    D ⊓ centralizer ({r} : Set (mixedExtension F d.coefficient d.diagonal)) =
      D ⊓ centralizer ((((center (unipotent F)).map (unipotent F).subtype).map
        (innerEmbedding (mixedExtension F d.coefficient d.diagonal)
          (inner_le_mixedExtension F d.coefficient d.diagonal)) :
            Subgroup (mixedExtension F d.coefficient d.diagonal)) :
              Set (mixedExtension F d.coefficient d.diagonal)) := by
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  apply uniform_mapped_center _
    (innerEmbedding_injective _ _ (inner_injective F))
    (mixedExtension F d.coefficient d.diagonal).subtype ?_ D ?_ r hr hne
  · intro b x
    apply Subtype.ext
    ext y
    simp [innerEmbedding]
  · exact commutator_generated_innerDiagonal _ D T hD
      (standard_eq_top_of_two_power_card F (by omega) hF)

end Matrix.PSL3.NormalizedRootCentralizers
