module

public import Theory.GroupTheory.PCoreImage

/-!
# Filling the radical of the local linear stabilizer

If P=P₀R with R abelian, any nontrivial P₀-normal subgroup B of R is
also P-normal. Irreducibility on R forces B=R, and hence P=P₀. Applying
this to B=O₂(P₀) gives the final group-theoretic step of 14.7.56.

The concrete linear calculation still has to identify R=O₂(P), prove the
cover P=P₀R, and supply the nontrivial core in the Y-image. These hypotheses
are deliberately explicit here and are not asserted as source conclusions.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
14.7.56, printed p.1066.
-/

public section
namespace CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics
open Subgroup
variable {A : Type*} [Group A]

/-- An abelian radical and a nontrivial normalized subgroup fill the whole
radical when the ambient stabilizer acts irreducibly on it. -/
theorem stabilizer_saturation (P₀ R P B : Subgroup A)
    (hcover : P₀ ⊔ R = P) (hBR : B ≤ R) (hB₀ : B ≤ P₀) (hne : B ≠ ⊥)
    (hnorm : P₀ ≤ normalizer B) (habelian : R ≤ centralizer (R : Set A))
    (hirr : ∀ C : Subgroup A, C ≤ R → P ≤ normalizer C → C = ⊥ ∨ C = R) :
    P₀ = P := by
  have hRB : R ≤ normalizer B :=
    (habelian.trans (centralizer_le hBR)).trans (centralizer_le_normalizer _)
  have hPB : P ≤ normalizer B := by
    rw [← hcover]
    exact sup_le hnorm hRB
  have he : B = R := (hirr B hBR hPB).resolve_left hne
  have hR₀ : R ≤ P₀ := he ▸ hB₀
  rw [← hcover, sup_eq_left.mpr hR₀]

/-- The last sentence of the printed 14.7.56 proof, applied to the actual
local-action image P₀ and the nontrivial two-core supplied by the Y-action.
The linear model must still supply the cover and radical irreducibility. -/
theorem local_image_saturation (P₀ Y₀ R P : Subgroup A)
    (hcover : P₀ ⊔ R = P) (hcore : P₀.pCoreIn 2 ≤ R)
    (hYcore : Y₀.pCoreIn 2 ≤ P₀.pCoreIn 2) (hYne : Y₀.pCoreIn 2 ≠ ⊥)
    (habelian : R ≤ centralizer (R : Set A))
    (hirr : ∀ C : Subgroup A, C ≤ R → P ≤ normalizer C → C = ⊥ ∨ C = R) :
    P₀ = P := by
  apply stabilizer_saturation P₀ R P (P₀.pCoreIn 2) hcover hcore (pCoreIn_le 2 P₀)
  · intro he
    exact hYne (le_bot_iff.mp (he ▸ hYcore))
  · exact P₀.le_normalizer.trans (normalizer_le_normalizer_characteristic_image P₀ (pCore 2 P₀))
  · exact habelian
  · exact hirr

end CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics
