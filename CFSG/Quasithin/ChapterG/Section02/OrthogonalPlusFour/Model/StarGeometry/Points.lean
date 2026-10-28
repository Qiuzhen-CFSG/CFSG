module

public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Model.Points
public import Theory.Representation.OrthogonalFourPlusMatrix.PrimeFieldTwo.Stabilizers

/-!
# The marked singular point and its full stabilizer in G.2.6

The marked point has order two, so fixing its unique nonzero vector is the
same as fixing it pointwise. Its stabilizer contains the actual U-image of
order four. The nonsingular stabilizer has order six, excluding that orbit;
the singular stabilizer has order four, giving equality with the U-image.
Source: Aschbacher–Smith, G.2.6, printed p.336, first proof paragraph.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
open Setup ClassicalOrthogonal.FourPlusMatrix
namespace Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G} (d : Hypothesis D g)
include d

/-- A nonzero marked vector determines the entire order-two point. -/
theorem pointStabilizer_eq_vector_stabilizer (z : D.V₁) (hz : d.pointVector z ≠ 0) :
    d.pointStabilizer = PrimeFieldTwo.stabilizer (d.pointVector z) := by
  obtain ⟨w, _, hw⟩ := (Nat.card_eq_two_iff' (1 : D.V₁)).mp d.point_card
  have hz1 : z ≠ 1 := fun he => hz ((d.pointVector_eq_zero_iff z).mpr he)
  ext a
  rw [d.mem_pointStabilizer, PrimeFieldTwo.mem_stabilizer]
  constructor
  · exact fun h => h z
  · intro ha v
    by_cases hv : v = 1
    · subst v
      simp [pointVector]
    · have he : v = z := (hw v hv).trans (hw z hz1).symm
      simpa only [he] using ha

/-- Every vector of the source point is singular for the actual determinant form. -/
theorem pointVector_singular (z : D.V₁) :
    determinantForm (d.pointVector z) = 0 := by
  rw [determinantForm_apply]
  by_cases hz : d.pointVector z = 0
  · simp [hz]
  · by_contra hn
    have hle := d.modelImage_U_le_pointStabilizer
    rw [d.pointStabilizer_eq_vector_stabilizer z hz] at hle
    have hdiv := card_dvd_of_le hle
    rw [d.modelImage_U_card, PrimeFieldTwo.stabilizer_card _ hz, if_neg hn] at hdiv
    norm_num at hdiv

/-- The original marked U-image is the full point stabilizer, with no extra premise. -/
theorem modelImage_U_eq_pointStabilizer : d.modelImage D.U = d.pointStabilizer := by
  obtain ⟨z, hz⟩ := d.exists_pointVector_ne_zero
  apply eq_of_le_of_card_ge d.modelImage_U_le_pointStabilizer
  rw [d.modelImage_U_card, d.pointStabilizer_eq_vector_stabilizer z hz,
    PrimeFieldTwo.stabilizer_card _ hz,
    if_pos ((determinantForm_apply _).symm.trans (d.pointVector_singular z))]

/-- A nonzero marked vector gives the corresponding single-vector stabilizer. -/
theorem modelImage_U_eq_vector_stabilizer (z : D.V₁) (hz : d.pointVector z ≠ 0) :
    d.modelImage D.U = PrimeFieldTwo.stabilizer (d.pointVector z) :=
  d.modelImage_U_eq_pointStabilizer.trans (d.pointStabilizer_eq_vector_stabilizer z hz)

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
