module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Transport
public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import Stellmacher.ElementaryAbelianMaxJFixedCenter

/-!
# Baumann images detected by fixed vectors

The elementary subgroup C_W(J(R)) lies in Ω₁(Z(J(R))) when W ≤ R.
Consequently Baum(R) centralizes it. If the image of its centralizer in R
is already contained in J(R)'s image, both images agree. This is the
fixed-vector argument underlying B.2.20, and does not require its stronger
unique-offender premise. The final application retains the literal plus map
on W_K in the ordinary A₇ branch of 13.6.22 (printed p.932).
-/
@[expose] public section
open Subgroup Stellmacher
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem thompson_le_baumann (R : Subgroup G) :
    elementaryAbelianMaxJ R ≤ ChapterB.baumann R := by
  have hJR : elementaryAbelianMaxJ R ≤ R := sSup_le fun _ hA => hA.1
  refine le_inf hJR ?_
  intro j hj
  rw [mem_centralizer_iff]
  intro w hw
  obtain ⟨wJ, hwJ, rfl⟩ := hw
  obtain ⟨wZ, _, rfl⟩ := hwJ
  exact congrArg Subtype.val
    ((mem_center_iff.mp wZ.property) ⟨j, hj⟩).symm

/-- The source fixed vectors bound Baum(R) in the original group. -/
theorem baumann_le_fixed_centralizer (R W : Subgroup G)
    [IsElementaryAbelian 2 W] (hWR : W ≤ R) :
    ChapterB.baumann R ≤ R ⊓ centralizer
      (W ⊓ centralizer (elementaryAbelianMaxJ R : Set G) : Set G) := by
  let F := W ⊓ centralizer (elementaryAbelianMaxJ R : Set G)
  let : IsElementaryAbelian 2 F := {
    toIsMulCommutative := ⟨⟨fun x y => Subtype.ext (congrArg (fun w : W => (w : G))
      (mul_comm (⟨x, x.property.1⟩ : W) ⟨y, y.property.1⟩))⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x =>
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (A := W) x x.property.1)) }
  have hF : F ≤ ChapterB.thompsonAlpha R :=
    elementary_centralizer_maxJ_le_omegaCenter R F (inf_le_left.trans hWR) inf_le_right
  exact inf_le_inf_left _ (centralizer_le hF)

/-- Apply fixed-vector detection through the literal plus projection.
The remaining premise concerns the fixed-vector centralizer, not Baum(R). -/
theorem baumann_plus_eq_of_fixed_centralizer
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    [IsElementaryAbelian 2 (WK K L T z v)]
    (hWT : WK K L T z v ≤ Tv T v)
    (hfixed : plusImage K L T z v hL hz
      (Tv T v ⊓ centralizer
        (WK K L T z v ⊓ centralizer
          (elementaryAbelianMaxJ (Tv T v) : Set G) : Set G)) ≤
      plusImage K L T z v hL hz (elementaryAbelianMaxJ (Tv T v))) :
    plusImage K L T z v hL hz (ChapterB.baumann (Tv T v)) =
      plusImage K L T z v hL hz (elementaryAbelianMaxJ (Tv T v)) := by
  apply le_antisymm
  · exact (map_mono (comap_mono
      (baumann_le_fixed_centralizer (Tv T v) (WK K L T z v) hWT))).trans hfixed
  · exact map_mono (comap_mono (thompson_le_baumann (Tv T v)))

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking
end
