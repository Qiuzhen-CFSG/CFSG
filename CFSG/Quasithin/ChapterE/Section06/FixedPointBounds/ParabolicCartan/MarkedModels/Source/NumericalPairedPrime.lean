module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source
public import CFSG.Quasithin.ChapterE.Section02.Structure.NumericalBounds.Paired.PrimeSharp.Original
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# The original paired prime row has parameter at most one

The marked quotient is the literal image of the original C-component in
H/core(M). The sharp paired prime theorem constructs E-generation at one
in H itself, through the full solvable core, and rules out this odd row
whenever the original parameter exceeds one. The hypothesis p>5 preserves
the source boundary: PSL₂(5) is the separate binary field-four row.
Source: Aschbacher–Smith E.2.2 and the numerical input to E.6.27, pp.215–216.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
universe u
variable {H : Type u} [Group H] [Finite H] {κ : GroupClass.{u}}

private theorem seven_le_of_prime_gt_five {p : ℕ} [Fact p.Prime] (hp : 5 < p) : 7 ≤ p := by
  obtain ⟨k,hk⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  omega

theorem paired_prime_isEGenerated_one
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent)
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hn : ¬K.Normal)
    {p : ℕ} [Fact p.Prime] (hp : 5 < p)
    (hm : ClassicalGroup.IsPSL (sourceImage (ChapterB.minimalParabolicMax T hP) K) 2 p) :
    IsEGenerated 1 H :=
  Structure.NumericalBounds.paired_prime_isEGenerated_one hA hH T hP hs K hK hgen hn
    (seven_le_of_prime_gt_five hp) hm

theorem paired_prime_parameter_le_one
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent)
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hn : ¬K.Normal)
    {p : ℕ} [Fact p.Prime] (hp : 5 < p)
    (hm : ClassicalGroup.IsPSL (sourceImage (ChapterB.minimalParabolicMax T hP) K) 2 p) :
    generationParameter H ≤ 1 :=
  Structure.NumericalBounds.paired_prime_upper_one hA hH T hP hs K hK hgen hn
    (seven_le_of_prime_gt_five hp) hm

/-- The literal original E.6 consumer excludes the odd prime row. -/
theorem not_paired_prime_of_parameter_gt_one
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent)
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hn : ¬K.Normal)
    (hparam : 1 < generationParameter H) {p : ℕ} [Fact p.Prime] (hp : 5 < p) :
    ¬ClassicalGroup.IsPSL (sourceImage (ChapterB.minimalParabolicMax T hP) K) 2 p := by
  intro hm
  exact (Nat.not_lt_of_ge (paired_prime_parameter_le_one hA hH T hP hs K hK hgen hn hp hm)) hparam

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
