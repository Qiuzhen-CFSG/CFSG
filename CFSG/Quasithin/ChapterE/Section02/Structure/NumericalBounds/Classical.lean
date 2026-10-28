module
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.SourceValues
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.G2.HigherUpper.SolvableKernel
public import CFSG.Quasithin.ChapterE.Section02.Structure.Sporadic.Reduction
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# Classical numerical upper bounds on the original minimal parabolic

The original normal C-component has a simple image in the actual star
quotient H/J. Its Sylow supplement and the core-free minimal-parabolic
structure identify that image with F*(H/J). The proved PSL₂, PSU₃ and PSL₃
values therefore give generation at the model exponent in H/J.

The maximal core J is solvable by B.6.8. Positive-rank E-generation lifts
through this full solvable kernel, including its possible odd central part,
and gives n(H) ≤ f. No equality between the parameters of H and H/J is used.

Source: Aschbacher–Smith, E.1.10–E.1.14 and the normal classical alternatives
of E.2.2, printed pp.212–216. This supplies the upper bound needed by the
field-indexed Cartan consumer while preserving the older exact-value interface.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Structure.NumericalBounds
universe u
variable {H : Type u} [Group H] [Finite H] {κ : GroupClass.{u}}

/-- Generation at the positive parameter of the literal star quotient lifts
through the actual solvable maximal core, not merely through O₂(H). -/
theorem isEGenerated_of_star_parameter (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) {f : ℕ} (hf : 0 < f)
    (he : generationParameter (H ⧸ ChapterB.minimalParabolicCore T hP) = f) :
    IsEGenerated f H := by
  let J := ChapterB.minimalParabolicCore T hP
  let : Group.IsSolvable J := ChapterB.minimalParabolic_core_solvable T hP
  apply IsEGenerated.of_normal_solvable_subgroup hf J
  have hh := isEGenerated_generationParameter_of_pos (G := H ⧸ J) (by rw [he]; exact hf)
  rwa [he] at hh

/-- In the normal classical branches, E.1.14 applies to the actual simple
image K* = F*(H/J), retaining the original quotient and Sylow maps. -/
theorem normal_classical_star_value
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) {f : ℕ}
    (hm :
      (2 ≤ f ∧ ClassicalGroup.IsPSL
        (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 2 (2 ^ f)) ∨
      (2 ≤ f ∧ ClassicalGroup.IsPSU
        (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 3 (2 ^ f)) ∨
      (0 < f ∧ ClassicalGroup.IsPSL
        (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 3 (2 ^ f))) :
    generationParameter (H ⧸ ChapterB.minimalParabolicCore T hP) = f := by
  let J := ChapterB.minimalParabolicCore T hP
  let q := QuotientGroup.mk' J
  let S := T.mapSurjective (QuotientGroup.mk'_surjective J)
  let L := K.map q
  obtain ⟨hLs,hLa,hLn,hLT⟩ := source_normal_simple_image T hP hs K hK hgen
  let : IsSimpleGroup L := hLs
  let : L.Normal := hLn
  have hstar := source_star_minimal_core_free T hP
  have hF := (Sporadic.faithful_normal_structure S hstar.1 hstar.2 L hLa hLT).1
  exact ValuesEvenClassical.source_classical_value (source_star_sqtk hA hH T hP hs)
    L hF.symm S hLT hm

/-- The source-correct upper bound for the original group in all three
normal binary classical branches. -/
theorem normal_classical_upper
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) {f : ℕ}
    (hm :
      (2 ≤ f ∧ ClassicalGroup.IsPSL
        (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 2 (2 ^ f)) ∨
      (2 ≤ f ∧ ClassicalGroup.IsPSU
        (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 3 (2 ^ f)) ∨
      (0 < f ∧ ClassicalGroup.IsPSL
        (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 3 (2 ^ f))) :
    generationParameter H ≤ f := by
  have hf : 0 < f := by rcases hm with h | h | h <;> have := h.1 <;> omega
  exact generationParameter_le hf (isEGenerated_of_star_parameter T hP hf
    (normal_classical_star_value hA hH T hP hs K hK hgen hm))

end CFSG.Quasithin.ChapterE.Structure.NumericalBounds
