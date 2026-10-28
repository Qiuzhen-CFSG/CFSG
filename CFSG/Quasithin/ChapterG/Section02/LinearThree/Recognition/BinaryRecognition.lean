module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Assembly
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.BinaryFlag
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.BinaryApplication

/-!
# Recognized layers on the original Section 12.8 binary flag

The general construction is applied to the literal binary setup, retaining
its U, the original conjugators, and their generated subgroup. It supplies
both homogeneous models and the marked coordinates used by Section 12.8.
The final application discharges the recognition premise in the existing
series-collapse theorem; only the independent earlier homogeneous cubic
coordinates and the permitted structural and G.1.3 inputs remain explicit.

Source: Aschbacher–Smith, G.2.5(6–7) and 12.8.8(4–5),
printed pp.335–336,851–852.
-/

@[expose] public section
universe uG
open Subgroup
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition
open Setup Projective
open CFSG.Quasithin.Chapter12.Section08 (InvariantFlag)
variable {G : Type uG} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G}
  (flag : InvariantFlag T V 3) (L : Subgroup G) (g h : G)
  (d : LinearThree.Hypothesis (binarySetup flag L) (ZMod 2) 1 g h)

/-- Both actual binary models on the literal Section 12.8 flag, with the
marked interface and full invariance constructed rather than assumed. -/
theorem binary_flag_recognized_layers (hUT : flag.U ≤ (T : Subgroup G))
    (hf : (frattini flag.U).map flag.U.subtype ≤ flag.Vi 1)
    (hLI : L ≤ I (binarySetup flag L) g h)
    (hU : S (binarySetup flag L) g h ≤ normalizer (flag.U : Set G))
    (hUg : S (binarySetup flag L) g h ≤ normalizer (conjugate flag.U g : Set G))
    (hUh : S (binarySetup flag L) g h ≤ normalizer (conjugate flag.U h : Set G))
    (hprod : (S (binarySetup flag L) g h : Set G) = (W (binarySetup flag L) g h : Set G) *
      (conjugate (W (binarySetup flag L) g h) g : Set G) *
      (conjugate (W (binarySetup flag L) g h) h : Set G))
    (e : StarComparison (binarySetup flag L) g h hLI)
    (hrad : Hypothesis.UpperRadicalIdentification d e)
    (recognize : RecognitionImplication.{0, uG, 0, uG} (ZMod 2)) :
    I (binarySetup flag L) g h ≤ normalizer (S₃ (binarySetup flag L) g h : Set G) ∧
    letI := Hypothesis.lower_normal d hUT hf hLI
    letI : ((S₃ (binarySetup flag L) g h).subgroupOf (S (binarySetup flag L) g h)).Normal :=
      normal_subgroupOf_of_le_normalizer (Hypothesis.core_normalizes_third d hLI hU hUg hUh)
    letI := Hypothesis.lower_elementary d hUT hf hLI
    letI := Hypothesis.upper_elementary d hUT hf hLI hU hUg hUh hprod
    ∃ r s : ℕ,
      Nonempty (DualGeometry.MarkedModel.Model d e s) ∧
      Nonempty (NaturalGeometry.Model d e r) ∧
      Nonempty (ChiefFactors.MarkedLayers d hLI r s) := by
  obtain ⟨hN, r, s, lower, upper, _, _, c⟩ :=
    Hypothesis.recognized_layers d hUT hf hLI hU hUg hUh hprod e hrad recognize
  exact ⟨hN, r, s, ⟨lower⟩, ⟨upper⟩, c⟩

/-- The original Section 12.8 collapse, now with the G.2.5 marked models
constructed. The independent 12.8.5 cubic coordinates remain explicit. -/
theorem binary_flag_collapse_of_recognition (hUT : flag.U ≤ (T : Subgroup G))
    (hf : (frattini flag.U).map flag.U.subtype ≤ flag.Vi 1)
    (hLI : L ≤ I (binarySetup flag L) g h)
    (hU : S (binarySetup flag L) g h ≤ normalizer (flag.U : Set G))
    (hUg : S (binarySetup flag L) g h ≤ normalizer (conjugate flag.U g : Set G))
    (hUh : S (binarySetup flag L) g h ≤ normalizer (conjugate flag.U h : Set G))
    (hprod : (S (binarySetup flag L) g h : Set G) = (W (binarySetup flag L) g h : Set G) *
      (conjugate (W (binarySetup flag L) g h) g : Set G) *
      (conjugate (W (binarySetup flag L) g h) h : Set G))
    (e : StarComparison (binarySetup flag L) g h hLI)
    (hrad : Hypothesis.UpperRadicalIdentification d e)
    (recognize : RecognitionImplication.{0, uG, 0, uG} (ZMod 2))
    (x : (binarySetup flag L).L₁) {t : ℕ} (b : ChiefFactors.CubicSpanCoordinates d x t) :
    let J := (flag.U ⊔ conjugate flag.U g) ⊔ conjugate flag.U h
    let W₀ := flag.U ⊓ J.pCoreIn 2
    ((flag.U ⊓ conjugate flag.U g) ⊓ conjugate flag.U h = V) ∧
      (J.pCoreIn 2 : Set G) =
        ((W₀ ⊓ conjugate W₀ g : Subgroup G) : Set G) *
        ((W₀ ⊓ conjugate W₀ h : Subgroup G) : Set G) *
        ((conjugate W₀ g ⊓ conjugate W₀ h : Subgroup G) : Set G) := by
  let := Hypothesis.lower_normal d hUT hf hLI
  let : ((S₃ (binarySetup flag L) g h).subgroupOf (S (binarySetup flag L) g h)).Normal :=
    normal_subgroupOf_of_le_normalizer (Hypothesis.core_normalizes_third d hLI hU hUg hUh)
  obtain ⟨_, r, s, _, _, ⟨c⟩⟩ :=
    binary_flag_recognized_layers flag L g h d hUT hf hLI hU hUg hUh hprod e hrad recognize
  obtain ⟨he, _, hp⟩ :=
    ChiefFactors.binary_flag_series_collapse flag L g h d hUT hf hLI c x b
  exact ⟨he, hp⟩

end CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition
