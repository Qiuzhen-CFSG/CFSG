module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Actions
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.BinaryFlag

/-!
# The recognition sections on the original binary flag

For n=1 the seed, its H-closure, and the three marked conjugators are
literally those of Section 12.8. The results below apply the constructed
elementary sections, lower direct sum and descended quotient actions to
those groups. Full I-invariance remains with the projective recognition
branch; no new ambient normality or S₃≤W assumption is made.

Source: Aschbacher–Smith, G.2.5(6–7) and 12.8.8(4–5),
printed pp.335–336 and 851–852.
-/

@[expose] public section
open Subgroup
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition
open Setup
open CFSG.Quasithin.Chapter12.Section08 (InvariantFlag)
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G}

/-- The lower direct sum for the original three-conjugate binary flag. -/
theorem binary_flag_lower_section (F : InvariantFlag T V 3)
    (L : Subgroup G) (g h : G)
    (d : LinearThree.Hypothesis (binarySetup F L) (ZMod 2) 1 g h)
    (hUT : F.U ≤ (T : Subgroup G))
    (hf : (frattini F.U).map F.U.subtype ≤ F.Vi 1)
    (hLI : L ≤ (F.U ⊔ conjugate F.U g) ⊔ conjugate F.U h) :
    letI := Hypothesis.lower_normal d hUT hf hLI
    let A := lowerImage (binarySetup F L) g h
      (W (binarySetup F L) g h ⊓ conjugate (W (binarySetup F L) g h) g)
    let B := lowerImage (binarySetup F L) g h
      (W (binarySetup F L) g h ⊓ conjugate (W (binarySetup F L) g h) h)
    let C := lowerImage (binarySetup F L) g h
      (conjugate (W (binarySetup F L) g h) g ⊓ conjugate (W (binarySetup F L) g h) h)
    IsElementaryAbelian 2 (LowerQuotient (binarySetup F L) g h) ∧
      Disjoint A B ∧ IsCompl (A ⊔ B) C := by
  let := Hypothesis.lower_normal d hUT hf hLI
  exact ⟨Hypothesis.lower_elementary d hUT hf hLI,
    Hypothesis.lower_marked_direct d hUT hf hLI⟩

/-- The original upper flag quotient and its genuine starred action.
The marked W₀ is only mapped to this quotient, never divided by a
subgroup asserted to lie in W₀. -/
theorem binary_flag_upper_action (F : InvariantFlag T V 3)
    (L : Subgroup G) (g h : G)
    (d : LinearThree.Hypothesis (binarySetup F L) (ZMod 2) 1 g h)
    (hUT : F.U ≤ (T : Subgroup G))
    (hf : (frattini F.U).map F.U.subtype ≤ F.Vi 1)
    (hLI : L ≤ (F.U ⊔ conjugate F.U g) ⊔ conjugate F.U h)
    (hU : S (binarySetup F L) g h ≤ normalizer (F.U : Set G))
    (hUg : S (binarySetup F L) g h ≤ normalizer (conjugate F.U g : Set G))
    (hUh : S (binarySetup F L) g h ≤ normalizer (conjugate F.U h : Set G))
    (hprod : (S (binarySetup F L) g h : Set G) = (W (binarySetup F L) g h : Set G) *
      (conjugate (W (binarySetup F L) g h) g : Set G) *
      (conjugate (W (binarySetup F L) g h) h : Set G))
    (hN : I (binarySetup F L) g h ≤ normalizer (S₃ (binarySetup F L) g h : Set G))
    (e : StarComparison (binarySetup F L) g h hLI) :
    letI : ((S₃ (binarySetup F L) g h).subgroupOf (S (binarySetup F L) g h)).Normal :=
      normal_subgroupOf_of_le_normalizer (Hypothesis.core_normalizes_third d hLI hU hUg hUh)
    letI := Hypothesis.upper_elementary d hUT hf hLI hU hUg hUh hprod
    ∃ (σ : Representation (ZMod 2) ((binarySetup F L).star L)
        (Additive (UpperQuotient (binarySetup F L) g h)))
      (s : Representation.BinaryConjugationSection (I (binarySetup F L) g h)
        (S (binarySetup F L) g h) (S₃ (binarySetup F L) g h) (σ.comp e.projection)),
      ∀ a : S (binarySetup F L) g h, (s.coordinates a).toAdd =
        Additive.ofMul (QuotientGroup.mk'
          ((S₃ (binarySetup F L) g h).subgroupOf (S (binarySetup F L) g h)) a) :=
  Hypothesis.upper_action d hUT hf hLI hU hUg hUh hprod hN e

/-- The dual layer of that same binary flag uses the same comparison
and retains the literal quotient map as coordinates. -/
theorem binary_flag_lower_action (F : InvariantFlag T V 3)
    (L : Subgroup G) (g h : G)
    (d : LinearThree.Hypothesis (binarySetup F L) (ZMod 2) 1 g h)
    (hUT : F.U ≤ (T : Subgroup G))
    (hf : (frattini F.U).map F.U.subtype ≤ F.Vi 1)
    (hLI : L ≤ (F.U ⊔ conjugate F.U g) ⊔ conjugate F.U h)
    (hU : S (binarySetup F L) g h ≤ normalizer (F.U : Set G))
    (hUg : S (binarySetup F L) g h ≤ normalizer (conjugate F.U g : Set G))
    (hUh : S (binarySetup F L) g h ≤ normalizer (conjugate F.U h : Set G))
    (hgen : S (binarySetup F L) g h =
      (W (binarySetup F L) g h ⊔ conjugate (W (binarySetup F L) g h) g) ⊔
        conjugate (W (binarySetup F L) g h) h)
    (hN : I (binarySetup F L) g h ≤ normalizer (S₃ (binarySetup F L) g h : Set G))
    (e : StarComparison (binarySetup F L) g h hLI) :
    letI := Hypothesis.lower_normal d hUT hf hLI
    letI := Hypothesis.lower_elementary d hUT hf hLI
    ∃ (σ : Representation (ZMod 2) ((binarySetup F L).star L)
        (Additive (LowerQuotient (binarySetup F L) g h)))
      (s : Representation.BinaryConjugationSection (I (binarySetup F L) g h)
        (S₃ (binarySetup F L) g h) (S₂ (binarySetup F L) g h) (σ.comp e.projection)),
      ∀ a : S₃ (binarySetup F L) g h, (s.coordinates a).toAdd =
        Additive.ofMul (QuotientGroup.mk'
          ((S₂ (binarySetup F L) g h).subgroupOf (S₃ (binarySetup F L) g h)) a) :=
  Hypothesis.lower_action d hUT hf hLI hU hUg hUh hgen hN e

end CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition
