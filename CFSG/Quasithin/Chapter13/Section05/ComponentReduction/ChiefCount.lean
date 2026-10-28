module

public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.ChiefCount.UpperSection
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.ChiefCount.ParabolicSection

/-!
# The source sections and common multiplicity in 13.5.22

G.2.4 supplies one NaturalLayer witness and both order formulas. Its upper
section restricts without loss to the original local two-residual. The real
normal filtration and its marked Borel/core quotient maps are constructed in
the imported modules, and the central middle interval contributes zero.

The remaining work is to refine the restricted natural section into 2s
noncentral binary factors, and the lower orthogonal and parabolic-core
sections into one each. No theorem here asserts the completed count or the
A₆ contradiction before those action calculations have been discharged.
Earlier source setup and G.1.3 recognition are explicit inputs.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.5.22 and 13.5.24, printed pp.924–925 (PDF pp.941–942).
-/

@[expose] public section
open Subgroup NoncentralChiefRefinement Matrix
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.ChiefCount
open ChapterG.Section02 ChapterG.Section02.Setup
open ChapterG.Section02.AlternatingFive
open ChapterG.Section02.AlternatingFive.Recognition
open ChapterG.Section02.AlternatingFive.Recognition.ProjectiveGeometry
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Both source orders and the lossless restriction use one actual NaturalLayer
witness. The denominator remains V(U_H∩U_Hᵍ), with right conjugation. -/
theorem source_orders_with_upper_section
    (V₁ V₃ V Lminus T H U_H : Subgroup G) (g : G)
    (d : Hypothesis (chapter13Setup V₁ V₃ Lminus T H) g)
    (hrec : RecognitionInput.{0,u} F4)
    (hspan : conjugateSpanBy V₁ Lminus = V)
    (hU : U_H = conjugateSpanBy V₃ H)
    (hgen : Lminus = U_H ⊔ conjugate U_H g) :
    let D := chapter13Setup V₁ V₃ Lminus T H
    let := d.second_normal_in_core d.L_le_I
    ∃ (s : ℕ) (c : NaturalLayer D g F4 s d.L_le_I),
      Nat.card (Lminus.pCoreIn 2) =
        2 ^ (4 * (s + 1)) * V.relIndex (V ⊔ (U_H ⊓ conjugate U_H g)) ∧
      Nat.card U_H =
        2 ^ (2 * s + 5) * V.relIndex (V ⊔ (U_H ⊓ conjugate U_H g)) ∧
      Function.Surjective (upperHom d) ∧
      Nonempty (Section (core d) (localCore D) ≃* pCore 2 (Borel d)) ∧
      ∀ (k : D.L₁) (x : Section (second d) (core d)),
        (upperCoordinates d (by simpa only [Setup.I, Setup.U, chapter13Setup, hU] using hgen.symm)
          c (sectionAction (second d) (core d) k x)).toAdd =
        fun j => (c.model (starProjection D (inclusion (residual_le_L D) k))).val *ᵥ
          (upperCoordinates d (by simpa only [Setup.I, Setup.U, chapter13Setup, hU] using hgen.symm)
            c x).toAdd j := by
  let D := chapter13Setup V₁ V₃ Lminus T H
  have hI : D.I g = D.L := by
    change conjugateSpanBy V₃ H ⊔ conjugate (conjugateSpanBy V₃ H) g = Lminus
    rw [← hU]
    exact hgen.symm
  let := d.second_normal_in_core d.L_le_I
  obtain ⟨s, c, _, _, _, hu, hs⟩ := d.source_natural_layer hrec
  refine ⟨s, c, ?_, ?_, upperHom_surjective d hI c, ⟨parabolicSectionEquiv d⟩, ?_⟩
  · change Nat.card ((D.I g).pCoreIn 2) =
      2 ^ (4 * s + 4) * D.VL.relIndex (AlternatingFive.S₂ D g) at hs
    rw [hI] at hs
    change Nat.card (Lminus.pCoreIn 2) =
      2 ^ (4 * s + 4) * (conjugateSpanBy V₁ Lminus).relIndex
        (conjugateSpanBy V₁ Lminus ⊔
          (conjugateSpanBy V₃ H ⊓ conjugate (conjugateSpanBy V₃ H) g)) at hs
    simpa only [hspan, ← hU, Nat.mul_add, Nat.mul_one] using hs
  · change Nat.card (conjugateSpanBy V₃ H) =
      2 ^ (2 * s + 5) * (conjugateSpanBy V₁ Lminus).relIndex
        (conjugateSpanBy V₁ Lminus ⊔
          (conjugateSpanBy V₃ H ⊓ conjugate (conjugateSpanBy V₃ H) g)) at hu
    simpa only [hspan, ← hU] using hu
  · exact upperCoordinates_equivariant d hI c

/-- An actual original-L₁ chief series inside the source's central middle
interval has zero count. No ambient-normality hypothesis is substituted. -/
theorem source_middle_count_zero
    (V₁ V₃ V Lminus T H L₁ U_H : Subgroup G) (g : G)
    (d : Hypothesis (chapter13Setup V₁ V₃ Lminus T H) g)
    (hspan : conjugateSpanBy V₁ Lminus = V)
    (hresidual : L₁ = (chapter13Setup V₁ V₃ Lminus T H).L₁)
    (hU : U_H = conjugateSpanBy V₃ H)
    (t : ChiefSeries L₁)
    (h0 : t.head.val = V.subgroupOf L₁)
    (h1 : t.last.val = (V ⊔ (U_H ⊓ conjugate U_H g)).subgroupOf L₁) :
    t.noncentralTwoCount = 0 := by
  subst L₁
  subst U_H
  apply middle_count_zero d t
  · apply Subtype.ext
    exact h0.trans (congrArg (fun A : Subgroup G => A.subgroupOf _) hspan.symm)
  · apply Subtype.ext
    simpa only [first, second, AlternatingFive.S₂, Setup.VL, Setup.U, chapter13Setup,
      hspan] using h1

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.ChiefCount
