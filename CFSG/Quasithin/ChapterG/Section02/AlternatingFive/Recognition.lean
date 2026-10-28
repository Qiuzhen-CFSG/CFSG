module

public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Recognition.Assembly
public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Recognition.Cardinality
public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Recognition.SourceInput
public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Chapter13

/-!
# The upper natural-layer branch of G.2.4

The conditional G.2.4(6–7) branch is assembled from genuine G.1.3 and the
explicit earlier structural conclusions. The actual starred Borel, projective
orbit map, root bounds and marked complement are proved. Recognition constructs
the shared NaturalLayer with its representative action identity and actual
coordinates; its W-image is exactly the fixed subgroup of the original U-action.

The same multiplicity gives the exact orders of the W-image, U and S, using
W∩S₂ as the quotient kernel and including multiplicity zero. The final application
constructs the natural layer for the literal H-closure used in Section 13.5.

The enclosing G.2 source owner retains discharge of the displayed structural
inputs and genuine G.1.3. These conditional results do not assert the other
clauses of G.2.4 or replace its orthogonal module by a natural SL₂(4)-module.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.4(6–7), printed pp.334–335, and 13.5.22, printed p.924.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterG.Section02.AlternatingFive
open Setup
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The core-order calculation with the literal V₃-closure from 13.5.14.
The source owner must supply its recognized natural upper layer. -/
theorem chapter13_core_order_of_naturalLayer
    (V₁ V₃ V Lminus T H : Subgroup G) (g : G)
    (d : Hypothesis (chapter13Setup V₁ V₃ Lminus T H) g)
    (hspan : conjugateSpanBy V₁ Lminus = V)
    (hLI : Lminus ≤ conjugateSpanBy V₃ H ⊔ conjugate (conjugateSpanBy V₃ H) g)
    [((S₂ (chapter13Setup V₁ V₃ Lminus T H) g).subgroupOf
      ((chapter13Setup V₁ V₃ Lminus T H).S g)).Normal]
    {F : Type*} [Field F] {s : ℕ}
    (c : NaturalLayer (chapter13Setup V₁ V₃ Lminus T H) g F s hLI) :
    Nat.card ((conjugateSpanBy V₃ H ⊔ conjugate (conjugateSpanBy V₃ H) g).pCoreIn 2) =
      2 ^ (4 * s + 4) * V.relIndex
        (V ⊔ (conjugateSpanBy V₃ H ⊓ conjugate (conjugateSpanBy V₃ H) g)) := by
  have hc := d.core_order_of_naturalLayer hLI c
  change Nat.card ((conjugateSpanBy V₃ H ⊔ conjugate (conjugateSpanBy V₃ H) g).pCoreIn 2) =
    2 ^ (4 * s + 4) * (conjugateSpanBy V₁ Lminus).relIndex
      (conjugateSpanBy V₁ Lminus ⊔
        (conjugateSpanBy V₃ H ⊓ conjugate (conjugateSpanBy V₃ H) g)) at hc
  rwa [hspan] at hc

/-- The literal core-order application in 13.5.22, with the natural layer
constructed by G.1.3 rather than supplied as an extra premise. -/
theorem chapter13_core_order_of_recognition
    (V₁ V₃ V Lminus T H : Subgroup G) (g : G)
    (d : Hypothesis (chapter13Setup V₁ V₃ Lminus T H) g)
    (hspan : conjugateSpanBy V₁ Lminus = V)
    (hrec : Recognition.RecognitionInput.{0,u} Recognition.ProjectiveGeometry.F4)
    (hI : (chapter13Setup V₁ V₃ Lminus T H).I g =
      Lminus ⊔ conjugateSpanBy V₃ H)
    (hcore : (chapter13Setup V₁ V₃ Lminus T H).S g =
      (chapter13Setup V₁ V₃ Lminus T H).I g ⊓ (Lminus ⊔ T).pCoreIn 2)
    (hsplit : (chapter13Setup V₁ V₃ Lminus T H).S g =
      (chapter13Setup V₁ V₃ Lminus T H).W g ⊔
        conjugate ((chapter13Setup V₁ V₃ Lminus T H).W g) g)
    (hVV : V₃ ⊔ conjugate V₃ g = V) :
    ∃ s : ℕ,
      Nat.card ((conjugateSpanBy V₃ H ⊔ conjugate (conjugateSpanBy V₃ H) g).pCoreIn 2) =
        2 ^ (4 * s + 4) * V.relIndex
          (V ⊔ (conjugateSpanBy V₃ H ⊓ conjugate (conjugateSpanBy V₃ H) g)) := by
  let D := chapter13Setup V₁ V₃ Lminus T H
  have hLI : D.L ≤ D.I g := le_sup_left.trans hI.ge
  let := d.second_normal_in_core hLI
  have hVV' : D.V ⊔ conjugate D.V g = D.VL := hVV.trans hspan.symm
  obtain ⟨s, c, _, _, _⟩ :=
    d.natural_upper_layer_of_recognition hrec hI hcore hsplit hVV'
  exact ⟨s, chapter13_core_order_of_naturalLayer V₁ V₃ V Lminus T H g d hspan hLI c⟩

end CFSG.Quasithin.ChapterG.Section02.AlternatingFive
