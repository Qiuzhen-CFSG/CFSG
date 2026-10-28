module

public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Assembly

/-!
# The assembled G.2.4 applications in §13.5

The substitution from 13.5.14 uses V₃ as the seed and V as the orthogonal
module. All internal G.2.4 premises are discharged here. Relative normality
of the original L₁ in H supplies both terminal hypotheses for 13.5.15.
The resulting quaternion factors lie in the original H-closure U_H and
have common center V₁. The same source setup also gives the count in
13.5.22 and the elementary second layer used in 13.5.25.

The chapter owner supplies its source setup, the span and residual identities,
and the genuine earlier G.1.3 implication; no core or block conclusion is
assumed. Other conclusions of 13.5.15 remain with that chapter's assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.5.14–15 and 13.5.22–25, printed pp.919–920,924–925.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterG.Section02.AlternatingFive
open Setup Recognition Recognition.ProjectiveGeometry
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The literal G.2.4(8) deduction in 13.5.15, with all earlier-clause inputs
constructed. Normality is in H, and L₁ is the original subgroup. -/
theorem chapter13_block_of_local_normal
    (V₁ V₃ V Lminus T H L₁ U_H K : Subgroup G) (g : G)
    (d : Hypothesis (chapter13Setup V₁ V₃ Lminus T H) g)
    (hrec : RecognitionInput.{0,u} F4)
    (hspan : conjugateSpanBy V₁ Lminus = V)
    (hresidual : L₁ = (chapter13Setup V₁ V₃ Lminus T H).L₁)
    (hn : (L₁.subgroupOf H).Normal)
    (hU : U_H = conjugateSpanBy V₃ H)
    (hK : K = U_H ⊔ conjugate U_H g) :
    K = Lminus ∧ ChapterC.IsAlternatingBlock K 5 ∧ K.pCoreIn 2 = V ∧
      U_H = ⁅U_H, L₁⁆ ∧ U_H = L₁.pCoreIn 2 ∧
      Nonempty (QuaternionCentralProductData U_H) ∧
      Nonempty (U_H ≃* QuaternionCentralProduct.Model) := by
  let := d.second_normal_in_core d.L_le_I
  obtain ⟨s, ⟨e⟩⟩ := d.exists_earlierUpper hrec
  exact chapter13_terminal_block V₁ V₃ V Lminus T H L₁ U_H K g d
    d.earlierStructure e hspan hresidual hn hU hK

/-- The actual factor embeddings and diagonal-quotient map for U_H in
13.5.15(5), with common center the original point V₁. -/
theorem chapter13_quaternion_of_local_normal
    (V₁ V₃ Lminus T H L₁ U_H : Subgroup G) (g : G)
    (d : Hypothesis (chapter13Setup V₁ V₃ Lminus T H) g)
    (hrec : RecognitionInput.{0,u} F4)
    (hresidual : L₁ = (chapter13Setup V₁ V₃ Lminus T H).L₁)
    (hn : (L₁.subgroupOf H).Normal)
    (hU : U_H = conjugateSpanBy V₃ H) :
    ∃ q : QuaternionCentralProductData U_H,
      (q.left ⊓ q.right).map U_H.subtype = V₁ ∧
      ∃ (eL : q.left ≃* QuaternionGroup 2) (eR : q.right ≃* QuaternionGroup 2)
        (f : QuaternionCentralProduct.Model ≃* U_H),
        ∀ x y : QuaternionGroup 2,
          f (QuotientGroup.mk' QuaternionCentralProduct.diagonalCenter (x, y)) =
            eL.symm x * eR.symm y := by
  let := d.second_normal_in_core d.L_le_I
  obtain ⟨s, ⟨e⟩⟩ := d.exists_earlierUpper hrec
  exact chapter13_terminal_quaternion_presentation V₁ V₃ Lminus T H L₁ U_H g d
    d.earlierStructure e hresidual hn hU

/-- The literal count of 13.5.22, needing no separate structural or natural
module witness. The denominator is V(U_H∩U_Hᵍ). -/
theorem chapter13_source_core_order
    (V₁ V₃ V Lminus T H U_H K : Subgroup G) (g : G)
    (d : Hypothesis (chapter13Setup V₁ V₃ Lminus T H) g)
    (hrec : RecognitionInput.{0,u} F4)
    (hspan : conjugateSpanBy V₁ Lminus = V)
    (hU : U_H = conjugateSpanBy V₃ H)
    (hK : K = U_H ⊔ conjugate U_H g) :
    ∃ s : ℕ, Nat.card (K.pCoreIn 2) =
      2 ^ (4 * s + 4) * V.relIndex (V ⊔ (U_H ⊓ conjugate U_H g)) := by
  subst K
  subst U_H
  let := d.second_normal_in_core d.L_le_I
  obtain ⟨s, c, _, _, _, _, _⟩ := d.source_natural_layer hrec
  exact ⟨s, chapter13_core_order_of_naturalLayer V₁ V₃ V Lminus T H g d
    hspan d.L_le_I c⟩

/-- The elementary layer used in 13.5.25, now with generation proved by
G.2.4(2). This deduction does not need the earlier recognition theorem. -/
theorem chapter13_source_second_elementary
    (V₁ V₃ V Lminus T H U_H : Subgroup G) (g : G)
    (d : Hypothesis (chapter13Setup V₁ V₃ Lminus T H) g)
    (hspan : conjugateSpanBy V₁ Lminus = V)
    (hU : U_H = conjugateSpanBy V₃ H) :
    IsElementaryAbelian 2 (V ⊔ (U_H ⊓ conjugate U_H g) : Subgroup G) := by
  subst U_H
  exact chapter13_second_layer_elementary V₁ V₃ V Lminus T H g d hspan d.L_le_I

end CFSG.Quasithin.ChapterG.Section02.AlternatingFive
