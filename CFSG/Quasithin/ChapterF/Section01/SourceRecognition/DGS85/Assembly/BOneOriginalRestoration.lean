module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.IntrinsicBOne.Recognition
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.LinearNativeDiagram
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.BinaryBorel
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.DefiningSylow
public import Theory.SpecificGroups.SymplecticFour.Sylow.FlagCounts

/-!
# Original restoration of the intrinsic noncommuting b=1 branch

Intrinsic recognition supplies the marked reduced A₂ or C₂ row. At field order
two the whole model Borel is a two-group, so the original Sylow subgroup and
both original endpoints already equal their reductions. In larger fields the
native lifting theorems restore the original pair inside a type-preserving
automorphism extension. Each output contains an isomorphism on the whole
original Borel, both inclusion squares, the chosen orientation, and equality
with the supplied marking on every reduced element.

Only the original F.1.11, critical-pair, noncommuting and b=1 hypotheses enter
the final theorem. No solvability, perfectness or prepared Chapter 12 pair is
required. This is the b=1 contribution to Theorem A(a); it does not identify
the ambient source completion with its finite local model.

Source: DGS, *Groups and Graphs* (1985), Theorem A, pp.99–100, and
(15.1)–(15.2), pp.225–228, following intrinsic Chapter 7–10 recognition.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneOriginalRestoration
open Reduction SuzukiContainment OriginalExtension SourceCompletion.UnitaryNonbinary
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- A binary restoration keeps the supplied reduced maps unchanged, including
its middle map on the full reduced Borel. The new isomorphism has the entire
original Borel as its domain and satisfies both inclusion squares. -/
@[expose] def BinaryRestored (h : HypothesisF11 L S)
    {A B C : Type*} [Group A] [Group B] [Group C] {α : RankTwoAmalgam A B C}
    (e : Iso (reducedAmalgam L S) α) : Prop :=
  ∃ f : Iso (originalAmalgam L S) α,
    (∀ x : parabolic L (reducedSylow L S) 0,
      f.left (inclusion (reduced_parabolic_le h 0) x) = e.left x) ∧
    (∀ b : commonBorel L (reducedSylow L S),
      f.middle (inclusion (reduced_commonBorel_le h) b) = e.middle b) ∧
    (∀ x : parabolic L (reducedSylow L S) 1,
      f.right (inclusion (reduced_parabolic_le h 1) x) = e.right x)

/-- The nonbinary restoration keeps the entire original overlap and both
inclusion squares in a type-preserving extension of the literal native pair.
Each reduced map agrees with its given marking followed by conjugation. -/
@[expose] def ExtensionRestored (h : HypothesisF11 L S)
    {X : Type*} [Group X] {P B Q : Subgroup X} {hBP : B ≤ P} {hBQ : B ≤ Q}
    (e : Iso (reducedAmalgam L S) (ofSubgroups P B Q hBP hBQ)) : Prop :=
  ∃ E : SourceExtension P Q, ∃ f : Iso (originalAmalgam L S) E.amalgam,
    (∀ x : parabolic L (reducedSylow L S) 0,
      (f.left (inclusion (reduced_parabolic_le h 0) x) : MulAut X) =
        MulAut.conj (e.left x : X)) ∧
    (∀ x : parabolic L (reducedSylow L S) 1,
      (f.right (inclusion (reduced_parabolic_le h 1) x) : MulAut X) =
        MulAut.conj (e.right x : X)) ∧
    (∀ b : commonBorel L (reducedSylow L S),
      (f.middle (inclusion (reduced_commonBorel_le h) b) : MulAut X) =
        MulAut.conj (e.middle b : X))

private theorem binary_restored (h : HypothesisF11 L S)
    {A B C : Type*} [Group A] [Group B] [Group C] {α : RankTwoAmalgam A B C}
    (e : Iso (reducedAmalgam L S) α)
    (hB : IsPGroup 2 (commonBorel L (reducedSylow L S))) : BinaryRestored h e :=
  ⟨(BinaryBorel.originalIsoReduced h hB).trans e,
    BinaryBorel.originalIsoReduced_trans_reduced h hB e⟩

private theorem linear_binary_borel (F : Type*) [Field F] [Finite F]
    (hF : Nat.card F = 2) : IsPGroup 2 (Matrix.PSL3.LinearThree.borel F) := by
  have hB : IsPGroup 2 (Matrix.PSL3.LinearThree.borelSL F) := by
    apply IsPGroup.of_card (n := 3)
    rw [Matrix.PSL3.LinearThree.DefiningSylow.card_borelSL, hF]
    norm_num
  exact hB.map (Matrix.PSL3.projection F)

private theorem symplectic_binary_borel (F : Type*) [Field F] [Finite F]
    (hF : Nat.card F = 2) : IsPGroup 2 (Theory.SpecificGroups.SymplecticFour.borel (F := F)) := by
  apply IsPGroup.of_card (n := 4)
  rw [Theory.SpecificGroups.SymplecticFour.card_borel, hF]
  norm_num

/-- Restore a marked linear row at every positive binary field degree. -/
theorem linear_restored (F : Type*) [Field F] [Finite F] [CharP F 2]
    (h : HypothesisF11 L S) {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (point : Bool) (e : Iso (reducedAmalgam L S) (LinearNative.amalgam F point)) :
    (m = 1 ∧ BinaryRestored h e) ∨ (1 < m ∧ ExtensionRestored h e) := by
  by_cases hm₁ : m = 1
  · have htwo : Nat.card F = 2 := by simpa only [hm₁, pow_one] using hF
    exact Or.inl ⟨hm₁, binary_restored h e ((linear_binary_borel F htwo).of_equiv e.middle.symm)⟩
  · have hmgt : 1 < m := by omega
    exact Or.inr ⟨hmgt, LinearNative.exists_original_extension_iso F h hF hmgt point e⟩

/-- Restore a marked symplectic row, including full Sp₄(2) in degree one. -/
theorem symplectic_restored (F : Type*) [Field F] [Finite F] [CharP F 2]
    (h : HypothesisF11 L S) {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (point : Bool) (e : Iso (reducedAmalgam L S) (SymplecticNative.amalgam F point)) :
    (m = 1 ∧ BinaryRestored h e) ∨ (1 < m ∧ ExtensionRestored h e) := by
  by_cases hm₁ : m = 1
  · have htwo : Nat.card F = 2 := by simpa only [hm₁, pow_one] using hF
    exact Or.inl ⟨hm₁, binary_restored h e ((symplectic_binary_borel F htwo).of_equiv e.middle.symm)⟩
  · have hmgt : 1 < m := by omega
    exact Or.inr ⟨hmgt, SymplecticNative.exists_original_extension_iso F h hF hmgt point e⟩

/-- Full original restoration from the unchanged intrinsic b=1 hypotheses.
The reduced witness and every restriction survive in the conclusion. -/
theorem small_original_comparison_of_critical_bOne
    (h : HypothesisF11 L S) {v w : Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) v w)
    (hne : ⁅Z (reducedFamily L S) v, Z (reducedFamily L S) w⁆ ≠ ⊥)
    (hb : b (reducedFamily L S) = 1) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (m : ℕ), 0 < m ∧ Nat.card F = 2^m ∧
      ((∃ (point : Bool) (e : Iso (reducedAmalgam L S) (LinearNative.amalgam F point)),
          (m = 1 ∧ BinaryRestored h e) ∨ (1 < m ∧ ExtensionRestored h e)) ∨
       (∃ (point : Bool) (e : Iso (reducedAmalgam L S) (SymplecticNative.amalgam F point)),
          (m = 1 ∧ BinaryRestored h e) ∨ (1 < m ∧ ExtensionRestored h e))) := by
  obtain ⟨F,_,_,_,m,hm,hF,he⟩ := IntrinsicBOne.small_comparison_of_critical_bOne h hc hne hb
  refine ⟨F,inferInstance,inferInstance,inferInstance,m,hm,hF,?_⟩
  rcases he with ⟨point,⟨e⟩⟩ | ⟨point,⟨e⟩⟩
  · exact Or.inl ⟨point,e,linear_restored F h hm hF point e⟩
  · exact Or.inr ⟨point,e,symplectic_restored F h hm hF point e⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneOriginalRestoration
