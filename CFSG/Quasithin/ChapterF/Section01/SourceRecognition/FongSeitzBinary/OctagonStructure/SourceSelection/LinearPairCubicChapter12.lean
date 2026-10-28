module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.SourceSelection.LinearPairChapter12
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.LinearPairCubicCentralizers

/-!
# Chapter 12 application of the cubic two-linear calculation

The selected two-linear octagon branch already carries both original full
Borel markings and their endpoint quotient squares.  This consumer passes
those literal maps to the source-level cubic centralizer theorem, retaining
the degree alternatives and the resulting two orientations.  No row choice
or ambient completion is inferred here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
open ChapterF.Source.FongSeitzBinary.LinearPanel
open ChapterF.Source.FongSeitzBinary.OctagonStructure
open ChapterF.Source.FongSeitzBinary.ReeSource

variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
  (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
  (split : SplitData Q.tits) (hm : rotationOrder Q = 8)

include D h hmany hn hpsl d hTH e split hm in
/-- The actual selected two-linear Chapter 12 branch supplies the cubic
centralizer calculation on the same quotient and original endpoint maps. -/
theorem rankOne_octagon_selected_linear_cubic_centralizers
    (hbranch : ∃ b, 0 < b ∧ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^b) ∧
      ((Odd n ∧ b = 2*n) ∨ (Odd b ∧ n = 2*b))) :
    (∃ b, 0 < b ∧ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^b) ∧
      ((Odd n ∧ b = 2*n) ∨ (Odd b ∧ n = 2*b)) ∧
      ((Odd n ∧ Even b ∧
        ∃ c : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)),
          orderOf c = 3 ∧
          (∀ w : Weyl Q,
            (c : X ⧸ Q.D) ∈ centralizer (rootAt Q split 0 w : Set (X ⧸ Q.D)) ∧
            rootAt Q split 1 w ⊓
              centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) = ⊥) ∧
          Nat.card (simpleRemainder Q split 0 ⊓
            centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) : Subgroup (X ⧸ Q.D)) =
              (2^n)^3 ∧
          Nat.card (simpleRemainder Q split 1 ⊓
            centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) : Subgroup (X ⧸ Q.D)) =
              (2^n)^4 ∧
          Nat.card (split.U ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) :
            Subgroup (X ⧸ Q.D)) = (2^n)^4) ∨
       (Even n ∧ Odd b ∧
        ∃ c : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)),
          orderOf c = 3 ∧
          (∀ w : Weyl Q,
            (c : X ⧸ Q.D) ∈ centralizer (rootAt Q split 1 w : Set (X ⧸ Q.D)) ∧
            rootAt Q split 0 w ⊓
              centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) = ⊥) ∧
          Nat.card (simpleRemainder Q split 1 ⊓
            centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) : Subgroup (X ⧸ Q.D)) =
              (2^b)^3 ∧
          Nat.card (simpleRemainder Q split 0 ⊓
            centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) : Subgroup (X ⧸ Q.D)) =
              (2^b)^4 ∧
          Nat.card (split.U ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) :
              Subgroup (X ⧸ Q.D)) = (2^b)^4))) := by
  rcases hbranch with ⟨b, hb, hR, hratio⟩
  have hL0 : ClassicalGroup.IsPSL
      (((![L,R] : Fin 2 → Subgroup G) 0) ⧸
        pCore 2 ((![L,R] : Fin 2 → Subgroup G) 0)) 2 (2^n) := by
    change ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n)
    exact hpsl
  have hR1 : ClassicalGroup.IsPSL
      (((![L,R] : Fin 2 → Subgroup G) 1) ⧸
        pCore 2 ((![L,R] : Fin 2 → Subgroup G) 1)) 2 (2^b) := by
    change ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^b)
    exact hR
  obtain ⟨_, _, σ₀, T₀, τ₀, _, _, τ₁, hdata⟩ :=
    rankOne_octagon_linear_pair_panel_data D h hmany hn hpsl d hTH Q e split hm
      (a := n) (b := b) (by omega) hb hL0 hR1
  rcases hdata with ⟨hσ₀, hτ₀, _, _, _, hσ₁, hτ₁, _, _, _, _⟩
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  have hres := original_linear_pair_cubic_centralizers Q split hm 0 1 (by decide)
    n b (by omega) hb e hf τ₀ T₀ hτ₀ τ₁ _ hτ₁
  rcases hres with hres | hres
  · exact ⟨b,hb,hR,hratio,Or.inl hres⟩
  · exact ⟨b,hb,hR,hratio,Or.inr hres⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
