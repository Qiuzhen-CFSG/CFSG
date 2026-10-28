module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.Opposition
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalCommonField

/-!
# Original marked application of source opposition

The same full-Borel and endpoint marking transports the natural panel models
and discharges the faithful-core hypothesis. This gives independent-root
Cartan separation and the actual simple-lift eighth-power equation on Q.
The marking can be the original or geometric one; X need not be finite.
The explicit preceding rank-one markings and odd degree remain unchanged.

Source: Fong--Seitz I (6H), p.51, and II section 10, p.232.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure (rootAt)
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
open MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 8) (n : ℕ) (hn : Odd n) (m : ℕ)
  (μ₀ : (parabolic L S 0 ⧸ originalPanelKernel (L := L) (S := S) 0) ≃* PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hB₀ : (originalFaithfulBorel (L := L) (S := S) 0).map μ₀.toMonoidHom = normalizer (T : Set _))
  (μ₁ : (parabolic L S 1 ⧸ originalPanelKernel (L := L) (S := S) 1) ≃* SuzukiMatrixGroup m)
  (hB₁ : (originalFaithfulBorel (L := L) (S := S) 1).map μ₁.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
  (s : ∀ i, RootReflection Q split i)

include e h hm hn μ₀ hB₀ μ₁ hB₁ s in
/-- Independent-root separation on the literal original/geometric quotient,
with faithful Borel core discharged by the original marked amalgam. -/
theorem original_ree_independent_root_centralizer_eq_bot
    (i j : Fin 2) (w v : Weyl Q)
    (hne : w⁻¹*Q.simple i*w ≠ v⁻¹*Q.simple j*v) :
    (((Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) ⊓
      centralizer (rootAt Q split i w : Set (X ⧸ Q.D))) ⊓
      centralizer (rootAt Q split j v : Set (X ⧸ Q.D))) = ⊥ :=
  ree_independent_root_centralizer_eq_bot Q split hm n hn m
    (faithfulModelMarking Q e h 0 μ₀) T (faithfulModelMarking_borel Q e h 0 μ₀ _ hB₀)
    (faithfulModelMarking Q e h 1 μ₁) (faithfulModelMarking_borel Q e h 1 μ₁ _ hB₁)
    s (LinearThreePresentation.borel_core_eq_bot Q e h) i j w v hne

include e h hm hn μ₀ hB₀ μ₁ hB₁ s in
/-- The original source simple representatives satisfy the literal eighth-power
relation in N; the full Borel marking and both endpoints are unchanged. -/
theorem original_ree_reflection_product_eight (a b : Q.tits.N)
    (ha : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) a = Q.simple 0)
    (hb : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) b = Q.simple 1) :
    (a*b)^8 = 1 :=
  ree_reflection_product_eight Q split hm n hn m
    (faithfulModelMarking Q e h 0 μ₀) T (faithfulModelMarking_borel Q e h 0 μ₀ _ hB₀)
    (faithfulModelMarking Q e h 1 μ₁) (faithfulModelMarking_borel Q e h 1 μ₁ _ hB₁)
    s (LinearThreePresentation.borel_core_eq_bot Q e h) a b ha hb

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
