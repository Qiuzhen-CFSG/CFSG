module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.FourCartanOrders
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.MarkedCores
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalCoordinates
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitarySource.CartanApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.LinearThreePresentation

/-!
# U4 Cartan orders from the original elementary radical

The original DGS (11.7)(e) elementary radical supplies the commuting-root
clause of Fong--Seitz (8.1). The two original faithful linear panel marks
then force the exact full Cartan and both Cartan-kernel orders. The same
original elementary radical also kills the Frattini subgroup of the
actual complementary section. Both endpoint orientations and the full
original quotient map are preserved, including q=2 and q=4.

The final applications remove the numerical Cartan premise from the
existing scalar-field construction on the original core. All nonzero
coefficients are realized by actual original conjugating elements. The
faithful panel markings, remainder containment and irreducible action
are retained earlier-source inputs. The local structural producers are
QuadrangleStructure (qt-dgs85-quadrangle-structure); compatible module
realizations, other endpoint labels and remaining Weyl equations stay
with qt-dgs85-unitary-source-recognition. No U5 assertion is inferred
from this elementary U4 radical calculation.

Source: DGS (11.7)(e), pp.174--175; Fong--Seitz I (6A)(b), pp.37--38;
II (8.1)--(8.2), p.197, and the characteristic-two argument on p.201.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}

/-- Exact orders on the same marked quotient, derived from the original
faithful endpoint maps and elementary large-endpoint radical. -/
theorem marked_four_cartan_cards
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      Q.standardAmalgam)
    (h : HypothesisF11 L S) (split : SplitData Q.tits)
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j) (n : ℕ) (hn : 0 < n)
    (μi : (parabolic L S i ⧸ ReeSource.originalPanelKernel (L := L) (S := S) i) ≃*
      PSL2BinaryMatrixGroup n)
    (Ti : Sylow 2 (PSL2BinaryMatrixGroup n))
    (hBi : (ReeSource.originalFaithfulBorel (L := L) (S := S) i).map μi.toMonoidHom = normalizer (Ti : Set _))
    (μj : (parabolic L S j ⧸ ReeSource.originalPanelKernel (L := L) (S := S) j) ≃*
      PSL2BinaryMatrixGroup (2*n))
    (Tj : Sylow 2 (PSL2BinaryMatrixGroup (2*n)))
    (hBj : (ReeSource.originalFaithfulBorel (L := L) (S := S) j).map μj.toMonoidHom = normalizer (Tj : Set _))
    (hV : simpleRemainder Q split j ≤ HexagonStructure.localKernel Q j)
    (he : IsElementaryAbelian 2 ((parabolic L S j).pCoreIn 2)) :
    Nat.card (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) = ((2^n)^2-1)*(2^n-1) ∧
      Nat.card (coreCartan Q i) = (2^n)^2-1 ∧
      Nat.card (coreCartan Q j) = 2^n-1 ∧
      frattini (simpleRemainder Q split j) = ⊥ := by
  have hc := QuadrangleStructure.marked_root_commutator_of_elementary_core Q e split i j hij hV he
  have hcards := four_linear_cartan_cards Q split hm i j hij n hn
    (ReeSource.faithfulModelMarking Q e h i μi) Ti
    (ReeSource.faithfulModelMarking_borel Q e h i μi _ hBi)
    (ReeSource.faithfulModelMarking Q e h j μj) Tj
    (ReeSource.faithfulModelMarking_borel Q e h j μj _ hBj) hc
    (LinearThreePresentation.borel_core_eq_bot Q e h)
  let := QuadrangleStructure.marked_remainder_elementary Q e split j hV he
  let : Fact (IsPGroup 2 (simpleRemainder Q split j)) := ⟨IsElementaryAbelian.isPGroup 2 _⟩
  exact ⟨hcards.1,hcards.2.1,hcards.2.2,frattini_eq_bot_of_isElementaryAbelian (p := 2)⟩

variable (Q : SourceQuotient L S) (h : HypothesisF11 L S) (split : SplitData Q.tits)
variable (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j) (n : ℕ) (hn : 0 < n)
variable (μi : (parabolic L S i ⧸ ReeSource.originalPanelKernel (L := L) (S := S) i) ≃*
  PSL2BinaryMatrixGroup n)
variable (Ti : Sylow 2 (PSL2BinaryMatrixGroup n))
variable (hBi : (ReeSource.originalFaithfulBorel (L := L) (S := S) i).map μi.toMonoidHom = normalizer (Ti : Set _))
variable (μj : (parabolic L S j ⧸ ReeSource.originalPanelKernel (L := L) (S := S) j) ≃*
  PSL2BinaryMatrixGroup (2*n))
variable (Tj : Sylow 2 (PSL2BinaryMatrixGroup (2*n)))
variable (hBj : (ReeSource.originalFaithfulBorel (L := L) (S := S) j).map μj.toMonoidHom = normalizer (Tj : Set _))
variable (hV : simpleRemainder Q split j ≤ HexagonStructure.localKernel Q j)
variable (he : IsElementaryAbelian 2 ((parabolic L S j).pCoreIn 2))

include h hm hij hn μi Ti hBi μj Tj hBj hV he

/-- Both orders and the actual Frattini kernel on the original SourceQuotient. -/
theorem original_four_cartan_cards :
    Nat.card (Q.tits.B ⊓ Q.tits.N : Subgroup ((generated L S) ⧸ Q.D)) = ((2^n)^2-1)*(2^n-1) ∧
      Nat.card (coreCartan Q i) = (2^n)^2-1 ∧
      Nat.card (coreCartan Q j) = 2^n-1 ∧
      frattini (simpleRemainder Q split j) = ⊥ :=
  marked_four_cartan_cards Q (originalMarkedIso Q) h split hm i j hij n hn
    μi Ti hBi μj Tj hBj hV he

variable [Representation.IsIrreducible (coreActorRepresentation Q split j hV)]

/-- The original source now supplies the coefficient-field order and every
nonzero scalar lift; no numerical Cartan premise is retained. -/
theorem original_four_coefficient_field :
    Nat.card (CoreCoefficientField Q split j hV n) = 2^n ∧
      Function.Bijective (coreCoefficientUnits Q split j hV n
        (original_four_cartan_cards Q h split hm i j hij n hn μi Ti hBi μj Tj hBj hV he).2.2.1) := by
  have hcard := (original_four_cartan_cards Q h split hm i j hij n hn μi Ti hBi μj Tj hBj hV he).2.2.1
  have hc := MarkedLocal.parabolic_core_selfCentralizing Q (originalMarkedIso Q) h j
  exact ⟨coreCoefficientField_card Q split j hV n hn hc (hcard ▸ dvd_refl _),
    coreCoefficientUnits_bijective Q split j hV n hn hc hcard⟩

/-- Each constructed nonzero coefficient is conjugation by a representative
in generated L S, with Q.q and the original Frattini projection retained. -/
theorem original_four_nonzero_coefficient_conjugation
    (c : CoreCoefficientField Q split j hV n) (hc : c ≠ 0) :
    ∃ a : generated L S, Q.q a ∈ coreCartan Q j ∧
      ∀ (v : generated L S) (hv : Q.q v ∈ simpleRemainder Q split j),
      ∃ w : simpleRemainder Q split j,
        (w : (generated L S) ⧸ Q.D) = Q.q (a*v*a⁻¹) ∧
        (coreActorRepresentation Q split j hV).asModuleEquiv
          (c • (coreActorRepresentation Q split j hV).asModuleEquiv.symm
            (Additive.ofMul (QuotientGroup.mk' (frattini (simpleRemainder Q split j)) ⟨Q.q v,hv⟩))) =
          Additive.ofMul (QuotientGroup.mk' (frattini (simpleRemainder Q split j)) w) :=
  original_nonzero_coefficient_conjugation Q split j hV h n hn
    (original_four_cartan_cards Q h split hm i j hij n hn μi Ti hBi μj Tj hBj hV he).2.2.1 c hc

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource
