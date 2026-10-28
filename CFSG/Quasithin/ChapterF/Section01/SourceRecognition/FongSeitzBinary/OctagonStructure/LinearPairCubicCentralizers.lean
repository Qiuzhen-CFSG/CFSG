module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.LinearPairDegrees
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.CubicRadicalCentralizers

/-!
# Cubic centralizers from the two original linear panels

The even-degree panel supplies an element of order three in the actual
Cartan. Its action is trivial on every odd-degree root and fixed-point-free
on every even-degree root. Unique positive-root coordinates then give
orders q³ and q⁴ in the two radicals, and q⁴ in the full unipotent group.
The original F.1.1 application transports both full Borel markings through
the same amalgam isomorphism and proves the required Borel-core condition.
Degree one on the smaller side and both orientations remain included.

Source: Fong--Seitz I (6G), pp.49--51. This establishes the root centralizer
calculation; the terminal exclusion still needs its representation argument.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
open ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- The two faithful marked panels construct a single cubic actor with the
exact fixed root groups and radical orders on this quotient. -/
theorem linear_pair_cubic_centralizers
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    (a b : ℕ) (ha : Odd a) (hb : 0 < b) (heb : Even b)
    (μi : (Endpoint Q i ⧸ panelKernel Q i) ≃* PSL2BinaryMatrixGroup a)
    (Ti : Sylow 2 (PSL2BinaryMatrixGroup a))
    (hBi : (quotientBorel Q i).map μi.toMonoidHom = normalizer (Ti : Set _))
    (μj : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL2BinaryMatrixGroup b)
    (Tj : Sylow 2 (PSL2BinaryMatrixGroup b))
    (hBj : (quotientBorel Q j).map μj.toMonoidHom = normalizer (Tj : Set _))
    (hcore : Q.tits.B.normalCore = ⊥) :
    ∃ c : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)),
      orderOf c = 3 ∧
      (∀ w : Weyl Q,
        (c : X ⧸ Q.D) ∈ centralizer (rootAt Q split i w : Set (X ⧸ Q.D)) ∧
        rootAt Q split j w ⊓
          centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) = ⊥) ∧
      Nat.card (simpleRemainder Q split i ⊓
        centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) : Subgroup (X ⧸ Q.D)) = (2^a)^3 ∧
      Nat.card (simpleRemainder Q split j ⊓
        centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) : Subgroup (X ⧸ Q.D)) = (2^a)^4 ∧
      Nat.card (split.U ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) :
        Subgroup (X ⧸ Q.D)) = (2^a)^4 := by
  obtain ⟨c,hc⟩ := exists_cubic_cartan Q split j b hb heb μj Tj hBj
    (UnitarySource.actorReflection Q split j)
  have hc3 : c^3 = 1 := by rw [←hc, pow_orderOf_eq_one]
  have hE : IsElementaryAbelian 2 (simpleRoot Q split j) := by
    rw [← rootAt_one Q split j]
    exact linear_rootAt_elementary Q split j b μj Tj hBj 1
  have hci : Nat.card (simpleRoot Q split i) = 2^a := by
    simpa only [rootAt_one] using linear_rootAt_card Q split i a μi Ti hBi ha.pos 1
  have hcj : Nat.card (simpleRoot Q split j) = 2^b := by
    simpa only [rootAt_one] using linear_rootAt_card Q split j b μj Tj hBj hb 1
  have hroots (w : Weyl Q) :
      (c : X ⧸ Q.D) ∈ centralizer (rootAt Q split i w : Set (X ⧸ Q.D)) ∧
      rootAt Q split j w ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) = ⊥ :=
    ⟨cubic_centralizes_odd_root Q split i a ha μi Ti hBi
      (UnitarySource.actorReflection Q split i) c hc3 w,
     cubic_root_centralizer_eq_bot Q split i j hij a b ha hb μi Ti hBi μj Tj hBj
      hE hcj (UnitarySource.actorReflection Q split) hcore c hc w⟩
  have horders := octagon_separated_root_centralizer_orders Q split hm i j hij c hroots
  rw [hci] at horders
  exact ⟨c,hc,hroots,horders⟩

variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Original F.1.1 full Borel markings determine the degree orientation and
construct the cubic centralizer calculation, including the binary case. -/
theorem original_linear_pair_cubic_centralizers
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      Q.standardAmalgam)
    (h : HypothesisF11 L S)
    (νi : (parabolic L S i ⧸ originalPanelKernel (L := L) (S := S) i) ≃*
      PSL2BinaryMatrixGroup a)
    (Ti : Sylow 2 (PSL2BinaryMatrixGroup a))
    (hBi : (originalFaithfulBorel (L := L) (S := S) i).map νi.toMonoidHom =
      normalizer (Ti : Set _))
    (νj : (parabolic L S j ⧸ originalPanelKernel (L := L) (S := S) j) ≃*
      PSL2BinaryMatrixGroup b)
    (Tj : Sylow 2 (PSL2BinaryMatrixGroup b))
    (hBj : (originalFaithfulBorel (L := L) (S := S) j).map νj.toMonoidHom =
      normalizer (Tj : Set _)) :
    (Odd a ∧ Even b ∧
      ∃ c : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)),
        orderOf c = 3 ∧
        (∀ w : Weyl Q,
          (c : X ⧸ Q.D) ∈ centralizer (rootAt Q split i w : Set (X ⧸ Q.D)) ∧
          rootAt Q split j w ⊓
            centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) = ⊥) ∧
        Nat.card (simpleRemainder Q split i ⊓
          centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) : Subgroup (X ⧸ Q.D)) = (2^a)^3 ∧
        Nat.card (simpleRemainder Q split j ⊓
          centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) : Subgroup (X ⧸ Q.D)) = (2^a)^4 ∧
        Nat.card (split.U ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) :
          Subgroup (X ⧸ Q.D)) = (2^a)^4) ∨
    (Even a ∧ Odd b ∧
      ∃ c : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)),
        orderOf c = 3 ∧
        (∀ w : Weyl Q,
          (c : X ⧸ Q.D) ∈ centralizer (rootAt Q split j w : Set (X ⧸ Q.D)) ∧
          rootAt Q split i w ⊓
            centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) = ⊥) ∧
        Nat.card (simpleRemainder Q split j ⊓
          centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) : Subgroup (X ⧸ Q.D)) = (2^b)^3 ∧
        Nat.card (simpleRemainder Q split i ⊓
          centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) : Subgroup (X ⧸ Q.D)) = (2^b)^4 ∧
        Nat.card (split.U ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) :
          Subgroup (X ⧸ Q.D)) = (2^b)^4) := by
  have hcore := LinearThreePresentation.borel_core_eq_bot Q e h
  rcases original_linear_pair_oriented_degrees Q split hm i j hij a b ha hb
      e h νi Ti hBi νj Tj hBj with ⟨hoa,heb,_⟩ | ⟨hea,hob,_⟩
  · exact Or.inl ⟨hoa,heb,linear_pair_cubic_centralizers Q split hm i j hij a b hoa hb heb
      (faithfulModelMarking Q e h i νi) Ti (faithfulModelMarking_borel Q e h i νi _ hBi)
      (faithfulModelMarking Q e h j νj) Tj (faithfulModelMarking_borel Q e h j νj _ hBj) hcore⟩
  · exact Or.inr ⟨hea,hob,linear_pair_cubic_centralizers Q split hm j i hij.symm b a hob ha hea
      (faithfulModelMarking Q e h j νj) Tj (faithfulModelMarking_borel Q e h j νj _ hBj)
      (faithfulModelMarking Q e h i νi) Ti (faithfulModelMarking_borel Q e h i νi _ hBi) hcore⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
