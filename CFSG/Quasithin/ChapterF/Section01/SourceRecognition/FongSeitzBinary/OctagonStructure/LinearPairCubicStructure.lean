module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.CubicAbelian
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.LinearPairCubicCentralizers
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.LinearPairQuadraticDegrees

/-!
# The original two-linear octagon cubic structure

The original factor quotients construct the full faithful panel markings,
the regular local linear actors, and the separating cubic Cartan element.
Its three-root radical centralizer is abelian of order q³. The associated
perpendicular rank-one groups commute in the same marked quotient. Both
orientations and the smaller binary field are retained.

Source: Fong--Seitz I (6G), printed p.49. The remaining kernel separation
and terminal exclusion are not assumed. The input amalgam isomorphism
retains the original full Borel and both endpoint inclusion squares.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
open MarkedLocal ReeSource
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1)
      inf_le_left inf_le_right) Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)

private theorem binary_marking {Y : Type*} [Group Y] {a : ℕ}
    (ha : 0 < a) (hlinear : ClassicalGroup.IsPSL Y 2 (2^a)) :
    Nonempty (Y ≃* PSL2BinaryMatrixGroup a) := by
  obtain ⟨F,hF,hfin,hcard,⟨μ⟩⟩ := hlinear
  let : Fintype F := Fintype.ofFinite F
  let : Fintype (GaloisField 2 a) := Fintype.ofFinite _
  let θ : F ≃+* GaloisField 2 a := FiniteField.ringEquivOfCardEq (by
    simpa only [Nat.card_eq_fintype_card] using
      hcard.trans (GaloisField.card 2 a ha.ne').symm)
  exact ⟨μ.trans (Atlas.fieldEquivPSL 2 θ)⟩

include e h

private theorem original_linear_local_marking (i : Fin 2)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (μ : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F)) :
    simpleRemainder Q split i ≤ localKernel Q i ∧
      Nonempty (localGroup Q split i ≃* PSL(2,F)) := by
  let := h.finite_local i
  obtain ⟨T,hT⟩ := h.sylow i
  have hK := linear_remainder_le_kernel Q e h split i T hT μ
  have hc : Nat.card (simpleRoot Q split i) = Nat.card (quotientSylow T) := by
    rw [simpleRoot_card_linear Q e h split i T hT μ]
    exact ((Nat.card_congr (linearSylowEquiv i T μ).toEquiv).trans
      ((Nat.card_congr (BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive
        (linearModelSylow i T μ)).symm.toEquiv).trans
          (Nat.card_congr Multiplicative.toAdd))).symm
  have hz : center ((L i) ⧸ pCore 2 (L i)) = ⊥ := by
    apply eq_bot_iff.mpr
    intro z hz
    have hh := MulEquivClass.apply_mem_center μ hz
    change μ z ∈ center PSL(2,F) at hh
    rw [BenderSuzuki.ZD.Linear.psl2_center_eq_bot,mem_bot] at hh
    exact μ.injective (hh.trans μ.map_one.symm)
  exact ⟨hK,⟨(regularFactorLocalEquiv Q e h split i T hT hK hc hz).trans μ⟩⟩

/-- The actual odd-degree factor has an abelian cubic centralizer and commutes
with its perpendicular rank-one group, including degree one. -/
theorem original_oriented_linear_cubic_structure
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    {a b : ℕ} (ha : Odd a) (hb : 0 < b) (heb : Even b)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hj : ClassicalGroup.IsPSL ((L j) ⧸ pCore 2 (L j)) 2 (2^b)) :
    ∃ c : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)),
      orderOf c = 3 ∧
      IsMulCommutative ↥(simpleRemainder Q split i ⊓
        centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D))) ∧
      Nat.card (simpleRemainder Q split i ⊓
        centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) : Subgroup (X ⧸ Q.D)) = (2^a)^3 ∧
      ⁅rankOne Q split i,rightConjugate (rankOne Q split i)
        (representative (Q.simple j*Q.simple i*Q.simple j) : X ⧸ Q.D)⁆ = ⊥ := by
  obtain ⟨μi⟩ := binary_marking ha.pos hi
  obtain ⟨μj⟩ := binary_marking hb hj
  obtain ⟨σi,Ti,_,hBi,_,_,_,_⟩ := LinearPanel.original_panel Q e h split i μi
  obtain ⟨σj,Tj,_,hBj,_,_,_,_⟩ := LinearPanel.original_panel Q e h split j μj
  obtain ⟨c,hc,hroots,horders⟩ := linear_pair_cubic_centralizers Q split hm i j hij
    a b ha hb heb σi Ti hBi σj Tj hBj (LinearThreePresentation.borel_core_eq_bot Q e h)
  obtain ⟨hK,⟨μ⟩⟩ := original_linear_local_marking Q e h split i μi
  have hcard : Nat.card (simpleRoot Q split i) = 2^a := by
    simpa only [rootAt_one] using linear_rootAt_card Q split i a σi Ti hBi ha.pos 1
  obtain ⟨habel,hperp⟩ := separated_linear_radical_abelian Q split hm i j hij hK μ
    (UnitarySource.actorReflection Q split i) ha.pos (GaloisField.card 2 a ha.pos.ne') hcard c hroots
  exact ⟨c,hc,habel,horders.1,perpendicular_rankOne_commutator Q split hm i j hij hperp⟩

/-- Both source orientations supply the structural step of (6G), with the
quadratic field ratio proved from the actual factors. -/
theorem original_linear_pair_cubic_structure
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hj : ClassicalGroup.IsPSL ((L j) ⧸ pCore 2 (L j)) 2 (2^b)) :
    (Odd a ∧ b = 2*a ∧
      ∃ c : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)),
        orderOf c = 3 ∧
        IsMulCommutative ↥(simpleRemainder Q split i ⊓
          centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D))) ∧
        Nat.card (simpleRemainder Q split i ⊓
          centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) : Subgroup (X ⧸ Q.D)) = (2^a)^3 ∧
        ⁅rankOne Q split i,rightConjugate (rankOne Q split i)
          (representative (Q.simple j*Q.simple i*Q.simple j) : X ⧸ Q.D)⁆ = ⊥) ∨
    (Odd b ∧ a = 2*b ∧
      ∃ c : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)),
        orderOf c = 3 ∧
        IsMulCommutative ↥(simpleRemainder Q split j ⊓
          centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D))) ∧
        Nat.card (simpleRemainder Q split j ⊓
          centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) : Subgroup (X ⧸ Q.D)) = (2^b)^3 ∧
        ⁅rankOne Q split j,rightConjugate (rankOne Q split j)
          (representative (Q.simple i*Q.simple j*Q.simple i) : X ⧸ Q.D)⁆ = ⊥) := by
  rcases original_linear_factor_quadratic_degrees Q e h split hm i j hij ha hb hi hj with
    ⟨hoa,hbval⟩ | ⟨hob,haval⟩
  · exact Or.inl ⟨hoa,hbval,original_oriented_linear_cubic_structure Q e h split hm i j hij
      hoa hb (hbval ▸ even_two_mul a) hi hj⟩
  · exact Or.inr ⟨hob,haval,original_oriented_linear_cubic_structure Q e h split hm j i hij.symm
      hob ha (haval ▸ even_two_mul b) hj hi⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
