module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.LinearPairCubicCentralizers
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.LinearPanelCompletion
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.CubicProduct
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.CubicSeparation

/-!
# A common cubic actor for the two-linear octagon calculations

For an actual F.1.1 pair of linear endpoints, this theorem retains one
order-three element while recording its root fixed points, its three-root
fixed radical, and the perpendicular rank-one product.  It also records the
exact Cartan coordinates and the two panel-kernel separation inside that
product.  These are the concrete inputs to the terminal part of the
Fong--Seitz (6G) argument; no terminal contradiction or row classification
is asserted here.

Source: Fong--Seitz I (6G), pp.49--51.  The original full amalgam map is
used throughout, so both endpoint squares and the whole Borel are retained.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
open MarkedLocal LinearPanel ReeSource

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

include e h split in
/-- The same original cubic actor controls the fixed radical and the
perpendicular product in either endpoint orientation.  The source field
markings, full Borel, and both endpoint maps are those of `e`. -/
theorem original_oriented_linear_cubic_terminal_input
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    {a b : ℕ} (ha : Odd a) (hb : 0 < b) (heb : Even b)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hj : ClassicalGroup.IsPSL ((L j) ⧸ pCore 2 (L j)) 2 (2^b)) :
    ∃ c : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)),
      orderOf c = 3 ∧
      (∀ w : Weyl Q,
        (c : X ⧸ Q.D) ∈ centralizer (rootAt Q split i w : Set (X ⧸ Q.D)) ∧
        rootAt Q split j w ⊓
          centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) = ⊥) ∧
      rootAt Q split i (Q.simple j) ⊔
          rootAt Q split i (Q.simple j * Q.simple i * Q.simple j) ⊔
          rootAt Q split i (Q.simple j * Q.simple i) =
        simpleRemainder Q split i ⊓
          centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) ∧
      Nat.card (simpleRemainder Q split i ⊓
        centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) : Subgroup (X ⧸ Q.D)) = (2^a)^3 ∧
      ⁅rankOne Q split i,
        rightConjugate (rankOne Q split i)
          (representative (Q.simple j * Q.simple i * Q.simple j) : X ⧸ Q.D)⁆ = ⊥ ∧
      (∃ z : rankOne Q split i ×
          rightConjugate (rankOne Q split i)
            (representative (Q.simple j * Q.simple i * Q.simple j) : X ⧸ Q.D) ≃*
          ↥(rankOne Q split i ⊔ rightConjugate (rankOne Q split i)
            (representative (Q.simple j * Q.simple i * Q.simple j) : X ⧸ Q.D)),
        ∀ x y, (z (x,y) : X ⧸ Q.D) = (x : X ⧸ Q.D) * (y : X ⧸ Q.D)) := by
  let hi₀ := hi
  let hj₀ := hj
  obtain ⟨F,hF,hfin,hcard,⟨μ⟩⟩ := hi
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  obtain ⟨hK,⟨ν⟩⟩ := original_linear_local_marking Q e h split i μ
  obtain ⟨μi⟩ := binary_marking (a := a) ha.pos hi₀
  obtain ⟨μj⟩ := binary_marking (a := b) hb hj₀
  obtain ⟨σi,Ti,_,hBi,_,_,_,_⟩ := original_panel Q e h split i μi
  obtain ⟨σj,Tj,_,hBj,_,_,_,_⟩ := original_panel Q e h split j μj
  have hroot : Nat.card (simpleRoot Q split i) = 2^a := by
    simpa only [rootAt_one] using linear_rootAt_card Q split i a σi Ti hBi ha.pos 1
  have hcore := LinearThreePresentation.borel_core_eq_bot Q e h
  obtain ⟨c,hc,hroots,horders⟩ := linear_pair_cubic_centralizers Q split hm i j hij
    a b ha hb heb σi Ti hBi σj Tj hBj hcore
  obtain ⟨_,hrootPerp⟩ := separated_linear_radical_abelian Q split hm i j hij hK ν
    (UnitarySource.actorReflection Q split i) ha.pos hcard hroot c hroots
  have hjoin := separated_radical_centralizer_sup Q split hm i j hij c hroots
  let w : Weyl Q := Q.simple j * Q.simple i * Q.simple j
  let B := rightConjugate (rankOne Q split i) (representative w : X ⧸ Q.D)
  have hperp := perpendicular_rankOne_commutator Q split hm i j hij hrootPerp
  obtain ⟨z,hz⟩ := linear_commuting_product Q split i hK ν B hperp
  dsimp only [w,B] at *
  exact ⟨c,hc,hroots,hjoin,horders.1,hperp,⟨z,hz⟩⟩

/-- The same terminal data with the two original endpoint model hypotheses
made existential.  This is the shape consumed by Chapter 12 source
selection, where the endpoint fields are supplied by the selected row. -/
abbrev original_oriented_linear_cubic_terminal_data
    {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
    (Q : MarkedQuotient P) (split : SplitData Q.tits)
    (i j : Fin 2) {a : ℕ} : Prop :=
  ∃ c : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)),
    orderOf c = 3 ∧
    (∀ w : Weyl Q,
      (c : X ⧸ Q.D) ∈ centralizer (rootAt Q split i w : Set (X ⧸ Q.D)) ∧
      rootAt Q split j w ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) = ⊥) ∧
    rootAt Q split i (Q.simple j) ⊔
        rootAt Q split i (Q.simple j * Q.simple i * Q.simple j) ⊔
        rootAt Q split i (Q.simple j * Q.simple i) =
      simpleRemainder Q split i ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) ∧
    Nat.card (simpleRemainder Q split i ⊓
      centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) : Subgroup (X ⧸ Q.D)) = (2^a)^3 ∧
    ⁅rankOne Q split i,
      rightConjugate (rankOne Q split i)
        (representative (Q.simple j * Q.simple i * Q.simple j) : X ⧸ Q.D)⁆ = ⊥ ∧
    ∃ z : rankOne Q split i ×
        rightConjugate (rankOne Q split i)
          (representative (Q.simple j * Q.simple i * Q.simple j) : X ⧸ Q.D) ≃*
        ↥(rankOne Q split i ⊔ rightConjugate (rankOne Q split i)
          (representative (Q.simple j * Q.simple i * Q.simple j) : X ⧸ Q.D)),
      ∀ x y, (z (x,y) : X ⧸ Q.D) = (x : X ⧸ Q.D) * (y : X ⧸ Q.D)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
