module

public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.LinearPairCubicTerminalInput
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.CartanFactors
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.CubicProduct
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.CubicRootMovement

/-!
# Degree-one Cartan obstruction and root movement in the original octagon

For the actual F.1.1 marked quotient, the two linear endpoint images bound the
full Cartan by the product of their field-unit images.  In the `1,2` degree
orientation, the cubic actor gives an element of order three, so the Cartan has
order exactly three. The two even-endpoint rank-one factors cannot commute.
The Weyl-reflection transport then proves the paper's noncommutativity of
the two even root groups. The cubic actor supplies the nearer odd-root zero
commutator, and the reflected fixed-radical coordinates construct the
diagonal involution in the two middle odd roots. These are inputs to the
subsequent normalizer argument; the terminal exclusion is not proved here.

Source: Fong--Seitz I (6G), printed pp.49--50.
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

private theorem binary_marking_source {Y : Type*} [Group Y] {a : ℕ}
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

private theorem original_linear_local_marking_source (i : Fin 2)
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

include e h split

/-- The literal degree-one `(6G)` contradiction once its even-endpoint
perpendicular commutator has been established by the preceding source steps. -/
theorem original_linear_degree_one_cartan_exclusion
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 2)
    (hj : ClassicalGroup.IsPSL ((L j) ⧸ pCore 2 (L j)) 2 4)
    (hcomm : ⁅rankOne Q split j,
      rightConjugate (rankOne Q split j)
        (representative (Q.simple i * Q.simple j * Q.simple i) : X ⧸ Q.D)⁆ = ⊥) :
    False := by
  obtain ⟨μi⟩ := binary_marking_source (a := 1) (by decide) hi
  obtain ⟨μj⟩ := binary_marking_source (a := 2) (by decide) hj
  obtain ⟨σi,Ti,_,hBi,_,_,_,_⟩ := original_panel Q e h split i μi
  obtain ⟨σj,Tj,_,hBj,_,_,_,_⟩ := original_panel Q e h split j μj
  have hcore := LinearThreePresentation.borel_core_eq_bot Q e h
  have hdiv := cartan_card_dvd_product_images Q split
    (UnitarySource.actorReflection Q split) hcore
  have hdiv' : Nat.card (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) ∣ 3 := by
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
      · exact (hij rfl).elim
      · rw [linear_cartanImage_card Q split 0 1 (by decide) σi Ti hBi
          (UnitarySource.actorReflection Q split 0),
        linear_cartanImage_card Q split 1 2 (by decide) σj Tj hBj
          (UnitarySource.actorReflection Q split 1)] at hdiv
        norm_num at hdiv ⊢
        exact hdiv
    · rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
      · rw [linear_cartanImage_card Q split 0 2 (by decide) σj Tj hBj
          (UnitarySource.actorReflection Q split 0),
        linear_cartanImage_card Q split 1 1 (by decide) σi Ti hBi
          (UnitarySource.actorReflection Q split 1)] at hdiv
        norm_num at hdiv ⊢
        exact hdiv
      · exact (hij rfl).elim
  obtain ⟨c,hc,_,_,_,_⟩ := original_oriented_linear_cubic_terminal_input Q e h split hm
    i j hij (a := 1) (b := 2) (by decide) (by decide) (by decide) hi hj
  have hcdiv : orderOf c ∣
      Nat.card (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) :=
    orderOf_dvd_natCard c
  have hlo : 3 ≤ Nat.card (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) := by
    rw [hc] at hcdiv
    exact Nat.le_of_dvd (Nat.card_pos) hcdiv
  have hupper : Nat.card (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) ≤ 3 := by
    exact Nat.le_of_dvd (by decide) hdiv'
  have hH : Nat.card (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) = 3 := by
    omega
  obtain ⟨F,hF,hfin,hFcard,⟨μ⟩⟩ := hj
  let : Fintype F := Fintype.ofFinite F
  have hcardF : Fintype.card F = 2^2 := by
    rw [← Nat.card_eq_fintype_card, hFcard]
    norm_num
  let : CharP F 2 := charP_of_card_eq_prime_pow hcardF
  obtain ⟨hK,⟨ν⟩⟩ := original_linear_local_marking_source Q e h split j μ
  have hprod := perpendicular_linear_cartan_card Q split j hK ν
    (Q.simple i * Q.simple j * Q.simple i) hcomm
  have hprod_le : (Nat.card F - 1)^2 ≤
      Nat.card (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) := by
    rw [← hprod]
    exact Nat.card_le_card_of_injective (inclusion inf_le_left)
      (inclusion_injective inf_le_left)
  have hprod_le' : 9 ≤
      Nat.card (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) := by
    have hcardF' : Fintype.card F = 4 := by simpa using hcardF
    simpa [hcardF'] using hprod_le
  omega

/-- In the degree-one branch the full even-endpoint rank-one groups across
the intervening Weyl element cannot commute. The root-group conclusion on
printed p.50 follows separately by Weyl-reflection transport below. -/
theorem original_linear_degree_one_perpendicular_nontrivial
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 2)
    (hj : ClassicalGroup.IsPSL ((L j) ⧸ pCore 2 (L j)) 2 4) :
    ⁅rankOne Q split j,
      rightConjugate (rankOne Q split j)
        (representative (Q.simple i * Q.simple j * Q.simple i) : X ⧸ Q.D)⁆ ≠ ⊥ := by
  intro hcomm
  exact original_linear_degree_one_cartan_exclusion Q e h split hm i j hij hi hj hcomm

/-- The actual root-group noncommutativity at the start of the degree-one
argument on printed p.50.  The Weyl-reflection lemma promotes a hypothetical
commuting pair of roots to commuting full rank-one groups. -/
theorem original_linear_degree_one_root_perpendicular_nontrivial
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 2)
    (hj : ClassicalGroup.IsPSL ((L j) ⧸ pCore 2 (L j)) 2 4) :
    ⁅simpleRoot Q split j,
      rootAt Q split j (Q.simple i * Q.simple j * Q.simple i)⁆ ≠ ⊥ := by
  intro hc
  exact original_linear_degree_one_perpendicular_nontrivial Q e h split hm i j hij hi hj
    (perpendicular_rankOne_commutator Q split hm j i hij.symm hc)

/-- The degree-one root inputs to the normalizer argument of (6G): the
even perpendicular roots do not commute, the nearer odd roots commute,
and the long odd-root commutator is the actual diagonal involution in the
two middle fixed roots. All local markings and cubic-actor premises are
constructed from the original factor quotients. -/
theorem original_linear_degree_one_root_relations
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 2)
    (hj : ClassicalGroup.IsPSL ((L j) ⧸ pCore 2 (L j)) 2 4) :
    ⁅simpleRoot Q split j,
      rootAt Q split j (Q.simple i * Q.simple j * Q.simple i)⁆ ≠ ⊥ ∧
    ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j * Q.simple i)⁆ = ⊥ ∧
    ∃ x ∈ rootAt Q split i (Q.simple j * Q.simple i * Q.simple j),
      ∃ y ∈ rootAt Q split i (Q.simple j * Q.simple i),
        x ≠ 1 ∧ y ≠ 1 ∧
        ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ = zpowers (x*y) ∧
        orderOf (x*y) = 2 := by
  obtain ⟨μ⟩ := binary_marking_source (a := 1) (by decide) hi
  obtain ⟨hK,⟨ν⟩⟩ := original_linear_local_marking_source Q e h split i μ
  have hcard : Nat.card (simpleRoot Q split i) = 2 := by
    rw [GTwoSource.simpleRoot_card Q split i hK ν,
      GaloisField.card 2 1 (by decide)]
    rfl
  obtain ⟨c,_,hc,_,_,hfull,_⟩ := original_oriented_linear_cubic_terminal_input
    Q e h split hm i j hij (a := 1) (b := 2) (by decide) (by decide) (by decide) hi hj
  have hperp : ⁅simpleRoot Q split i,
      rootAt Q split i (Q.simple j * Q.simple i * Q.simple j)⁆ = ⊥ := by
    apply bot_unique
    apply le_trans (commutator_mono
      (show simpleRoot Q split i ≤ rankOne Q split i from le_sup_left)
      (comap_mono (show simpleRoot Q split i ≤ rankOne Q split i from le_sup_left)))
    exact hfull.le
  exact ⟨original_linear_degree_one_root_perpendicular_nontrivial Q e h split hm
      i j hij hi hj,
    separated_distance_two_commutator Q split hm i j hij hK c hc,
    separated_binary_long_commutator_diagonal Q split hm i j hij hK
      (UnitarySource.actorReflection Q split i) hcard c hc hperp⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
