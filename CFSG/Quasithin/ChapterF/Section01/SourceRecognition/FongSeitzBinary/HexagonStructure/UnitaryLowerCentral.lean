module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.UnitaryLowerCentral
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.UnitaryWeights

/-!
# Original unitary lower-central sections in a hexagon

Each original regular SU3/PSU3 factor supplies a nonabelian class-two
canonical root, the actual local quotient and its special-unitary cover.
These facts put T = [U_sj',U_sj] in the three middle roots and make
U_sj'/T a nontrivial effective elementary binary section. Its relative
normal subgroup and effective denominator are identified literally.
The source degree theorem gives 2^(6n)|T| <= |U_sj'|.

For degrees m <= n, the existing first-layer bound yields
2^(6n)|T| <= 2^(9m). In particular, the previously established ratio
for an unequal-degree quotient of order 2^(6n) forces T = 1. This is a
reduction to the remaining class-two contradiction, not its exclusion.
The required nontriviality and Cartan lower bound for T, the remaining
unitary degree cases and the oriented (6E) assembly remain with this family.

Every statement allows both scalar conventions and both endpoint
orientations without original-factor perfectness. The general marked
application covers original and geometric amalgams. The final two exports
identify the numerator and denominator over the literal Q.q image of S,
with the full original Borel and the same right-conjugation reflection.
Marked quotient, split and rotation-six inputs retain their earlier source
producers and their final discharge in source assembly.

Source: Fong--Seitz I (6D), printed pp.42--43, using (3G), (4D), (5D).
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
open MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
  {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
  {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
  (hconj : ∀ x, J.conj x=x^(2^n))

include e h split hn hcard hconj in
private theorem unitary_lowerCentral_inputs (j : Fin 2)
    (hmodel : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
    simpleRemainder Q split j ≤ localKernel Q j ∧
      ∃ σ : J.specialSubgroup →* rankOne Q split j, Function.Surjective σ ∧
        Nonempty (localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J) := by
  let := h.finite_local j
  obtain ⟨T,hT⟩ := h.sylow j
  rcases hmodel with ⟨⟨μ⟩⟩ | ⟨⟨μ⟩⟩
  · have hK := projectiveUnitary_remainder_le_kernel Q e h split j T hT J hn hcard hconj μ
    have hc := projectiveUnitary_simpleRoot_card_eq_quotientSylow Q e h split j T hT J
      (by omega) hcard hconj μ
    let a := (regularFactorRootEquiv Q e h split j T hT hK hc).trans μ
    exact ⟨hK,a.symm.toMonoidHom.comp J.specialToProjective,
      a.symm.surjective.comp J.specialToProjective_surjective,
      ⟨projectiveUnitaryFactorLocalEquiv Q e h split j T hT J
        (by omega) hcard hconj hK μ⟩⟩
  · have hK := specialUnitary_remainder_le_kernel Q e h split j T hT J hn hcard hconj μ
    have hc := specialUnitary_simpleRoot_card_eq_quotientSylow Q e h split j T hT J
      (by omega) hcard hconj μ
    let a := (regularFactorRootEquiv Q e h split j T hT hK hc).trans μ
    exact ⟨hK,a.symm.toMonoidHom,a.symm.surjective,
      ⟨specialUnitaryFactorLocalEquiv Q e h split j T hT J
        (by omega) hcard hconj hK μ⟩⟩

include e h split hn hcard hconj in
/-- The original regular unitary factor supplies a nonabelian class-two canonical root. -/
theorem original_unitary_root_classTwo (j : Fin 2)
    (hmodel : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
    ⁅⁅simpleRoot Q split j,simpleRoot Q split j⁆,simpleRoot Q split j⁆ = ⊥ ∧
      ⁅simpleRoot Q split j,simpleRoot Q split j⁆ ≠ ⊥ := by
  let A := simpleRoot Q split j
  have hZ := (original_unitary_root_cartan_constituents Q e h split J hn hcard hconj j 1 hmodel).1
  rw [rootAt_one] at hZ
  let : Fact (IsPGroup 2 A) := ⟨split.isTwo.to_le (simpleRoot_le Q split j)⟩
  have hc : _root_.commutator A ≤ center A := (commutator_le_frattini_of_isPGroup (p := 2)).trans_eq hZ
  constructor
  · apply commutator_eq_bot_iff_le_centralizer.mpr
    rw [←map_subtype_commutator]
    rintro x ⟨a,ha,rfl⟩ y hy
    exact congrArg Subtype.val (mem_center_iff.mp (hc ha) ⟨y,hy⟩)
  · obtain ⟨a,ha⟩ := original_unitary_root_square_witness Q e h split J hn hcard hconj j hmodel
    have hs := original_unitary_root_square_mem_commutator Q e h split J hn hcard hconj j hmodel a
    intro he
    have hh := mem_map_of_mem A.subtype hs
    rw [map_subtype_commutator,he] at hh
    exact ha (Subtype.ext (mem_bot.mp hh))

variable {E : Type*} [Field E] [Finite E] (I : HermitianForm 3 E)
  {m : ℕ} (hm : 2 ≤ m) (hE : Nat.card E = (2^m)^2)
  (hconjE : ∀ x, I.conj x=x^(2^m))

include e h split hn hcard hconj hm hE hconjE in
/-- The source D/T is a moving elementary section with exactly its stated denominator. -/
theorem original_unitary_pair_derivedCentral_section
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup I) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* I.specialSubgroup))
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
    ∃ hKj : simpleRemainder Q split j ≤ localKernel Q j,
      let d := derivedCentralSection Q split j hKj
      IsElementaryAbelian 2 d.Carrier ∧ d.effectiveDenominator = d.denominator ∧
        d.IsEffective ∧ d.action ≠ 1 ∧ 2^(6*n) ≤ Nat.card d.Carrier := by
  obtain ⟨hKi,_⟩ := unitary_lowerCentral_inputs Q e h split I hm hE hconjE i hi
  obtain ⟨hKj,σ,hσ,⟨μ⟩⟩ := unitary_lowerCentral_inputs Q e h split J hn hcard hconj j hj
  have hclass := original_unitary_root_classTwo Q e h split I hm hE hconjE i hi
  have hPhi := original_unitary_pair_frattini_eq_commutator Q e h split J hn hcard hconj
    I hm hE hconjE hhex i j hij hi hj
  exact ⟨hKj,derivedCentralSection_elementary Q split j hKj hPhi,
    derivedCentralSection_effectiveDenominator Q split j hKj hPhi,
    unitary_section_effective Q split j J hn hcard hconj σ hσ hKj μ _
      (derivedCentralSection_action_ne_one Q split hhex i j hij hKi hKj hclass.1 hclass.2),
    derivedCentralSection_action_ne_one Q split hhex i j hij hKi hKj hclass.1 hclass.2,
    (unitary_derived_mod_triple_card_bound Q split J hn hcard hconj hhex i j hij hKi hKj
      σ hσ hclass.1 hclass.2).1⟩

include e h split hn hcard hconj hm hE hconjE in
/-- The third lower-central term has its actual middle-root placement and size contribution. -/
theorem original_unitary_pair_lowerCentral_control
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup I) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* I.specialSubgroup))
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
    let V := simpleRemainder Q split j
    let D := ⁅V,V⁆
    let T := ⁅D,V⁆
    T ≤ middleRoots Q split i j ∧ 2^(6*n)*Nat.card T ≤ Nat.card D := by
  obtain ⟨hKi,_⟩ := unitary_lowerCentral_inputs Q e h split I hm hE hconjE i hi
  obtain ⟨hKj,σ,hσ,_⟩ := unitary_lowerCentral_inputs Q e h split J hn hcard hconj j hj
  have hclass := original_unitary_root_classTwo Q e h split I hm hE hconjE i hi
  exact ⟨radical_triple_le_middle Q split hhex i j hij hKi hclass.1,
    (unitary_derived_mod_triple_card_bound Q split J hn hcard hconj hhex i j hij hKi hKj
      σ hσ hclass.1 hclass.2).2⟩

include e h split hn hcard hconj hm hE hconjE in
/-- Combining the first two actual sections retains the entire third-term factor in the source order inequality. -/
theorem original_unitary_pair_third_card_bound
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j) (hmn : m ≤ n)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup I) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* I.specialSubgroup))
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
    let V := simpleRemainder Q split j
    2^(6*n)*Nat.card (⁅⁅V,V⁆,V⁆ : Subgroup (X ⧸ Q.D)) ≤ 2^(9*m) := by
  have hlo := (original_unitary_pair_lowerCentral_control Q e h split J hn hcard hconj
    I hm hE hconjE hhex i j hij hi hj).2
  have hhi := (original_unitary_pair_derived_control Q e h split J hn hcard hconj
    I hm hE hconjE hhex i j hij hmn hi hj).2.1
  exact hlo.trans hhi

include e h split hn hcard hconj hm hE hconjE in
/-- The minimal unequal-degree quotient would force the actual radical to have class at most two. -/
theorem original_unitary_pair_minimal_quotient_classTwo
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j) (hmn : m < n)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup I) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* I.specialSubgroup))
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup))
    (hquot : Nat.card (simpleRemainder Q split j ⧸ frattini (simpleRemainder Q split j)) = 2^(6*n)) :
    ⁅⁅simpleRemainder Q split j,simpleRemainder Q split j⁆,simpleRemainder Q split j⁆ = ⊥ := by
  have hratio := (original_unitary_pair_small_quotient_ratios Q e h split J hn hcard hconj
    I hm hE hconjE hhex i j hij hmn hi hj).1 hquot
  have hb := original_unitary_pair_third_card_bound Q e h split J hn hcard hconj
    I hm hE hconjE hhex i j hij hmn.le hi hj
  dsimp only at hb
  rw [show 9*m = 6*n by omega] at hb
  apply eq_bot_of_card_le
  exact Nat.le_of_mul_le_mul_left (by simpa only [mul_one] using hb)
    (Nat.pow_pos (by decide : 0 < 2))

include e h split hn hcard hconj hm hE hconjE in
/-- Both claims on the original or geometric Sylow image, with its actual reflection. -/
theorem original_unitary_pair_lowerCentral_on_sylow
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup I) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* I.specialSubgroup))
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
    let V := (sylowMap Q e h).range ⊓ rightConjugate (sylowMap Q e h).range
      ((UnitarySource.actorReflection Q split j).val : X ⧸ Q.D)
    let D := ⁅V,V⁆
    let T := ⁅D,V⁆
    T ≤ middleRoots Q split i j ∧ 2^(6*n)*Nat.card T ≤ Nat.card D := by
  dsimp only
  rw [←marked_radical_eq h Q e split j (UnitarySource.actorReflection Q split j).val
    (UnitarySource.actorReflection Q split j).class_eq]
  exact original_unitary_pair_lowerCentral_control Q e h split J hn hcard hconj
    I hm hE hconjE hhex i j hij hi hj

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure

open Subgroup
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- Conditional source consumer for the repeated lower-central argument in
(6D).  Once the unitary composition-section calculation supplies the uniform
cardinal bound on every term, the finite two-group radical is nilpotent and
the abstract lower-central contradiction closes the branch. -/
theorem unitary_lowerCentral_persistence_contradiction
    (j : Fin 2) {n : ℕ} (hn : 2 ≤ n)
    (hpersist : ∀ k : ℕ,
      2^(6*n) ≤ Nat.card ((simpleRemainder Q split j).lowerCentralSeries k)) : False := by
  let V := simpleRemainder Q split j
  let : Fact (IsPGroup 2 V) := ⟨split.isTwo.to_le inf_le_left⟩
  let : Group.IsNilpotent V := (split.isTwo.to_le inf_le_left).isNilpotent
  have hc : 2 ≤ 2^(6*n) := by
    calc
      2 = 2^1 := by norm_num
      _ ≤ 2^(6*n) := Nat.pow_le_pow_right (by decide) (by omega)
  apply lowerCentralSeries_card_contradiction (c := 2^(6*n)) V hc
  intro k
  simpa only [V] using hpersist k

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The lower-central placement and multiplicative bound on the literal Q.q image of S. -/
theorem quotient_unitary_pair_lowerCentral_control
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x=x^(2^n))
    {E : Type*} [Field E] [Finite E] (I : HermitianForm 3 E)
    {m : ℕ} (hm : 2 ≤ m) (hE : Nat.card E = (2^m)^2)
    (hconjE : ∀ x, I.conj x=x^(2^m))
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup I) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* I.specialSubgroup))
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
    let V := ((S.subgroupOf (generated L S)).map Q.q) ⊓
      rightConjugate ((S.subgroupOf (generated L S)).map Q.q)
        ((UnitarySource.actorReflection Q split j).val : (generated L S) ⧸ Q.D)
    let D := ⁅V,V⁆
    let T := ⁅D,V⁆
    T ≤ middleRoots Q split i j ∧ 2^(6*n)*Nat.card T ≤ Nat.card D := by
  dsimp only
  rw [quotient_sourceS_image_eq_unipotent h Q split]
  have hh := original_unitary_pair_lowerCentral_on_sylow Q (originalMarkedIso Q) h split
    J hn hcard hconj I hm hE hconjE hhex i j hij hi hj
  dsimp only at hh
  rwa [MarkedLocal.sylow_range Q (originalMarkedIso Q) h split] at hh

/-- The effective elementary section on the literal Q.q image, with both ambient subgroup maps identified. -/
theorem quotient_unitary_pair_derivedCentral_section
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x=x^(2^n))
    {E : Type*} [Field E] [Finite E] (I : HermitianForm 3 E)
    {m : ℕ} (hm : 2 ≤ m) (hE : Nat.card E = (2^m)^2)
    (hconjE : ∀ x, I.conj x=x^(2^m))
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup I) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* I.specialSubgroup))
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
    let V := ((S.subgroupOf (generated L S)).map Q.q) ⊓
      rightConjugate ((S.subgroupOf (generated L S)).map Q.q)
        ((UnitarySource.actorReflection Q split j).val : (generated L S) ⧸ Q.D)
    ∃ d : RootSection Q split j,
      d.numerator = ⁅V,V⁆ ∧ d.denominator.map d.numerator.subtype = ⁅⁅V,V⁆,V⁆ ∧
      IsElementaryAbelian 2 d.Carrier ∧ d.effectiveDenominator = d.denominator ∧
      d.IsEffective ∧ d.action ≠ 1 ∧ 2^(6*n) ≤ Nat.card d.Carrier := by
  obtain ⟨hKj,hE₀,hden,heff,hmove,hbound⟩ := original_unitary_pair_derivedCentral_section
    Q (originalMarkedIso Q) h split J hn hcard hconj I hm hE hconjE hhex i j hij hi hj
  dsimp only
  rw [quotient_sourceS_image_eq_unipotent h Q split]
  have hV := marked_radical_eq h Q (originalMarkedIso Q) split j
    (UnitarySource.actorReflection Q split j).val (UnitarySource.actorReflection Q split j).class_eq
  rw [MarkedLocal.sylow_range Q (originalMarkedIso Q) h split] at hV
  rw [←hV]
  refine ⟨derivedCentralSection Q split j hKj,rfl,?_,hE₀,hden,heff,hmove,hbound⟩
  exact map_subgroupOf_eq_of_le (radical_triple_le_derived Q split j)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
