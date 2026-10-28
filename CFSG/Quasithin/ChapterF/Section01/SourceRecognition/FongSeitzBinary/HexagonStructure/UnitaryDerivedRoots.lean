module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.UnitaryDerivedRoots
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.UnitaryLayers

/-!
# Actual unitary-pair derived radicals in the marked hexagon

Regularity and the original quotient-Sylow order identify each root actor
with its marked SU3 or PSU3 group. Hermitian commutators therefore put
every canonical root square in the root's derived subgroup. The five-root
factorization proves Φ(U_sj) = U_sj' on either endpoint.

For regular degrees m ≤ n, the literal source action gives
2^(6n) ≤ |U_sj'| ≤ 2^(9m). The same R_j centralizes Φ(U_sj'), and the
four nonmiddle roots are not contained in U_sj'. Both scalar conventions
are retained independently, with no original-factor perfectness premise.
The general marked application covers the original and geometric amalgams;
the final applications use the literal image of S under Q.q and its
right conjugate by the actual root reflection. The full Borel is unchanged.

These results identify and control the derived section used in (6D).
They do not prove the remaining Cartan constituent calculation, unitary
parameter equality or lower-central-series contradiction. The mixed
linear--unitary exclusion and exhaustive oriented (6E) assembly remain.
The marked quotient, split and rotation-six hypotheses retain their earlier
source producers and their final discharge in source assembly.

Source: Fong--Seitz I (6D), printed pp.42--43, using (4D), (5D) and (3G).
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
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
private theorem regular_unitary_root_models (j : Fin 2)
    (hmodel : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
    simpleRemainder Q split j ≤ localKernel Q j ∧
      Nat.card (simpleRoot Q split j) = (2^n)^3 ∧
      (Nonempty (rankOne Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
        Nonempty (rankOne Q split j ≃* J.specialSubgroup)) := by
  let := h.finite_local j
  obtain ⟨T,hT⟩ := h.sylow j
  rcases hmodel with ⟨⟨μ⟩⟩ | ⟨⟨μ⟩⟩
  · have hK := projectiveUnitary_remainder_le_kernel Q e h split j T hT J hn hcard hconj μ
    have hc := projectiveUnitary_simpleRoot_card_eq_quotientSylow Q e h split j T hT J
      (by omega) hcard hconj μ
    exact ⟨hK,projectiveUnitary_simpleRoot_card Q e h split j T hT J
      (by omega) hcard hconj μ,Or.inl ⟨(regularFactorRootEquiv Q e h split j T hT hK hc).trans μ⟩⟩
  · have hK := specialUnitary_remainder_le_kernel Q e h split j T hT J hn hcard hconj μ
    have hc := specialUnitary_simpleRoot_card_eq_quotientSylow Q e h split j T hT J
      (by omega) hcard hconj μ
    exact ⟨hK,specialUnitary_simpleRoot_card Q e h split j T hT J
      (by omega) hcard hconj μ,Or.inr ⟨(regularFactorRootEquiv Q e h split j T hT hK hc).trans μ⟩⟩

include e h split hn hcard hconj in
/-- The actual regular original unitary factor supplies root squares in the root commutator. -/
theorem original_unitary_root_square_mem_commutator (j : Fin 2)
    (hmodel : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
    ∀ x : simpleRoot Q split j, x^2 ∈ _root_.commutator (simpleRoot Q split j) := by
  obtain ⟨_,hc,hR⟩ := regular_unitary_root_models Q e h split J hn hcard hconj j hmodel
  exact unitary_root_square_mem_commutator Q split J hn hcard hconj j hR hc

variable {E : Type*} [Field E] [Finite E] (I : HermitianForm 3 E)
  {m : ℕ} (hm : 2 ≤ m) (hE : Nat.card E = (2^m)^2)
  (hconjE : ∀ x, I.conj x=x^(2^m))

include e h split hn hcard hconj hm hE hconjE in
/-- The radical Frattini and derived subgroups coincide for both unitary scalar conventions. -/
theorem original_unitary_pair_frattini_eq_commutator
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup I) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* I.specialSubgroup))
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
    frattini (simpleRemainder Q split j) = _root_.commutator (simpleRemainder Q split j) := by
  apply radical_frattini_eq_commutator_of_root_squares Q split hhex i j hij
  intro k
  have hk : k=i ∨ k=j := by omega
  rcases hk with hk | hk
  · subst k
    exact original_unitary_root_square_mem_commutator Q e h split I hm hE hconjE i hi
  · subst k
    exact original_unitary_root_square_mem_commutator Q e h split J hn hcard hconj j hj

include e h split hn hcard hconj hm hE hconjE in
/-- The larger-degree actor controls the actual derived radical, with all model and square inputs discharged. -/
theorem original_unitary_pair_derived_control
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j) (hmn : m ≤ n)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup I) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* I.specialSubgroup))
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
    let D := ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆
    2^(6*n) ≤ Nat.card D ∧ Nat.card D ≤ 2^(9*m) ∧
      ⁅rankOne Q split j,(frattini D).map D.subtype⁆ = ⊥ ∧
      ∀ t : Fin 5, t ≠ 2 →
        ¬ rootAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t) ≤ D := by
  obtain ⟨_,hci,_⟩ := regular_unitary_root_models Q e h split I hm hE hconjE i hi
  obtain ⟨hKj,hcj,hRj⟩ := regular_unitary_root_models Q e h split J hn hcard hconj j hj
  have hσ : ∃ σ : J.specialSubgroup →* rankOne Q split j, Function.Surjective σ := by
    rcases hRj with ⟨⟨μ⟩⟩ | ⟨⟨μ⟩⟩
    · exact ⟨μ.symm.toMonoidHom.comp J.specialToProjective,
        μ.symm.surjective.comp J.specialToProjective_surjective⟩
    · exact ⟨μ.symm.toMonoidHom,μ.symm.surjective⟩
  obtain ⟨σ,hσ⟩ := hσ
  have hsquare : ∀ k : Fin 2, ∃ x : simpleRoot Q split k, x^2 ≠ 1 := by
    intro k
    have hk : k=i ∨ k=j := by omega
    rcases hk with hk | hk
    · subst k
      exact original_unitary_root_square_witness Q e h split I hm hE hconjE i hi
    · subst k
      exact original_unitary_root_square_witness Q e h split J hn hcard hconj j hj
  have hsq : ∀ k : Fin 2, ∀ x : simpleRoot Q split k,
      x^2 ∈ _root_.commutator (simpleRoot Q split k) := by
    intro k
    have hk : k=i ∨ k=j := by omega
    rcases hk with hk | hk
    · subst k
      exact original_unitary_root_square_mem_commutator Q e h split I hm hE hconjE i hi
    · subst k
      exact original_unitary_root_square_mem_commutator Q e h split J hn hcard hconj j hj
  have hci' : Nat.card (simpleRoot Q split i) = 2^(3*m) := by
    rw [hci,←pow_mul,Nat.mul_comm]
  simpa only [←Nat.mul_assoc,Nat.reduceMul] using
    unitary_derived_radical_control Q split J hn hcard hconj hhex i j hij hKj σ hσ
      hci' hcj (by omega : 3*m < 4*n) hsquare hsq

include e h split hn hcard hconj hm hE hconjE in
/-- The same statement on the original or geometric Sylow image and the literal reflection word. -/
theorem original_unitary_pair_derived_control_on_sylow
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j) (hmn : m ≤ n)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup I) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* I.specialSubgroup))
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
    let V := (sylowMap Q e h).range ⊓ rightConjugate (sylowMap Q e h).range
      ((UnitarySource.actorReflection Q split j).val : X ⧸ Q.D)
    let D := ⁅V,V⁆
    2^(6*n) ≤ Nat.card D ∧ Nat.card D ≤ 2^(9*m) ∧
      ⁅rankOne Q split j,(frattini D).map D.subtype⁆ = ⊥ ∧
      ∀ t : Fin 5, t ≠ 2 →
        ¬ rootAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t) ≤ D := by
  dsimp only
  rw [←marked_radical_eq h Q e split j (UnitarySource.actorReflection Q split j).val
    (UnitarySource.actorReflection Q split j).class_eq]
  exact original_unitary_pair_derived_control Q e h split J hn hcard hconj I hm hE hconjE
    hhex i j hij hmn hi hj

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Derived-radical bounds and centralization on the literal Q.q image of the original S. -/
theorem quotient_unitary_pair_derived_control
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x=x^(2^n))
    {E : Type*} [Field E] [Finite E] (I : HermitianForm 3 E)
    {m : ℕ} (hm : 2 ≤ m) (hE : Nat.card E = (2^m)^2)
    (hconjE : ∀ x, I.conj x=x^(2^m))
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j) (hmn : m ≤ n)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup I) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* I.specialSubgroup))
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
    let V := ((S.subgroupOf (generated L S)).map Q.q) ⊓
      rightConjugate ((S.subgroupOf (generated L S)).map Q.q)
        ((UnitarySource.actorReflection Q split j).val : (generated L S) ⧸ Q.D)
    let D := ⁅V,V⁆
    2^(6*n) ≤ Nat.card D ∧ Nat.card D ≤ 2^(9*m) ∧
      ⁅rankOne Q split j,(frattini D).map D.subtype⁆ = ⊥ ∧
      ∀ t : Fin 5, t ≠ 2 →
        ¬ rootAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t) ≤ D := by
  dsimp only
  rw [quotient_sourceS_image_eq_unipotent h Q split]
  have hh := original_unitary_pair_derived_control_on_sylow Q (originalMarkedIso Q) h split
    J hn hcard hconj I hm hE hconjE hhex i j hij hmn hi hj
  dsimp only at hh
  rwa [MarkedLocal.sylow_range Q (originalMarkedIso Q) h split] at hh

/-- The Frattini identification on the same original quotient-map radical, in either orientation. -/
theorem quotient_unitary_pair_frattini_eq_commutator
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
    frattini V = _root_.commutator V := by
  dsimp only
  rw [quotient_sourceS_image_eq_unipotent h Q split,
    ←MarkedLocal.sylow_range Q (originalMarkedIso Q) h split,
    ←marked_radical_eq h Q (originalMarkedIso Q) split j
      (UnitarySource.actorReflection Q split j).val (UnitarySource.actorReflection Q split j).class_eq]
  exact original_unitary_pair_frattini_eq_commutator Q (originalMarkedIso Q) h split
    J hn hcard hconj I hm hE hconjE hhex i j hij hi hj

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
