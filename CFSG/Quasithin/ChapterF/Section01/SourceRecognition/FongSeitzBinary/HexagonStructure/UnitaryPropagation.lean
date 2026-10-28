module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.UnitaryPropagation
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.UnitaryCartanBounds
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.RegularUnitaryCover

/-!
# Original unitary escape and lower-central propagation

Both original regular unitary factor markings supply the actual roots,
class-two identities, and the special-unitary cover of the rank-one actor.
Their already proved parameter equality bounds the literal central product
Z(A₁) A₂ Z(A₃) by 2^(5n). An initial derived-subgroup escape therefore
propagates to every actual lower-central term and contradicts nilpotence.

The only added mathematical premise is the initial escape. Its sharp
minimal-degree representation argument remains with the initial-seed
construction; there is no assumed recurrence or uniform lower-central bound.
Both orientations, SU3/PSU3 scalar conventions, nonperfect original factors,
and the literal original quotient map are retained.
Source: Fong--Seitz I (6D), printed pp.42--43.
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
private theorem unitary_propagation_inputs (j : Fin 2)
    (hmodel : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
    simpleRemainder Q split j ≤ localKernel Q j ∧
      Nat.card (simpleRoot Q split j) = (2^n)^3 := by
  let := h.finite_local j
  obtain ⟨T,hT⟩ := h.sylow j
  rcases hmodel with ⟨⟨μ⟩⟩ | ⟨⟨μ⟩⟩
  · exact ⟨projectiveUnitary_remainder_le_kernel Q e h split j T hT J hn hcard hconj μ,
      projectiveUnitary_simpleRoot_card Q e h split j T hT J (by omega) hcard hconj μ⟩
  · exact ⟨specialUnitary_remainder_le_kernel Q e h split j T hT J hn hcard hconj μ,
      specialUnitary_simpleRoot_card Q e h split j T hT J (by omega) hcard hconj μ⟩

variable {E : Type*} [Field E] [Finite E] (I : HermitianForm 3 E)
  {m : ℕ} (hm : 2 ≤ m) (hE : Nat.card E = (2^m)^2)
  (hconjE : ∀ x, I.conj x=x^(2^m))

include e h split hn hcard hconj hm hE hconjE in
/-- Parameter equality makes the actual central-coordinate product smaller
than a moving unitary section, in both scalar conventions and orientations. -/
theorem original_unitary_pair_centralProduct_card_bound
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup I) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* I.specialSubgroup))
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
    Nat.card (middleCentralProduct Q split i j) ≤ 2^(5*n) := by
  have hmn := original_unitary_pair_parameters_eq Q e h split J hn hcard hconj
    I hm hE hconjE hhex i j hij hi hj
  have hci := (unitary_propagation_inputs Q e h split I hm hE hconjE i hi).2
  have hZ := original_unitary_root_cartan_constituents Q e h split J hn hcard hconj j 1 hj
  have hcj : Nat.card (center (simpleRoot Q split j)) = 2^n := by
    have hz := hZ.1 ▸ hZ.2.1
    change Nat.card (center (rootAt Q split j 1)) = 2^n at hz
    rwa [rootAt_one] at hz
  have hb := middleCentralProduct_card_le Q split i j
  rw [hci,hcj,hmn,←pow_mul,←pow_mul,←pow_add] at hb
  convert hb using 1
  congr 1
  omega

include e h split hn hcard hconj hm hE hconjE in
/-- The initial source escape supplies every actual lower-central bound.
All local covers, class-two geometry, and the small-product bound are
constructed from the original unitary endpoint hypotheses. -/
theorem original_unitary_pair_lowerCentral_bound_of_escape
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup I) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* I.specialSubgroup))
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup))
    (hescape : ¬ ((⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ ⊓
      middleRoots Q split i j : Subgroup (X ⧸ Q.D)) : Set (X ⧸ Q.D)) ⊆
        middleCentralProduct Q split i j) :
    ∀ k : ℕ, 2^(6*n) ≤ Nat.card ((simpleRemainder Q split j).lowerCentralSeries k) := by
  have hKi := (unitary_propagation_inputs Q e h split I hm hE hconjE i hi).1
  have hKj := (unitary_propagation_inputs Q e h split J hn hcard hconj j hj).1
  obtain ⟨_,σ,hσ,_⟩ := regular_unitary_cover_of_factor Q e h split J (by omega) hcard hconj j hKj hj.symm
  have hclass := (original_unitary_root_classTwo Q e h split I hm hE hconjE i hi).1
  have hsmall : Nat.card (middleCentralProduct Q split i j) < 2^(6*n) :=
    (original_unitary_pair_centralProduct_card_bound Q e h split J hn hcard hconj
      I hm hE hconjE hhex i j hij hi hj).trans_lt
      ((Nat.pow_lt_pow_iff_right (by decide : 1 < (2:ℕ))).mpr (by omega))
  exact unitary_lowerCentral_bound_of_escape Q split hhex i j hij
    (UnitarySource.actorReflection Q split j) hKi hKj hclass
    J hn hcard hconj σ hσ hsmall hescape

include e h split hn hcard hconj hm hE hconjE in
/-- The regular-unitary pair is excluded once its initial escape is
constructed; no persistence or later-section input remains. -/
theorem original_unitary_pair_excluded_of_escape
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup I) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* I.specialSubgroup))
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup))
    (hescape : ¬ ((⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ ⊓
      middleRoots Q split i j : Subgroup (X ⧸ Q.D)) : Set (X ⧸ Q.D)) ⊆
        middleCentralProduct Q split i j) : False :=
  unitary_lowerCentral_persistence_contradiction Q split j hn
    (original_unitary_pair_lowerCentral_bound_of_escape Q e h split J hn hcard hconj
      I hm hE hconjE hhex i j hij hi hj hescape)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The escape-to-contradiction application on the literal Q.q image of the
original Sylow subgroup, with its actual right-conjugation reflection. -/
theorem quotient_unitary_pair_excluded_of_escape
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
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup))
    (hescape :
      let V := ((S.subgroupOf (generated L S)).map Q.q) ⊓
        rightConjugate ((S.subgroupOf (generated L S)).map Q.q)
          ((UnitarySource.actorReflection Q split j).val : (generated L S) ⧸ Q.D)
      ¬ ((⁅V,V⁆ ⊓ middleRoots Q split i j : Subgroup ((generated L S) ⧸ Q.D)) :
          Set ((generated L S) ⧸ Q.D)) ⊆ middleCentralProduct Q split i j) : False := by
  dsimp only at hescape
  rw [quotient_sourceS_image_eq_unipotent h Q split] at hescape
  have he := marked_radical_eq h Q (originalMarkedIso Q) split j
    (UnitarySource.actorReflection Q split j).val (UnitarySource.actorReflection Q split j).class_eq
  rw [MarkedLocal.sylow_range Q (originalMarkedIso Q) h split] at he
  rw [←he] at hescape
  exact original_unitary_pair_excluded_of_escape Q (originalMarkedIso Q) h split
    J hn hcard hconj I hm hE hconjE hhex i j hij hi hj hescape

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
