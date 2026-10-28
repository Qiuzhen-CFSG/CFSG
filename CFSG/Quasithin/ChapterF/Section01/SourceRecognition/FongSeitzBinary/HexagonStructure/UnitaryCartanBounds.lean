module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.UnitaryCartanBounds
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.UnitaryClassTwo

/-!
# The third Cartan bound and equality of regular unitary parameters

Let V be the actual radical U_sj, D = [V,V], and T = [D,V]. The
previous class-two contradiction makes T nontrivial. Normal root-interval
projections and the actual unitary Cartan actions give |T| >= 2^m for
m <= n. The effective derived quotient D/T then gives
|D| >= 2^(6n+m), in particular 3n <= 4m.

This stronger derived bound excludes all unequal parameters directly.
If m < n, the three proved Cartan possibilities for |V/Phi(V)| are
2^(6m+2n), 2^(4m+4n), and 2^(6m+4n). Multiplying each by the lower bound
on D contradicts |V| = 2^(9m+6n), since Phi(V) = D. Applying the same
argument in the other orientation proves m = n. This uses the literal
central derived section, not merely a minimum-degree numerical inequality.

Both SU3 and PSU3 conventions, the full Borel, the original/geometric
markings and the literal Q.q image of S are retained. The final application
gives |T| >= 2^n and |D| >= 2^(7n) on that same image. No original-factor
perfectness assumption is added.

Source: Fong--Seitz I (6D), printed p.42, through parameter equality.
The equal-parameter and mixed linear-unitary contradictions, and the
oriented (6E) assembly, remain further obligations. The marked quotient,
split and rotation-six inputs retain their earlier producers and their
final discharge in source assembly; the small unitary exclusions remain
in their existing modules.
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
private theorem unitary_cartan_inputs (j : Fin 2)
    (hmodel : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
    simpleRemainder Q split j ≤ localKernel Q j ∧
      Nonempty (localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∧
      Nat.card (simpleRoot Q split j) = (2^n)^3 := by
  let := h.finite_local j
  obtain ⟨T,hT⟩ := h.sylow j
  rcases hmodel with ⟨⟨μ⟩⟩ | ⟨⟨μ⟩⟩
  · have hK := projectiveUnitary_remainder_le_kernel Q e h split j T hT J hn hcard hconj μ
    exact ⟨hK,⟨projectiveUnitaryFactorLocalEquiv Q e h split j T hT J
      (by omega) hcard hconj hK μ⟩,
      projectiveUnitary_simpleRoot_card Q e h split j T hT J (by omega) hcard hconj μ⟩
  · have hK := specialUnitary_remainder_le_kernel Q e h split j T hT J hn hcard hconj μ
    exact ⟨hK,⟨specialUnitaryFactorLocalEquiv Q e h split j T hT J
      (by omega) hcard hconj hK μ⟩,
      specialUnitary_simpleRoot_card Q e h split j T hT J (by omega) hcard hconj μ⟩

include e h split hn hcard hconj in
/-- A nontrivial Cartan-invariant normal subgroup of the actual unitary
root has at least fixed-field order, in either scalar convention. -/
theorem original_unitary_root_normal_card_bound (j : Fin 2)
    (hmodel : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup))
    (W : Subgroup (X ⧸ Q.D)) (hW : W ≤ simpleRoot Q split j) (hne : W ≠ ⊥)
    (hWN : simpleRoot Q split j ≤ normalizer (W : Set (X ⧸ Q.D)))
    (hH : Q.tits.B ⊓ Q.tits.N ≤ normalizer (W : Set (X ⧸ Q.D))) : 2^n ≤ Nat.card W := by
  obtain ⟨hK,⟨μ⟩,_⟩ := unitary_cartan_inputs Q e h split J hn hcard hconj j hmodel
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n*2)
    (by simpa only [pow_mul,Nat.card_eq_fintype_card] using hcard)
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hconj
  let J₀ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
  obtain ⟨a⟩ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
    J (2^n) hcard hf
  exact unitary_simpleRoot_normal_card_bound Q split J₀ hn hcard hf rfl
    j (μ.trans a) hK W hW hne hWN hH

variable {E : Type*} [Field E] [Finite E] (I : HermitianForm 3 E)
  {m : ℕ} (hm : 2 ≤ m) (hE : Nat.card E = (2^m)^2)
  (hconjE : ∀ x, I.conj x=x^(2^m))

include e h split hn hcard hconj hm hE hconjE in
/-- The nontrivial third term has the source Cartan lower bound. Its
full size survives in the effective derived-section inequality. -/
theorem original_unitary_pair_cartan_lower_bounds
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j) (hmn : m ≤ n)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup I) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* I.specialSubgroup))
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
    let V := simpleRemainder Q split j
    2^m ≤ Nat.card (⁅⁅V,V⁆,V⁆ : Subgroup (X ⧸ Q.D)) ∧
      2^(6*n+m) ≤ Nat.card (⁅V,V⁆ : Subgroup (X ⧸ Q.D)) ∧ 3*n ≤ 4*m := by
  let V := simpleRemainder Q split j
  let D := ⁅V,V⁆
  let T := ⁅D,V⁆
  obtain ⟨hKi,_⟩ := unitary_cartan_inputs Q e h split I hm hE hconjE i hi
  obtain ⟨hKj,_⟩ := unitary_cartan_inputs Q e h split J hn hcard hconj j hj
  have hK (k : Fin 2) : simpleRemainder Q split k ≤ localKernel Q k := by
    by_cases he : k=i
    · subst k; exact hKi
    · have he' : k=j := by omega
      subst k; exact hKj
  have hroot (k : Fin 2) (W : Subgroup (X ⧸ Q.D)) (hW : W ≤ simpleRoot Q split k)
      (hne : W ≠ ⊥) (hWN : simpleRoot Q split k ≤ normalizer (W : Set (X ⧸ Q.D)))
      (hH : Q.tits.B ⊓ Q.tits.N ≤ normalizer (W : Set (X ⧸ Q.D))) : 2^m ≤ Nat.card W := by
    by_cases he : k=i
    · subst k
      exact original_unitary_root_normal_card_bound Q e h split I hm hE hconjE i hi W hW hne hWN hH
    · have he' : k=j := by omega
      subst k
      exact (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hmn).trans
        (original_unitary_root_normal_card_bound Q e h split J hn hcard hconj j hj W hW hne hWN hH)
  have hT : 2^m ≤ Nat.card T := radical_normal_subgroup_card_bound Q split hhex hK
    (2^m) hroot j T ((radical_triple_le_derived Q split j).trans (commutator_le_self V))
    (original_unitary_pair_triple_ne_bot Q e h split J hn hcard hconj I hm hE hconjE
      hhex i j hij hmn hi hj)
    (normalizer_commutator_ge_right D V)
    (inf_le_left.trans ((Q.tits.B_le_standardParabolic _).trans (radical_triple_normalized Q split j hKj)))
  have hD : 2^(6*n+m) ≤ Nat.card D := by
    rw [pow_add]
    exact (Nat.mul_le_mul_left _ hT).trans
      (original_unitary_pair_lowerCentral_control Q e h split J hn hcard hconj
        I hm hE hconjE hhex i j hij hi hj).2
  have hu := (original_unitary_pair_derived_control Q e h split J hn hcard hconj
    I hm hE hconjE hhex i j hij hmn hi hj).2.1
  have he := (Nat.pow_le_pow_iff_right (by decide : 1 < (2:ℕ))).mp (hD.trans hu)
  exact ⟨hT,hD,by omega⟩

include e h split hn hcard hconj hm hE hconjE in
private theorem unitary_pair_not_lt
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j) (hmn : m < n)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup I) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* I.specialSubgroup))
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) : False := by
  let V := simpleRemainder Q split j
  let D := ⁅V,V⁆
  have hD := (original_unitary_pair_cartan_lower_bounds Q e h split J hn hcard hconj
    I hm hE hconjE hhex i j hij hmn.le hi hj).2.1
  obtain ⟨_,_,hci⟩ := unitary_cartan_inputs Q e h split I hm hE hconjE i hi
  obtain ⟨_,_,hcj⟩ := unitary_cartan_inputs Q e h split J hn hcard hconj j hj
  have hV : Nat.card V = 2^(9*m+6*n) := by
    rw [Nat.card_congr (radicalCoordinates Q split hhex i j hij).symm]
    simp only [Nat.card_prod,rootAt,card_rightConjugate,hci,hcj,←pow_mul,←pow_add]
    congr 1
    omega
  have hPhi := original_unitary_pair_frattini_eq_commutator Q e h split J hn hcard hconj
    I hm hE hconjE hhex i j hij hi hj
  have hphiD : Nat.card (frattini V) = Nat.card D := by
    rw [hPhi]
    change Nat.card (_root_.commutator V) = Nat.card (⁅V,V⁆ : Subgroup (X ⧸ Q.D))
    rw [←map_subtype_commutator]
    exact Nat.card_congr ((_root_.commutator V).equivMapOfInjective V.subtype V.subtype_injective).toEquiv
  have hp := (frattini V).index_mul_card
  change Nat.card (V ⧸ frattini V)*Nat.card (frattini V) = Nat.card V at hp
  rw [hphiD,hV] at hp
  have hb : Nat.card (V ⧸ frattini V)*2^(6*n+m) ≤ 2^(9*m+6*n) :=
    (Nat.mul_le_mul_left _ hD).trans_eq hp
  have ho := original_unitary_pair_unequal_quotient_orders Q e h split J hn hcard hconj
    I hm hE hconjE hhex i j hij hmn hi hj
  rcases ho with ho | ho | ho <;>
    rw [ho,←pow_add] at hb <;>
    have he := (Nat.pow_le_pow_iff_right (by decide : 1 < (2:ℕ))).mp hb <;> omega

include e h split hn hcard hconj hm hE hconjE in
/-- Regular unitary endpoints in the actual hexagon have the same
field degree. Both orientations and all four scalar-convention pairs are included. -/
theorem original_unitary_pair_parameters_eq
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup I) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* I.specialSubgroup))
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) : m=n := by
  rcases lt_trichotomy m n with hlt | he | hgt
  · exact (unitary_pair_not_lt Q e h split J hn hcard hconj I hm hE hconjE hhex i j hij hlt hi hj).elim
  · exact he
  · exact (unitary_pair_not_lt Q e h split I hm hE hconjE J hn hcard hconj hhex j i hij.symm hgt hj hi).elim

include e h split hn hcard hconj hm hE hconjE in
/-- Parameter equality and the strengthened lower-central bounds on the
original or geometric Sylow image, using its literal source reflection. -/
theorem original_unitary_pair_cartan_control_on_sylow
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup I) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* I.specialSubgroup))
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
    let V := (sylowMap Q e h).range ⊓ rightConjugate (sylowMap Q e h).range
      ((UnitarySource.actorReflection Q split j).val : X ⧸ Q.D)
    m=n ∧ 2^n ≤ Nat.card (⁅⁅V,V⁆,V⁆ : Subgroup (X ⧸ Q.D)) ∧
      2^(7*n) ≤ Nat.card (⁅V,V⁆ : Subgroup (X ⧸ Q.D)) := by
  dsimp only
  rw [←marked_radical_eq h Q e split j (UnitarySource.actorReflection Q split j).val
    (UnitarySource.actorReflection Q split j).class_eq]
  have he := original_unitary_pair_parameters_eq Q e h split J hn hcard hconj
    I hm hE hconjE hhex i j hij hi hj
  have hb := original_unitary_pair_cartan_lower_bounds Q e h split J hn hcard hconj
    I hm hE hconjE hhex i j hij he.le hi hj
  dsimp only at hb
  rw [he] at hb
  refine ⟨he,hb.1,?_⟩
  convert hb.2.1 using 1
  congr 1
  omega

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The source parameter equality and both lower-central bounds on the
literal Q.q image of S. The full Borel and endpoint markings are retained. -/
theorem quotient_unitary_pair_cartan_control
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
    m=n ∧ 2^n ≤ Nat.card (⁅⁅V,V⁆,V⁆ : Subgroup ((generated L S) ⧸ Q.D)) ∧
      2^(7*n) ≤ Nat.card (⁅V,V⁆ : Subgroup ((generated L S) ⧸ Q.D)) := by
  dsimp only
  rw [quotient_sourceS_image_eq_unipotent h Q split]
  have hh := original_unitary_pair_cartan_control_on_sylow Q (originalMarkedIso Q) h split
    J hn hcard hconj I hm hE hconjE hhex i j hij hi hj
  dsimp only at hh
  rwa [MarkedLocal.sylow_range Q (originalMarkedIso Q) h split] at hh

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
