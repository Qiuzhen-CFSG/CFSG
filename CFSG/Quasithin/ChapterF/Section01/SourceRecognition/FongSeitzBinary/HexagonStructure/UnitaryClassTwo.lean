module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.UnitaryClassTwo
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.UnitaryLowerCentral

/-!
# Excluding class-two radicals in regular unitary hexagons

The actual unitary root centers equal their derived subgroups, by the
previously proved root-square calculation and the binary Frattini formula.
If V = U_sj had class at most two, successive ordered root coordinates
would give |Z(V)| <= 2^(3m+2n). The effective derived section gives
|V'| >= 2^(6n). For m <= n these bounds contradict V' <= Z(V).
Consequently the actual third term [V',V] is nontrivial.

When m < n, a radical Frattini quotient of order 2^(6n) had already been
shown to force class at most two. The contradiction now excludes that
quotient order. Both special and projective unitary conventions and both
orientations are retained, without original-factor perfectness. The
original/geometric and literal Q.q applications use the same Sylow image
and the same right-conjugation reflection.

The Cartan lower bound for the nontrivial third term, remaining regular
unitary contradictions and oriented (6E) assembly remain source obligations.
Marked quotient, split and rotation-six inputs retain their earlier producers
and their final discharge in source assembly.

Source: Fong--Seitz I (6D), printed p.42, from the five-root center bound
through the exclusion of the minimal unequal-degree quotient.
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
/-- The actual regular unitary root center equals its derived subgroup. -/
theorem original_unitary_root_center_eq_commutator (j : Fin 2)
    (hmodel : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
    center (simpleRoot Q split j) = _root_.commutator (simpleRoot Q split j) := by
  let A := simpleRoot Q split j
  have hZ := (original_unitary_root_cartan_constituents Q e h split J hn hcard hconj j 1 hmodel).1
  rw [rootAt_one] at hZ
  have hp : IsPGroup 2 A := split.isTwo.to_le (simpleRoot_le Q split j)
  let : Fact (IsPGroup 2 A) := ⟨hp⟩
  rw [←hZ]
  apply le_antisymm _ (commutator_le_frattini_of_isPGroup (p := 2))
  rw [hp.frattini_eq_closure_squares]
  apply (closure_le _).mpr
  rintro _ ⟨x,rfl⟩
  exact original_unitary_root_square_mem_commutator Q e h split J hn hcard hconj j hmodel x

variable {E : Type*} [Field E] [Finite E] (I : HermitianForm 3 E)
  {m : ℕ} (hm : 2 ≤ m) (hE : Nat.card E = (2^m)^2)
  (hconjE : ∀ x, I.conj x=x^(2^m))

include e h split hn hcard hconj hm hE hconjE in
/-- In the class-two case, successive literal root coordinates bound the whole radical center. -/
theorem original_unitary_pair_classTwo_center_bound
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup I) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* I.specialSubgroup))
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup))
    (hclass : ⁅⁅simpleRemainder Q split j,simpleRemainder Q split j⁆,
      simpleRemainder Q split j⁆ = ⊥) :
    Nat.card (center (simpleRemainder Q split j)) ≤ 2^(3*m+2*n) := by
  obtain ⟨hKj,_⟩ := original_unitary_pair_derivedCentral_section Q e h split J hn hcard hconj
    I hm hE hconjE hhex i j hij hi hj
  obtain ⟨hKi,_⟩ := original_unitary_pair_derivedCentral_section Q e h split I hm hE hconjE
    J hn hcard hconj hhex j i hij.symm hj hi
  have hK (k : Fin 2) : simpleRemainder Q split k ≤ localKernel Q k := by
    by_cases he : k=i
    · subst k; exact hKi
    · have he' : k=j := by omega
      subst k; exact hKj
  have hc (k : Fin 2) : center (simpleRoot Q split k) ≤ _root_.commutator (simpleRoot Q split k) := by
    by_cases he : k=i
    · subst k
      exact (original_unitary_root_center_eq_commutator Q e h split I hm hE hconjE i hi).le
    · have he' : k=j := by omega
      subst k
      exact (original_unitary_root_center_eq_commutator Q e h split J hn hcard hconj j hj).le
  have hb := radical_classTwo_center_card_bound Q split hhex hK hc i j hij hclass
  have hci := original_unitary_root_cartan_constituents Q e h split I hm hE hconjE i 1 hi
  have hcj := original_unitary_root_cartan_constituents Q e h split J hn hcard hconj j 1 hj
  have hiZ : Nat.card (center (rootAt Q split i 1)) = 2^m := hci.1 ▸ hci.2.1
  have hjZ : Nat.card (center (rootAt Q split j 1)) = 2^n := hcj.1 ▸ hcj.2.1
  rw [rootAt_one] at hiZ hjZ
  rw [hiZ,hjZ,←pow_mul,←pow_mul,←pow_add] at hb
  convert hb using 1
  congr 1
  omega

include e h split hn hcard hconj hm hE hconjE in
/-- The actual third lower-central term is nontrivial for regular unitary pairs. -/
theorem original_unitary_pair_triple_ne_bot
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j) (hmn : m ≤ n)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup I) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* I.specialSubgroup))
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
    ⁅⁅simpleRemainder Q split j,simpleRemainder Q split j⁆,
      simpleRemainder Q split j⁆ ≠ ⊥ := by
  intro hclass
  let V := simpleRemainder Q split j
  let D := ⁅V,V⁆
  have hcen : D ≤ centralizer (V : Set (X ⧸ Q.D)) :=
    commutator_eq_bot_iff_le_centralizer.mp hclass
  let f : D → center V := fun x => ⟨⟨x,(commutator_le_self V) x.property⟩,by
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (hcen x.property y y.property)⟩
  have hinj : Function.Injective f := by
    intro x y he
    exact Subtype.ext (congrArg (fun z : center V => (z.val : X ⧸ Q.D)) he)
  have hD : Nat.card D ≤ 2^(3*m+2*n) := (Nat.card_le_card_of_injective f hinj).trans
    (original_unitary_pair_classTwo_center_bound Q e h split J hn hcard hconj I hm hE hconjE
      hhex i j hij hi hj hclass)
  have hlo := (original_unitary_pair_lowerCentral_control Q e h split J hn hcard hconj
    I hm hE hconjE hhex i j hij hi hj).2
  rw [hclass,Subgroup.card_bot,mul_one] at hlo
  have hh := (Nat.pow_le_pow_iff_right (by decide : 1 < (2:ℕ))).mp (hlo.trans hD)
  omega

include e h split hn hcard hconj hm hE hconjE in
/-- The source quotient cannot have the minimal unitary degree when the two parameters differ. -/
theorem original_unitary_pair_quotient_ne_minimal
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j) (hmn : m < n)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup I) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* I.specialSubgroup))
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
    Nat.card (simpleRemainder Q split j ⧸ frattini (simpleRemainder Q split j)) ≠ 2^(6*n) := by
  intro hquot
  exact original_unitary_pair_triple_ne_bot Q e h split J hn hcard hconj I hm hE hconjE
    hhex i j hij hmn.le hi hj
    (original_unitary_pair_minimal_quotient_classTwo Q e h split J hn hcard hconj I hm hE hconjE
      hhex i j hij hmn hi hj hquot)

include e h split hn hcard hconj hm hE hconjE in
/-- Both exclusions on the original or geometric Sylow image, with the actual source reflection. -/
theorem original_unitary_pair_classTwo_exclusion_on_sylow
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j) (hmn : m ≤ n)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup I) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* I.specialSubgroup))
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
    let V := (sylowMap Q e h).range ⊓ rightConjugate (sylowMap Q e h).range
      ((UnitarySource.actorReflection Q split j).val : X ⧸ Q.D)
    ⁅⁅V,V⁆,V⁆ ≠ ⊥ ∧
      (m < n → Nat.card (V ⧸ frattini V) ≠ 2^(6*n)) := by
  dsimp only
  rw [←marked_radical_eq h Q e split j (UnitarySource.actorReflection Q split j).val
    (UnitarySource.actorReflection Q split j).class_eq]
  exact ⟨original_unitary_pair_triple_ne_bot Q e h split J hn hcard hconj I hm hE hconjE
    hhex i j hij hmn hi hj,fun hlt =>
      original_unitary_pair_quotient_ne_minimal Q e h split J hn hcard hconj I hm hE hconjE
        hhex i j hij hlt hi hj⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Third-term nontriviality and minimal-quotient exclusion on the literal Q.q image of S. -/
theorem quotient_unitary_pair_classTwo_exclusion
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
    ⁅⁅V,V⁆,V⁆ ≠ ⊥ ∧
      (m < n → Nat.card (V ⧸ frattini V) ≠ 2^(6*n)) := by
  dsimp only
  rw [quotient_sourceS_image_eq_unipotent h Q split]
  have hh := original_unitary_pair_classTwo_exclusion_on_sylow Q (originalMarkedIso Q) h split
    J hn hcard hconj I hm hE hconjE hhex i j hij hmn hi hj
  dsimp only at hh
  rwa [MarkedLocal.sylow_range Q (originalMarkedIso Q) h split] at hh

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
