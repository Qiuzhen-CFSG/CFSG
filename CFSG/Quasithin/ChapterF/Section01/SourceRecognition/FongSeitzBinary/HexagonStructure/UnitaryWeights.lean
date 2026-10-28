module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.UnitaryWeights
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.UnitaryDerivedRoots
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFactorAction

/-!
# Original unitary roots and Cartan sections in a hexagon

The actual original SU₃ or PSU₃ quotient identifies the faithful local
action, including its scalar kernel. Form transport then gives both Cartan
constituents on every literal Weyl-conjugate root: its center and its
quadratic-dimensional Frattini quotient.

For two regular unitary endpoints, the five root maps control all invariant
sections of the actual radical quotient. The previous whole-root exclusions
make the four nonmiddle maps injective and identify their exact intersections
with the derived radical as their centers. The original and geometric
markings use the full Borel; the last application retains the literal Q.q.
No endpoint-perfectness assumption is added.

Source: Fong--Seitz I (6D), printed p.42. These constituent and intersection
results give the three possible unequal-degree radical quotient orders
and the necessary parameter ratios at degrees 6n and 7n. The remaining
regular-unitary contradiction is not asserted here.
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
private theorem regular_unitary_local_model (j : Fin 2)
    (hmodel : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
    simpleRemainder Q split j ≤ localKernel Q j ∧
      Nonempty (localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J) := by
  let := h.finite_local j
  obtain ⟨T,hT⟩ := h.sylow j
  rcases hmodel with ⟨⟨μ⟩⟩ | ⟨⟨μ⟩⟩
  · have hK := projectiveUnitary_remainder_le_kernel Q e h split j T hT J hn hcard hconj μ
    exact ⟨hK,⟨projectiveUnitaryFactorLocalEquiv Q e h split j T hT J
      (by omega) hcard hconj hK μ⟩⟩
  · have hK := specialUnitary_remainder_le_kernel Q e h split j T hT J hn hcard hconj μ
    exact ⟨hK,⟨specialUnitaryFactorLocalEquiv Q e h split j T hT J
      (by omega) hcard hconj hK μ⟩⟩

include e h split hn hcard hconj in
/-- The actual root center and quadratic Frattini constituent, for either original scalar convention. -/
theorem original_unitary_root_cartan_constituents (j : Fin 2) (w : Weyl Q)
    (hmodel : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
    frattini (rootAt Q split j w) = center (rootAt Q split j w) ∧
      Nat.card (frattini (rootAt Q split j w)) = 2^n ∧
      (rootAtCartanFrattiniRepresentation Q split j w).IsIrreducible ∧
      Module.finrank (ZMod 2)
        (Additive (rootAt Q split j w ⧸ frattini (rootAt Q split j w))) = 2*n := by
  obtain ⟨hK,⟨μ⟩⟩ := regular_unitary_local_model Q e h split J hn hcard hconj j hmodel
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n*2)
    (by simpa only [pow_mul,Nat.card_eq_fintype_card] using hcard)
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hconj
  let J₀ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
  obtain ⟨a⟩ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
    J (2^n) hcard hf
  have hZ := unitary_rootAt_frattini_center Q split J₀ hn hcard hf rfl j (μ.trans a) hK w
  have hρ := unitary_rootAt_cartan_frattini_irreducible Q split J₀ hn hcard hf rfl j (μ.trans a) hK w
  exact ⟨hZ.1,hZ.2,hρ⟩

include e h split hn hcard hconj in
/-- The other Cartan constituent is the whole center: every nonzero invariant
subgroup fills it, on every literal conjugate root. -/
theorem original_unitary_root_center_irreducible (j : Fin 2) (w : Weyl Q)
    (hmodel : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup))
    (A : Subgroup (X ⧸ Q.D))
    (hA : A ≤ (center (rootAt Q split j w)).map (rootAt Q split j w).subtype)
    (hne : A ≠ ⊥) (hH : Q.tits.B ⊓ Q.tits.N ≤ normalizer (A : Set (X ⧸ Q.D))) :
    A = (center (rootAt Q split j w)).map (rootAt Q split j w).subtype := by
  obtain ⟨hK,⟨μ⟩⟩ := regular_unitary_local_model Q e h split J hn hcard hconj j hmodel
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n*2)
    (by simpa only [pow_mul,Nat.card_eq_fintype_card] using hcard)
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hconj
  let J₀ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
  obtain ⟨a⟩ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
    J (2^n) hcard hf
  exact QuadrangleStructure.rootAt_center_eq_of_torus_invariant Q split
    (QuadrangleStructure.unitary_sylow_center_irreducible J₀ (by omega) hcard hf rfl)
    j (μ.trans a) hK w A hA hne hH

variable {E : Type*} [Field E] [Finite E] (I : HermitianForm 3 E)
  {m : ℕ} (hm : 2 ≤ m) (hE : Nat.card E = (2^m)^2)
  (hconjE : ∀ x, I.conj x=x^(2^m))

include e h split hn hcard hconj hm hE hconjE in
/-- Every Cartan-invariant section of the actual radical quotient has a
subset sum of the five source dimensions 2m,2n,2m,2n,2m. -/
theorem original_unitary_pair_radical_section_dimensions
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup I) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* I.specialSubgroup))
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
    ∃ hKj : simpleRemainder Q split j ≤ localKernel Q j,
      ∀ (U : Subrepresentation (radicalHRepresentation Q split j hKj))
        (N : Subrepresentation U.toRepresentation),
        ∃ s : Finset (Fin 5), Module.finrank (ZMod 2) (U ⧸ N.toSubmodule) =
          ∑ t ∈ s, if t = 1 ∨ t = 3 then 2*n else 2*m := by
  obtain ⟨hKj,_⟩ := regular_unitary_local_model Q e h split J hn hcard hconj j hj
  refine ⟨hKj,?_⟩
  intro U N
  apply radical_section_dimension_of_root_profile Q split hhex i j hij hKj
    (fun t => if t = 1 ∨ t = 3 then 2*n else 2*m) ?_ U N
  intro t
  fin_cases t <;> dsimp only [radicalRootKind,radicalRootWord]
  · exact (original_unitary_root_cartan_constituents Q e h split I hm hE hconjE i 1 hi).2.2
  · exact (original_unitary_root_cartan_constituents Q e h split J hn hcard hconj j (Q.simple i) hj).2.2
  · exact (original_unitary_root_cartan_constituents Q e h split I hm hE hconjE i (Q.simple j*Q.simple i) hi).2.2
  · exact (original_unitary_root_cartan_constituents Q e h split J hn hcard hconj j (Q.simple i*Q.simple j) hj).2.2
  · exact (original_unitary_root_cartan_constituents Q e h split I hm hE hconjE i (Q.simple j) hi).2.2

include e h split hn hcard hconj hm hE hconjE in
/-- Every irreducible Cartan section of the actual radical quotient has
exactly one of the two source dimensions, including all scalar conventions. -/
theorem original_unitary_pair_irreducible_section_dimension
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup I) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* I.specialSubgroup))
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
    ∃ hKj : simpleRemainder Q split j ≤ localKernel Q j,
      ∀ (U : Subrepresentation (radicalHRepresentation Q split j hKj))
        (N : Subrepresentation U.toRepresentation),
        N.quotientRepresentation.IsIrreducible →
          Module.finrank (ZMod 2) (U ⧸ N.toSubmodule) = 2*m ∨
          Module.finrank (ZMod 2) (U ⧸ N.toSubmodule) = 2*n := by
  obtain ⟨hKj,_⟩ := regular_unitary_local_model Q e h split J hn hcard hconj j hj
  refine ⟨hKj,?_⟩
  intro U N hN
  obtain ⟨t,ht⟩ := radical_irreducible_section_dimension_of_root_profile Q split hhex i j hij hKj
    (fun t => if t = 1 ∨ t = 3 then 2*n else 2*m) (by
    intro t
    fin_cases t <;> dsimp only [radicalRootKind,radicalRootWord]
    · exact (original_unitary_root_cartan_constituents Q e h split I hm hE hconjE i 1 hi).2.2
    · exact (original_unitary_root_cartan_constituents Q e h split J hn hcard hconj j (Q.simple i) hj).2.2
    · exact (original_unitary_root_cartan_constituents Q e h split I hm hE hconjE i (Q.simple j*Q.simple i) hi).2.2
    · exact (original_unitary_root_cartan_constituents Q e h split J hn hcard hconj j (Q.simple i*Q.simple j) hj).2.2
    · exact (original_unitary_root_cartan_constituents Q e h split I hm hE hconjE i (Q.simple j) hi).2.2
    ) U N hN
  by_cases hh : t = 1 ∨ t = 3
  · exact Or.inr (by simpa only [if_pos hh] using ht)
  · exact Or.inl (by simpa only [if_neg hh] using ht)

include e h split hn hcard hconj hm hE hconjE in
/-- The four nonmiddle root maps inject into the actual radical quotient;
their kernels before projection are exactly their intrinsic centers. -/
theorem original_unitary_pair_nonmiddle_constituents
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j) (hmn : m ≤ n)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup I) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* I.specialSubgroup))
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
    ∃ hKj : simpleRemainder Q split j ≤ localKernel Q j,
      ∀ t : Fin 5, t ≠ 2 →
        Function.Injective (radicalRootIntertwiner Q split hhex i j hij hKj t) ∧
        rootAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t) ⊓
            ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ =
          (center (rootAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t))).map
            (rootAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t)).subtype := by
  obtain ⟨hKj,_⟩ := regular_unitary_local_model Q e h split J hn hcard hconj j hj
  have hΦ := original_unitary_pair_frattini_eq_commutator Q e h split J hn hcard hconj
    I hm hE hconjE hhex i j hij hi hj
  have hnot := (original_unitary_pair_derived_control Q e h split J hn hcard hconj
    I hm hE hconjE hhex i j hij hmn hi hj).2.2.2
  have hD : (frattini (simpleRemainder Q split j)).map (simpleRemainder Q split j).subtype =
      ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ := by
    rw [hΦ,map_subtype_commutator]
  refine ⟨hKj,?_⟩
  intro t ht
  let k := radicalRootKind i j t
  let w := radicalRootWord Q i j t
  have hroot : frattini (rootAt Q split k w) = center (rootAt Q split k w) ∧
      (rootAtCartanFrattiniRepresentation Q split k w).IsIrreducible := by
    by_cases hk : k=i
    · rw [hk]
      have hh := original_unitary_root_cartan_constituents Q e h split I hm hE hconjE i w hi
      exact ⟨hh.1,hh.2.2.1⟩
    · have hk' : k=j := by omega
      rw [hk']
      have hh := original_unitary_root_cartan_constituents Q e h split J hn hcard hconj j w hj
      exact ⟨hh.1,hh.2.2.1⟩
  have hnroot : ¬ rootAt Q split k w ≤
      (frattini (simpleRemainder Q split j)).map (simpleRemainder Q split j).subtype := by
    rw [hD]; exact hnot t ht
  have hh := root_frattini_intertwiner_injective_and_intersection Q split j hKj k w
    (radicalRoot_le Q split hhex i j hij t) hroot.2 hnroot
  refine ⟨hh.1,?_⟩
  have hinter := hh.2
  rw [hD,hroot.1] at hinter
  exact hinter

include e h split hn hcard hconj hm hE hconjE in
/-- The exact intersections in the original or geometric Sylow-image radical. -/
theorem original_unitary_pair_nonmiddle_centers_on_sylow
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j) (hmn : m ≤ n)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup I) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* I.specialSubgroup))
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
    let V := (sylowMap Q e h).range ⊓ rightConjugate (sylowMap Q e h).range
      ((UnitarySource.actorReflection Q split j).val : X ⧸ Q.D)
    ∀ t : Fin 5, t ≠ 2 →
      rootAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t) ⊓ ⁅V,V⁆ =
        (center (rootAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t))).map
          (rootAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t)).subtype := by
  dsimp only
  rw [←marked_radical_eq h Q e split j (UnitarySource.actorReflection Q split j).val
    (UnitarySource.actorReflection Q split j).class_eq]
  obtain ⟨_,hh⟩ := original_unitary_pair_nonmiddle_constituents Q e h split J hn hcard hconj
    I hm hE hconjE hhex i j hij hmn hi hj
  exact fun t ht => (hh t ht).2

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The same four exact center intersections on the literal Q.q image of S. -/
theorem quotient_unitary_pair_nonmiddle_centers
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
    ∀ t : Fin 5, t ≠ 2 →
      rootAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t) ⊓ ⁅V,V⁆ =
        (center (rootAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t))).map
          (rootAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t)).subtype := by
  dsimp only
  rw [quotient_sourceS_image_eq_unipotent h Q split]
  have hh := original_unitary_pair_nonmiddle_centers_on_sylow Q (originalMarkedIso Q) h split
    J hn hcard hconj I hm hE hconjE hhex i j hij hmn hi hj
  dsimp only at hh
  rwa [MarkedLocal.sylow_range Q (originalMarkedIso Q) h split] at hh

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure

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
  {E : Type*} [Field E] [Finite E] (I : HermitianForm 3 E)
  {m : ℕ} (hm : 2 ≤ m) (hE : Nat.card E = (2^m)^2)
  (hconjE : ∀ x, I.conj x=x^(2^m))

include e h split hn hcard hconj hm hE hconjE in
/-- In unequal degree the actual radical Frattini quotient has one of the
three orders in the source Cartan calculation. -/
theorem original_unitary_pair_unequal_quotient_orders
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j) (hmn : m < n)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup I) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* I.specialSubgroup))
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
    let V := simpleRemainder Q split j
    Nat.card (V ⧸ frattini V) = 2^(6*m+2*n) ∨
      Nat.card (V ⧸ frattini V) = 2^(4*m+4*n) ∨
      Nat.card (V ⧸ frattini V) = 2^(6*m+4*n) := by
  obtain ⟨hKj,_⟩ := regular_unitary_local_model Q e h split J hn hcard hconj j hj
  let V := simpleRemainder Q split j
  let C := (radicalSection Q split j hKj).EffectiveCarrier
  let d := Module.finrank (ZMod 2) (Additive C)
  obtain ⟨s,hs⟩ := radical_dimension_of_root_profile Q split hhex i j hij hKj
    (fun t => if t = 1 ∨ t = 3 then 2*n else 2*m) (by
    intro t
    fin_cases t <;> dsimp only [radicalRootKind,radicalRootWord]
    · exact (original_unitary_root_cartan_constituents Q e h split I hm hE hconjE i 1 hi).2.2
    · exact (original_unitary_root_cartan_constituents Q e h split J hn hcard hconj j (Q.simple i) hj).2.2
    · exact (original_unitary_root_cartan_constituents Q e h split I hm hE hconjE i (Q.simple j*Q.simple i) hi).2.2
    · exact (original_unitary_root_cartan_constituents Q e h split J hn hcard hconj j (Q.simple i*Q.simple j) hj).2.2
    · exact (original_unitary_root_cartan_constituents Q e h split I hm hE hconjE i (Q.simple j) hi).2.2)
  have hc : Nat.card (V ⧸ frattini V) = 2^d := by
    have he : Nat.card C = Nat.card (V ⧸ frattini V) := by
      change (radicalSection Q split j hKj).effectiveDenominator.index = _
      rw [suzuki_radical_effectiveDenominator Q split j hKj]
      rfl
    rw [←he]
    change Nat.card (Additive C) = _
    simpa only [Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive C))
  have hlo := original_unitary_radical_two_layers Q e h split J hn hcard hconj hhex i j hij hj
  dsimp only at hlo
  rw [←marked_radical_eq h Q e split j (UnitarySource.actorReflection Q split j).val
    (UnitarySource.actorReflection Q split j).class_eq] at hlo
  have hb : 6*n ≤ d := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (hc ▸ hlo.1)
  dsimp only
  rw [hc]
  rcases unequal_unitary_weight_sum hmn hb s hs with hd | hd | hd
  · exact Or.inl (congrArg (fun a => 2^a) hd)
  · exact Or.inr (Or.inl (congrArg (fun a => 2^a) hd))
  · exact Or.inr (Or.inr (congrArg (fun a => 2^a) hd))

include e h split hn hcard hconj hm hE hconjE in
/-- The minimal dimension forces the boundary ratio 3m=2n; the next
source degree forces 4m=3n or 6m=5n. These are necessary conditions on
the same radical quotient, not an existence assertion or a degree-gap theorem. -/
theorem original_unitary_pair_small_quotient_ratios
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j) (hmn : m < n)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup I) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* I.specialSubgroup))
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
    let V := simpleRemainder Q split j
    (Nat.card (V ⧸ frattini V) = 2^(6*n) → 3*m=2*n) ∧
      (Nat.card (V ⧸ frattini V) = 2^(7*n) → 4*m=3*n ∨ 6*m=5*n) := by
  have hh := original_unitary_pair_unequal_quotient_orders Q e h split J hn hcard hconj
    I hm hE hconjE hhex i j hij hmn hi hj
  have hb := original_unitary_pair_parameter_bound Q e h split J hn hcard hconj
    I (by omega) hE hconjE hhex i j hij hi hj
  dsimp only at hh ⊢
  constructor
  · intro he
    rw [he] at hh
    rcases hh with hh | hh | hh <;>
      have hd := Nat.pow_right_injective (by decide : 1 < (2:ℕ)) hh <;> omega
  · intro he
    rw [he] at hh
    rcases hh with hh | hh | hh <;>
      have hd := Nat.pow_right_injective (by decide : 1 < (2:ℕ)) hh <;> omega

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The three source quotient orders on the literal Q.q image of S,
with its original full Borel and both possible scalar conventions. -/
theorem quotient_unitary_pair_unequal_quotient_orders
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x=x^(2^n))
    {E : Type*} [Field E] [Finite E] (I : HermitianForm 3 E)
    {m : ℕ} (hm : 2 ≤ m) (hE : Nat.card E = (2^m)^2)
    (hconjE : ∀ x, I.conj x=x^(2^m))
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j) (hmn : m < n)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup I) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* I.specialSubgroup))
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
    let V := ((S.subgroupOf (generated L S)).map Q.q) ⊓
      rightConjugate ((S.subgroupOf (generated L S)).map Q.q)
        ((UnitarySource.actorReflection Q split j).val : (generated L S) ⧸ Q.D)
    Nat.card (V ⧸ frattini V) = 2^(6*m+2*n) ∨
      Nat.card (V ⧸ frattini V) = 2^(4*m+4*n) ∨
      Nat.card (V ⧸ frattini V) = 2^(6*m+4*n) := by
  have hV := marked_radical_eq h Q (originalMarkedIso Q) split j
    (UnitarySource.actorReflection Q split j).val (UnitarySource.actorReflection Q split j).class_eq
  rw [MarkedLocal.sylow_range Q (originalMarkedIso Q) h split] at hV
  dsimp only
  rw [quotient_sourceS_image_eq_unipotent h Q split,←hV]
  exact original_unitary_pair_unequal_quotient_orders Q (originalMarkedIso Q) h split
    J hn hcard hconj I hm hE hconjE hhex i j hij hmn hi hj

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
