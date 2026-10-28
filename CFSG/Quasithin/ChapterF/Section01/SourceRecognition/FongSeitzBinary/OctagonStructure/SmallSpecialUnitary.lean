module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.SmallSpecialUnitary
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.SmallProjectiveUnitary
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.LinearUnitaryLargeDegree
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.BinaryAffineOctagonExclusion
public import Theory.SpecificGroups.SU3.FixedFieldTwo

/-!
# The remaining small special-unitary octagon degrees

The full original SU3(2) quotient identifies the root actor with its actual
order-216 scalar cover. A Hermitian basis change transports that marking
to standard coordinates. The two fixed Frattini layers then exclude
linear degrees four and six. Combined with the earlier parameter reduction,
every special or projective unitary alternative has odd degree b and
linear degree 2b, including b = 1.

The original quotient map, full Borel and both endpoint inclusion squares
remain those of the supplied amalgam isomorphism. No scalar center or
nonperfect endpoint is removed. Source: Fong--Seitz I (6F), printed p.46.
The quadratic-degree commutator contradiction is still required.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
open MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1)
      inf_le_left inf_le_right) Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
include e h split

/-- The original SU3(2) endpoint cannot oppose linear degree four or six. -/
theorem original_small_special_unitary_large_degree_false
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    {a : ℕ} (ha : a=4 ∨ a=6)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hj : IsSU ((L j) ⧸ pCore 2 (L j)) 3 2) : False := by
  obtain ⟨E,hEfield,hEfin,hEcard,⟨μ⟩⟩ := hi
  let : Field E := hEfield
  let : Finite E := hEfin
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hEcard)
  have hE2 : 2 < Nat.card E := by
    rw [hEcard]
    rcases ha with rfl | rfl <;> decide
  have hregular := marked_octagon_regularity_of_linear_quotient Q e h split hE2 hm i μ
  let := h.finite_local i
  let := h.finite_local j
  obtain ⟨Ti,hTi⟩ := h.sylow i
  obtain ⟨Tj,hTj⟩ := h.sylow j
  have hc : Nat.card (simpleRoot Q split i) = Nat.card (quotientSylow Ti) := by
    rw [simpleRoot_card_linear Q e h split i Ti hTi μ]
    exact ((Nat.card_congr (linearSylowEquiv i Ti μ).toEquiv).trans
      ((Nat.card_congr (BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive
        (linearModelSylow i Ti μ)).symm.toEquiv).trans
          (Nat.card_congr Multiplicative.toAdd))).symm
  have hz : center ((L i) ⧸ pCore 2 (L i)) = ⊥ := by
    apply eq_bot_iff.mpr
    intro z hz
    have hh := MulEquivClass.apply_mem_center μ hz
    change μ z ∈ center PSL(2,E) at hh
    rw [BenderSuzuki.ZD.Linear.psl2_center_eq_bot,mem_bot] at hh
    exact μ.injective (hh.trans μ.map_one.symm)
  let μi := (regularFactorLocalEquiv Q e h split i Ti hTi (hregular i).1 hc hz).trans μ
  obtain ⟨F,hF,hfin,J,hcard,hconj,⟨ν⟩⟩ := hj
  have hjcard := specialUnitary_simpleRoot_card_eq_quotientSylow Q e h split j Tj hTj J
    (n:=1) (by decide) (by simpa using hcard) (by simpa using hconj) ν
  let μj := (regularFactorRootEquiv Q e h split j Tj hTj (hregular j).1 hjcard).trans ν
  have hroot : Nat.card (simpleRoot Q split j) = 8 := by
    simpa only [Nat.reducePow] using specialUnitary_simpleRoot_card Q e h split j Tj hTj J
      (n:=1) (by decide) (by simpa using hcard) (by simpa using hconj) ν
  have hfixed : Nat.card {x : F // J.conj x=x}=2 := by
    simpa using FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 1
      (by decide) (by simpa using hcard) (by simpa using hconj)
  obtain ⟨C,hC⟩ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_standard_basis
    J 2 hcard hfixed
  let J₀ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
  let ν₀ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.specialEquiv J C hC
  apply Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure.small_special_large_linear_false
    Q split j J₀ hcard hconj rfl (hregular j).1 (μj.trans ν₀) hroot hm i hij (hregular i).1 μi
  rcases ha with rfl | rfl
  · exact Or.inl hEcard
  · exact Or.inr hEcard

/-- Only the quadratic linear degree remains at the original SU3(2)
endpoint, retaining the entire scalar cover. -/
theorem original_small_special_unitary_linear_degree
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    {a : ℕ} (ha : 0 < a)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hj : IsSU ((L j) ⧸ pCore 2 (L j)) 3 2) : a=2 := by
  obtain ⟨_,_,hcases⟩ := original_linear_unitary_degrees Q e h split hm i j hij ha
    (b:=1) (by decide) hi (Or.inr (by simpa only [pow_one] using hj))
  rcases hcases with he | he | he
  · omega
  · exact (original_small_special_unitary_large_degree_false Q e h split hm i j hij
      (Or.inl (by omega)) hi hj).elim
  · exact (original_small_special_unitary_large_degree_false Q e h split hm i j hij
      (Or.inr (by omega)) hi hj).elim

/-- Every original unitary alternative has odd degree b and linear degree
2b, for both orientations and both scalar conventions, including b = 1. -/
theorem original_linear_unitary_all_quadratic_degree
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hj : ClassicalGroup.IsPSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b) ∨
      IsSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b)) : Odd b ∧ a=2*b := by
  rcases hj with hp | hs
  · exact original_linear_projective_unitary_quadratic_degree Q e h split hm i j hij ha hb hi hp
  · by_cases hb1 : b=1
    · subst b
      refine ⟨by decide,?_⟩
      simpa only [mul_one] using original_small_special_unitary_linear_degree Q e h split hm i j hij
        ha hi (by simpa only [pow_one] using hs)
    · exact original_linear_unitary_quadratic_degree Q e h split hm i j hij ha (by omega) hi (Or.inr hs)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
