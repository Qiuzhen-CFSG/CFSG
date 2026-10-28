module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.SmallProjectiveUnitary
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.LinearUnitaryLargeDegree
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.BinaryAffineOctagonExclusion
public import Theory.SpecificGroups.SU3.FixedFieldTwo

/-!
# The original small projective-unitary octagon degree

The original nonbinary linear quotient supplies regularity at both
endpoints. The original PSU3(2) marking therefore identifies the actual
root-generated actor with the solvable order-72 group, and its root with
an order-eight Sylow. The separating-prime fixed-radical contradiction
excludes linear degrees four and six, leaving only degree two.

No original-factor perfectness or small-case simplicity is assumed.
Both orientations, the full original amalgam isomorphism and its two
endpoint squares are retained. Source: Fong--Seitz I (6F), printed p.46.
The quadratic case and the distinct SU3(2) scalar cover remain separate.
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

/-- The original PSU3(2) endpoint cannot oppose linear degree four or six. -/
theorem original_small_projective_unitary_large_degree_false
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    {a : ℕ} (ha : a=4 ∨ a=6)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hj : ClassicalGroup.IsPSU ((L j) ⧸ pCore 2 (L j)) 3 2) : False := by
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
  have hjcard := projectiveUnitary_simpleRoot_card_eq_quotientSylow Q e h split j Tj hTj J
    (n:=1) (by decide) (by simpa using hcard) (by simpa using hconj) ν
  let μj := (regularFactorRootEquiv Q e h split j Tj hTj (hregular j).1 hjcard).trans ν
  have hroot : Nat.card (simpleRoot Q split j) = 8 := by
    simpa only [Nat.reducePow] using projectiveUnitary_simpleRoot_card Q e h split j Tj hTj J
      (n:=1) (by decide) (by simpa using hcard) (by simpa using hconj) ν
  let := HermitianForm.FixedFieldTwo.projective_isSolvable J hcard hconj
  let : Group.IsSolvable (rankOne Q split j) :=
    Group.isSolvable_of_surjective (f:=μj.symm.toMonoidHom) μj.symm.surjective
  have hR : Nat.card (rankOne Q split j) = 72 :=
    (Nat.card_congr μj.toEquiv).trans (HermitianForm.FixedFieldTwo.card_projective J hcard hconj)
  apply Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure.nine_actor_large_linear_false
    Q split j hR hroot hm i hij (hregular i).1 (hregular j).1 μi
  rcases ha with rfl | rfl
  · exact Or.inl hEcard
  · exact Or.inr hEcard

/-- Only linear degree two remains opposite the original small projective
unitary quotient. This does not identify or exclude that quadratic case. -/
theorem original_small_projective_unitary_linear_degree
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    {a : ℕ} (ha : 0 < a)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hj : ClassicalGroup.IsPSU ((L j) ⧸ pCore 2 (L j)) 3 2) : a=2 := by
  obtain ⟨_,_,hcases⟩ := original_linear_unitary_degrees Q e h split hm i j hij ha
    (b:=1) (by decide) hi (Or.inl (by simpa only [pow_one] using hj))
  rcases hcases with he | he | he
  · omega
  · exact (original_small_projective_unitary_large_degree_false Q e h split hm i j hij
      (Or.inl (by omega)) hi hj).elim
  · exact (original_small_projective_unitary_large_degree_false Q e h split hm i j hij
      (Or.inr (by omega)) hi hj).elim

/-- The larger-degree exclusions and the small-case argument give the
quadratic ratio for every original projective-unitary degree. -/
theorem original_linear_projective_unitary_quadratic_degree
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hj : ClassicalGroup.IsPSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b)) : Odd b ∧ a=2*b := by
  by_cases hb1 : b=1
  · subst b
    refine ⟨by decide,?_⟩
    simpa only [mul_one] using original_small_projective_unitary_linear_degree Q e h split hm i j hij
      ha hi (by simpa only [pow_one] using hj)
  · exact original_linear_unitary_quadratic_degree Q e h split hm i j hij ha (by omega) hi (Or.inl hj)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
