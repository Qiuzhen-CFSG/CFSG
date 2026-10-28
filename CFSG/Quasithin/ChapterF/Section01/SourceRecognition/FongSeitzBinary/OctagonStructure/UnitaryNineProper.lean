module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.UnitaryNineProper
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.UnitaryNineIndex

/-!
# Proper source invariant-subgroup exclusion

The original PSL2 and SU3/PSU3 markings supply the full-Cartan root
irreducibility, including the cubic argument in degree one. A proper
Cartan-invariant subgroup of the literal nine-b subgroup therefore has
index at least 2^b and order at most 2^(8b). An elementary section of order
at least 2^(8b) exhausts such a candidate, contradicting its 2^(7b) bound.

The final application uses the actual RootSection numerator and quotient
by its effective denominator. It retains the original quotient map, full
Borel, both endpoint squares, both orientations and scalar conventions.
The section-size hypothesis is the bound supplied by the independent
projective-degree producer; it is not asserted here without proof.

Source: Fong--Seitz I (6F), printed p.47, the proper invariant-subgroup
paragraph. Whole-X exclusion and lower-central persistence are subsequent
obligations of the original recognition family.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
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

/-- The original factor marks discharge every input of the proper-subgroup index gap. -/
theorem original_linear_unitary_nine_proper_index
    (hm : rotationOrder Q=8) (i j : Fin 2) (hij : i ≠ j)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hj : ClassicalGroup.IsPSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b) ∨
      IsSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b)) :
    ∀ W : Subgroup (X ⧸ Q.D), W < unitaryNineSubgroup Q split i j →
      Q.tits.B ⊓ Q.tits.N ≤ normalizer (W : Set (X ⧸ Q.D)) →
      2^b ≤ W.relIndex (unitaryNineSubgroup Q split i j) := by
  have hfixed := (original_linear_unitary_cubic_fixed_roots Q e h split hm i j hij ha hb hi hj).2
  obtain ⟨_,hab⟩ := original_linear_unitary_all_quadratic_degree Q e h split hm i j hij ha hb hi hj
  obtain ⟨E,hEfield,hEfin,hEcard,⟨ν⟩⟩ := hi
  let : Field E := hEfield
  let : Finite E := hEfin
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hEcard)
  have hE2 : 2 < Nat.card E := by
    rw [hEcard,hab]
    exact (by decide : 2 < 2^2).trans_le
      (Nat.pow_le_pow_right (by decide) (show 2 ≤ 2*b by omega))
  have hregular := marked_octagon_regularity_of_linear_quotient Q e h split hE2 hm i ν
  let := h.finite_local i
  let := h.finite_local j
  obtain ⟨Ti,hTi⟩ := h.sylow i
  obtain ⟨Tj,hTj⟩ := h.sylow j
  have hri : Nat.card (simpleRoot Q split i)=2^(2*b) := by
    rw [simpleRoot_card_linear Q e h split i Ti hTi ν,hEcard,hab]
  have hquot : Nat.card (simpleRoot Q split i)=Nat.card (quotientSylow Ti) := by
    rw [simpleRoot_card_linear Q e h split i Ti hTi ν]
    exact ((Nat.card_congr (linearSylowEquiv i Ti ν).toEquiv).trans
      ((Nat.card_congr (BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive
        (linearModelSylow i Ti ν)).symm.toEquiv).trans
          (Nat.card_congr Multiplicative.toAdd))).symm
  have hcenter : center ((L i) ⧸ pCore 2 (L i))=⊥ := by
    apply eq_bot_iff.mpr
    intro z hz
    have hh := MulEquivClass.apply_mem_center ν hz
    change ν z ∈ center PSL(2,E) at hh
    rw [BenderSuzuki.ZD.Linear.psl2_center_eq_bot,mem_bot] at hh
    exact ν.injective (hh.trans ν.map_one.symm)
  let νi := (regularFactorLocalEquiv Q e h split i Ti hTi (hregular i).1 hquot hcenter).trans ν
  have applyModel {F : Type} [Field F] [Finite F] (J : HermitianForm 3 F)
      (hcard : Nat.card F=(2^b)^2) (hconj : ∀ x,J.conj x=x^(2^b))
      (hmodel : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
        Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
      ∀ W : Subgroup (X ⧸ Q.D), W < unitaryNineSubgroup Q split i j →
        Q.tits.B ⊓ Q.tits.N ≤ normalizer (W : Set (X ⧸ Q.D)) →
        2^b ≤ W.relIndex (unitaryNineSubgroup Q split i j) := by
    obtain ⟨μ,σ,hσ,_⟩ := regular_unitary_cover_of_factor Q e h split J hb hcard hconj
      j (hregular j).1 hmodel.symm
    have hrj : Nat.card (simpleRoot Q split j)=(2^b)^3 := by
      rcases hmodel with ⟨⟨μ⟩⟩ | ⟨⟨μ⟩⟩
      · exact projectiveUnitary_simpleRoot_card Q e h split j Tj hTj J hb hcard hconj μ
      · exact specialUnitary_simpleRoot_card Q e h split j Tj hTj J hb hcard hconj μ
    exact unitaryNineSubgroup_proper_index Q split J hb hcard hconj i j
      (hregular i).1 (hregular j).1 νi μ hri hrj (fun w => (hfixed w).2.1.le)
  rcases hj with ⟨F,hF,hfin,J,hcard,hconj,μ⟩ | ⟨F,hF,hfin,J,hcard,hconj,μ⟩
  · exact applyModel J hcard hconj (Or.inl μ)
  · exact applyModel J hcard hconj (Or.inr μ)

/-- The proper candidate is elementary by order saturation, and is then excluded
by the literal middle-root bound. The elementary section is an actual quotient
of a subgroup, with its surjection retained. -/
theorem original_linear_unitary_nine_large_section_eq
    (hm : rotationOrder Q=8) (i j : Fin 2) (hij : i ≠ j)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hj : ClassicalGroup.IsPSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b) ∨
      IsSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b))
    (W : Subgroup (X ⧸ Q.D)) (hW : W ≤ unitaryNineSubgroup Q split i j)
    (hH : Q.tits.B ⊓ Q.tits.N ≤ normalizer (W : Set (X ⧸ Q.D)))
    {Z : Type*} [Group Z] [IsElementaryAbelian 2 Z]
    (A : Subgroup W) (f : A →* Z) (hf : Function.Surjective f)
    (hlarge : 2^(8*b) ≤ Nat.card Z) : W=unitaryNineSubgroup Q split i j := by
  by_contra hne
  have hindex := original_linear_unitary_nine_proper_index Q e h split hm i j hij ha hb hi hj
    W (lt_of_le_of_ne hW hne) hH
  have hcard := (original_linear_unitary_nine_subgroup Q e h split hm i j hij ha hb hi hj).1
  have hbound := unitaryNineSubgroup_proper_card_le Q split i j hcard W hW hindex
  have hel := IsElementaryAbelian.of_large_section A f hf (hbound.trans hlarge)
  have hsmall := (original_linear_unitary_nine_subgroup_control Q e h split hm i j hij ha hb hi hj).2.2.1
    W hW hel
  have hlo := hlarge.trans ((Nat.card_le_card_of_surjective f hf).trans
    (Nat.card_le_card_of_injective A.subtype A.subtype_injective))
  have hlt : 2^(7*b) < 2^(8*b) := Nat.pow_lt_pow_right (by decide) (by omega)
  omega

/-- Application to the literal invariant section and its effective quotient
X/Phi(X)Y(H intersect X), with no replacement of its quotient map. -/
theorem original_linear_unitary_nine_rootSection_numerator
    (hm : rotationOrder Q=8) (i j : Fin 2) (hij : i ≠ j)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hj : ClassicalGroup.IsPSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b) ∨
      IsSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b))
    (d : RootSection Q split j)
    (hd : d.numerator ≤ unitaryNineSubgroup Q split i j)
    (hH : Q.tits.B ⊓ Q.tits.N ≤ normalizer (d.numerator : Set (X ⧸ Q.D)))
    (hlarge : 2^(8*b) ≤ Nat.card d.EffectiveCarrier) :
    d.numerator=unitaryNineSubgroup Q split i j := by
  let A : Subgroup d.numerator := ⊤
  let f : A →* d.EffectiveCarrier := (QuotientGroup.mk' d.effectiveDenominator).comp A.subtype
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective d.effectiveDenominator y
    exact ⟨⟨x,trivial⟩,rfl⟩
  exact original_linear_unitary_nine_large_section_eq Q e h split hm i j hij ha hb hi hj
    d.numerator hd hH A f hf hlarge

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
