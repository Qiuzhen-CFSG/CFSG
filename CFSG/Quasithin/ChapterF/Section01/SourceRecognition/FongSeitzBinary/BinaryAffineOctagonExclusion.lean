module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.AffineExclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.BinaryUnitaryApplications
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.RegularUnitaryCover
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.RegularFactorCover

/-!
# Original-factor regularity in a nonbinary linear octagon

The nonbinary original linear quotient supplies its exact regular local
PSL2 marking. The octagon fixed-kernel argument then excludes the only
remaining order-144 affine local action. Both remainder preimages equal
the original endpoint two-cores, without perfectness of either factor.

The unitary application constructs its actual SU3 cover and projective
square at every positive degree, including degree one. The final two
theorems instantiate these conclusions on the literal Chapter 12 pair,
with its original full Borel and endpoint maps. These results discharge
the regularity prerequisite of Fong--Seitz I (6F); the exclusion of regular
unitary endpoints remains separate. Sources: Fong--Seitz I (2B), (6F);
Aschbacher--Smith F.1.1 and 12.2.2; DGS Theorem D, printed p.224.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)

include e h in
/-- A nonbinary original linear quotient excludes the opposite affine octagon without original perfectness. -/
theorem binary_affine_octagon_false_of_linear_quotient
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : 2 < Nat.card F)
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    (μ : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F))
    (hx : BinaryUnitaryException Q split j) : False := by
  let := h.finite_local i
  obtain ⟨T,hT⟩ := h.sylow i
  have hV := linear_remainder_le_kernel Q e h split i T hT μ
  have hc : Nat.card (simpleRoot Q split i) = Nat.card (quotientSylow T) := by
    have hTcard : Nat.card (quotientSylow T) = Nat.card F :=
      (Nat.card_congr (linearSylowEquiv i T μ).toEquiv).trans
        ((Nat.card_congr (BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive
          (linearModelSylow i T μ)).symm.toEquiv).trans
            (Nat.card_congr Multiplicative.toAdd))
    exact (simpleRoot_card_linear Q e h split i T hT μ).trans hTcard.symm
  have hz : center ((L i) ⧸ pCore 2 (L i)) = ⊥ := by
    apply eq_bot_iff.mpr
    intro z hz
    have he := MulEquivClass.apply_mem_center μ hz
    change μ z ∈ center PSL(2,F) at he
    rw [BenderSuzuki.ZD.Linear.psl2_center_eq_bot,mem_bot] at he
    exact μ.injective (he.trans μ.map_one.symm)
  let a := (regularFactorLocalEquiv Q e h split i T hT hV hc hz).trans μ
  exact no_affine_octagon_of_linear Q split hF hm i j hij hV a
    (UnitarySource.actorReflection Q split i) hx.1 hx.2.1 hx.2.2.1

include e h in
/-- A nonbinary original linear endpoint removes the affine defect at both marked octagon endpoints. -/
theorem marked_octagon_regularity_of_linear_quotient
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : 2 < Nat.card F)
    (hm : rotationOrder Q = 8) (i : Fin 2)
    (μ : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F)) :
    ∀ j : Fin 2, simpleRemainder Q split j ≤ localKernel Q j ∧
      (simpleRemainder Q split j).comap (endpointMap Q e j) = pCore 2 (parabolic L S j) := by
  intro j
  by_cases hij : i = j
  · subst j
    let := h.finite_local i
    obtain ⟨T,hT⟩ := h.sylow i
    have hr := linear_remainder_le_kernel Q e h split i T hT μ
    exact ⟨hr,remainder_comap_of_containment Q e split i hr⟩
  · let := h.finite_local j
    obtain ⟨T,hT⟩ := h.sylow j
    rcases remainder_le_kernel_or_binary_unitary_exception Q e h split j T hT with hr | hx
    · exact hr
    · exact (binary_affine_octagon_false_of_linear_quotient Q e h split hF hm i j hij μ hx).elim

include e h in
/-- Model form of octagon regularity, preserving the original marking and both literal core preimages. -/
theorem marked_octagon_regularity_of_linear
    (hm : rotationOrder Q = 8) (i : Fin 2) {a : ℕ} (ha : 1 < a)
    (hlinear : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a)) :
    ∀ j : Fin 2, simpleRemainder Q split j ≤ localKernel Q j ∧
      (simpleRemainder Q split j).comap (endpointMap Q e j) = pCore 2 (parabolic L S j) := by
  obtain ⟨F,hF,hfin,hcard,⟨μ⟩⟩ := hlinear
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  have hF2 : 2 < Nat.card F := by
    rw [hcard]
    exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mpr ha
  exact marked_octagon_regularity_of_linear_quotient Q e h split hF2 hm i μ

include e h in
/-- The opposite actual SU3 cover, including degree one, follows from a nonbinary original linear endpoint. -/
theorem marked_octagon_unitary_cover_of_linear
    (hm : rotationOrder Q = 8) (i j : Fin 2) {a : ℕ} (ha : 1 < a)
    (hlinear : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    {n : ℕ} (hn : 0 < n) (hc : Nat.card E = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (hfactor : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J)) :
    (∀ k : Fin 2, simpleRemainder Q split k ≤ localKernel Q k ∧
      (simpleRemainder Q split k).comap (endpointMap Q e k) = pCore 2 (parabolic L S k)) ∧
    ∃ ν : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J,
      ∃ π : J.specialSubgroup →* rankOne Q split j,
        Function.Surjective π ∧
        ∀ a, ν (RootLocalCover.projection Q split j (π a)) = J.specialToProjective a := by
  have hr := marked_octagon_regularity_of_linear Q e h split hm i ha hlinear
  exact ⟨hr,regular_unitary_cover_of_factor Q e h split J hn hc hconj j (hr j).1 hfactor⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
include D

/-- Both original Chapter 12 kernel containments and core preimages hold in the octagonal branch. -/
theorem rankOne_octagon_regularity
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) (hm : rotationOrder Q = 8) :
    ∀ i : Fin 2, simpleRemainder Q split i ≤ localKernel Q i ∧
      (simpleRemainder Q split i).comap (MarkedLocal.endpointMap Q e i) =
        pCore 2 (parabolic ![L,R] (Global.sourceS L H) i) := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  exact MarkedLocal.marked_octagon_regularity_of_linear Q e hf split hm 0 hn hpsl

/-- The actual Chapter 12 opposite SU3/PSU3 factor supplies its SU3 cover and literal projective square at every positive degree. -/
theorem rankOne_octagon_unitary_cover
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) (hm : rotationOrder Q = 8)
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    {b : ℕ} (hb : 0 < b) (hc : Nat.card E = (2^b)^2)
    (hconj : ∀ x, J.conj x = x^(2^b))
    (hfactor : Nonempty ((R ⧸ pCore 2 R) ≃* J.specialSubgroup) ∨
      Nonempty ((R ⧸ pCore 2 R) ≃* ProjectiveSpecialUnitaryMatrixGroup J)) :
    ∃ ν : localGroup Q split 1 ≃* ProjectiveSpecialUnitaryMatrixGroup J,
      ∃ π : J.specialSubgroup →* rankOne Q split 1,
        Function.Surjective π ∧
        ∀ a, ν (RootLocalCover.projection Q split 1 (π a)) = J.specialToProjective a := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  exact (MarkedLocal.marked_octagon_unitary_cover_of_linear
    Q e hf split hm 0 1 hn hpsl J hb hc hconj hfactor).2

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
