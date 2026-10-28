module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.UnitaryCommutatorEscape
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.UnitaryNineEscape

/-!
# The next lower-central term of the original unitary octagon

For the original linear/unitary factor marks, escape from the nine-b
subgroup forces the next commutator with the radical to carry a nontrivial
rank-one action and a Frattini quotient of order at least 2^(6b). The
shifted-radical kernels retain the literal end coordinates, and the odd
panel index handles both degree-one scalar conventions.

Applying this to the already proved escape of the derived radical gives
the actual third lower-central term. Both endpoint orientations, the
original quotient, the full Borel and the marked inclusion squares are
retained. The recurrence of the stronger projective eight-b section is
still needed before concluding the lower-central-series contradiction.

Source: Fong--Seitz I (6F), printed p.47, the last full paragraph.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped IsMulCommutative MatrixGroups
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

private theorem original_unitary_remainder_regular
    (hm : rotationOrder Q=8) (i j : Fin 2) (hij : i ≠ j)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hj : ClassicalGroup.IsPSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b) ∨
      IsSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b)) :
    simpleRemainder Q split j ≤ localKernel Q j := by
  obtain ⟨E,hE,hfin,hcard,⟨ν⟩⟩ := hi
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  have hab := (original_linear_unitary_all_quadratic_degree Q e h split hm i j hij ha hb
    ⟨E,hE,hfin,hcard,⟨ν⟩⟩ hj).2
  have hE2 : 2 < Nat.card E := by
    rw [hcard,hab]
    exact (by decide : 2 < 2^2).trans_le
      (Nat.pow_le_pow_right (by decide) (show 2 ≤ 2*b by omega))
  exact (marked_octagon_regularity_of_linear_quotient Q e h split hE2 hm i ν j).1

/-- A literal escaping invariant subgroup forces the source's nontrivial
next commutator and six-b Frattini bound, including degree one. -/
theorem original_linear_unitary_next_commutator
    (hm : rotationOrder Q=8) (i j : Fin 2) (hij : i ≠ j)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hj : ClassicalGroup.IsPSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b) ∨
      IsSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b))
    (W : Subgroup (X ⧸ Q.D)) (hWM : W ≤ middleFive Q split j i)
    (hWR : rankOne Q split j ≤ normalizer (W : Set (X ⧸ Q.D)))
    (hescape : ¬ W ≤ unitaryNineSubgroup Q split i j) :
    let C := ⁅W,simpleRemainder Q split j⁆
    ⁅rankOne Q split j,C⁆ ≠ ⊥ ∧ 2^(6*b) ≤ Nat.card (C ⧸ frattini C) := by
  have hKj := original_unitary_remainder_regular Q e h split hm i j hij ha hb hi hj
  let := h.finite_local j
  obtain ⟨Tj,hTj⟩ := h.sylow j
  have applyModel {F : Type} [Field F] [Finite F] (J : HermitianForm 3 F)
      (hcard : Nat.card F=(2^b)^2) (hconj : ∀ x,J.conj x=x^(2^b))
      (hmodel : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
        Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
      let C := ⁅W,simpleRemainder Q split j⁆
      ⁅rankOne Q split j,C⁆ ≠ ⊥ ∧ 2^(6*b) ≤ Nat.card (C ⧸ frattini C) := by
    obtain ⟨μ,σ,hσ,_⟩ := regular_unitary_cover_of_factor Q e h split J hb hcard hconj
      j hKj hmodel.symm
    have hroot : Nat.card (simpleRoot Q split j)=(2^b)^3 := by
      rcases hmodel with ⟨⟨ν⟩⟩ | ⟨⟨ν⟩⟩
      · exact projectiveUnitary_simpleRoot_card Q e h split j Tj hTj J hb hcard hconj ν
      · exact specialUnitary_simpleRoot_card Q e h split j Tj hTj J hb hcard hconj ν
    refine ⟨?_,unitary_commutator_frattini_bound_all Q split J hb hcard hconj hm i j hij
      hKj μ σ hσ hroot W hWM hWR hescape⟩
    intro he
    have hcent := commutator_eq_bot_iff_le_centralizer.mp he
    apply unitary_commutator_action_of_escape Q split J hb hcard hconj hm i j hij
      hKj μ W hWM hWR hescape
    let d := radicalCommutatorSection Q split j hKj W
      (hWM.trans (middleFive_le_remainder Q split hm j i hij.symm)) hWR
    change d.action=1
    ext r z
    induction z using QuotientGroup.induction_on with
    | H z =>
      change d.action r (QuotientGroup.mk z)=QuotientGroup.mk z
      rw [d.action_mk]
      congr 1
      apply Subtype.ext
      rw [d.numeratorAction_apply]
      have hz := mem_centralizer_iff.mp (hcent r.property) z z.property
      rw [←hz,mul_inv_cancel_right]
  rcases hj with ⟨F,hF,hfin,J,hcard,hconj,hmodel⟩ | ⟨F,hF,hfin,J,hcard,hconj,hmodel⟩
  · exact applyModel J hcard hconj (Or.inl hmodel)
  · exact applyModel J hcard hconj (Or.inr hmodel)

/-- The third lower-central term of the original unitary radical is moved
by the unitary actor and has the source's six-b Frattini bound. -/
theorem original_linear_unitary_triple_commutator
    (hm : rotationOrder Q=8) (i j : Fin 2) (hij : i ≠ j)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hj : ClassicalGroup.IsPSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b) ∨
      IsSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b)) :
    let V := simpleRemainder Q split j
    let C := ⁅⁅V,V⁆,V⁆
    ⁅rankOne Q split j,C⁆ ≠ ⊥ ∧ 2^(6*b) ≤ Nat.card (C ⧸ frattini C) := by
  have hKj := original_unitary_remainder_regular Q e h split hm i j hij ha hb hi hj
  exact original_linear_unitary_next_commutator Q e h split hm i j hij ha hb hi hj _
    (original_linear_unitary_derived_bounds Q e h split hm i j hij ha hb hi hj).1
    ((rankOne_le_parabolic Q split j).trans (radical_commutator_normalized Q split j hKj))
    (original_linear_unitary_derived_not_le_nine Q e h split hm i j hij ha hb hi hj)

/-- The actual derived quotient by the third lower-central term is too
small to carry a projective eight-b section. This is the source size budget
for the subsequent Jordan--Hölder persistence argument. -/
theorem original_linear_unitary_derived_mod_triple_bound
    (hm : rotationOrder Q=8) (i j : Fin 2) (hij : i ≠ j)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hj : ClassicalGroup.IsPSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b) ∨
      IsSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b)) :
    let V := simpleRemainder Q split j
    let D := ⁅V,V⁆
    let C := ⁅D,V⁆
    Nat.card (D ⧸ C.subgroupOf D) ≤ 2^(7*b) := by
  let V := simpleRemainder Q split j
  let D := ⁅V,V⁆
  let C := ⁅D,V⁆
  have hCD : C ≤ D := radical_triple_le_derived Q split j
  have hc : 2^(6*b) ≤ Nat.card C :=
    (original_linear_unitary_triple_commutator Q e h split hm i j hij ha hb hi hj).2.trans
      (Nat.card_le_card_of_surjective (QuotientGroup.mk' (frattini C))
        (QuotientGroup.mk'_surjective _))
  have hd : Nat.card D ≤ 2^(13*b) :=
    (original_linear_unitary_derived_bounds Q e h split hm i j hij ha hb hi hj).2.1
  have hprod := relIndex_mul_relIndex (⊥ : Subgroup (X ⧸ Q.D)) C D bot_le hCD
  rw [relIndex_bot_left,relIndex_bot_left] at hprod
  change C.relIndex D ≤ 2^(7*b)
  apply Nat.le_of_mul_le_mul_left (c:=2^(6*b)) ?_ (by positivity)
  calc
    2^(6*b)*C.relIndex D ≤ Nat.card C*C.relIndex D := Nat.mul_le_mul_right _ hc
    _ = Nat.card D := hprod
    _ ≤ 2^(13*b) := hd
    _ = 2^(6*b)*2^(7*b) := by rw [←pow_add]; congr 1; omega

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
