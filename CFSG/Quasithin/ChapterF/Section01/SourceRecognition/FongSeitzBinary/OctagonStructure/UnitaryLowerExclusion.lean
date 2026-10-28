module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.UnitaryScalarPersistence
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.UnitaryCommutatorEscape
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.UnitaryNineEscape
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.UnitaryCommutatorEscape

/-!
# Excluding the original linear/unitary octagon pair

For every scalar-fixed lower-central term, the projective eight-b bound
excludes containment in the nine-b subgroup. Root commutators then give a
six-b next term. Since the entire derived radical has order at most
2^(13b), the quotient by that next term has order at most 2^(7b). The
projective action must therefore persist in its scalar-fixed subgroup.
Induction contradicts nilpotence of the actual finite two-radical.

The proof includes degree one, both original endpoint orientations, both
SU3/PSU3 conventions, the literal quotient, the full Cartan and Borel, and
both marked inclusion squares. The import-all edges reuse this family's
internal original-factor cover and center argument without changing those
public interfaces.

Source: Fong--Seitz I (6F), printed p.47, the subgroup exclusion and
lower-central persistence paragraphs. Other unitary pair types and the
complete rank-two source assembly remain separate branches.
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

/-- The source nine-b subgroup contains no scalar-fixed invariant section
of projective size. The bound is discharged by the following recurrence. -/
theorem original_linear_unitary_scalar_section_not_le_nine
    (hm : rotationOrder Q=8) (i j : Fin 2) (hij : i ≠ j)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hj : ClassicalGroup.IsPSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b) ∨
      IsSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b))
    (d : RootSection Q split j)
    (hscalar : d.numerator ≤ centralizer (rankOneScalar Q split j : Set (X ⧸ Q.D)))
    (hH : Q.tits.B ⊓ Q.tits.N ≤ normalizer (d.numerator : Set (X ⧸ Q.D)))
    (hlarge : 2^(8*b) ≤ Nat.card d.EffectiveCarrier) :
    ¬ d.numerator ≤
      unitaryNineSubgroup Q split i j := by
  have hKj := original_unitary_remainder_regular Q e h split hm i j hij ha hb hi hj
  have hodd := (original_linear_unitary_all_quadratic_degree Q e h split hm i j hij ha hb hi hj).1
  have hsource := original_linear_unitary_nine_subgroup Q e h split hm i j hij ha hb hi hj
  have hfixed := (original_linear_unitary_cubic_fixed_roots Q e h split hm i j hij ha hb hi hj).2
  have hab := original_linear_unitary_cubic_radical_abelian Q e h split hm i j hij ha hb hi hj
  have hcenter := (original_linear_unitary_nine_subgroup_control Q e h split hm i j hij ha hb hi hj).1
  have applyModel {F : Type} [Field F] [Finite F] (J : HermitianForm 3 F)
      (hcard : Nat.card F=(2^b)^2) (hconj : ∀ x,J.conj x=x^(2^b))
      (hmodel : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
        Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
      ¬ d.numerator ≤
        unitaryNineSubgroup Q split i j := by
    intro hdK
    let := h.finite_local j
    obtain ⟨μ,σ,hσ,_⟩ := regular_unitary_cover_of_factor Q e h split J hb hcard hconj
      j hKj hmodel.symm
    let K := unitaryNineSubgroup Q split i j
    let M := rootFrattiniAt Q split j (Q.simple i*Q.simple j*Q.simple i)
    let Y := simpleRemainder Q split j ⊓ centralizer (cartanThreeCore Q : Set (X ⧸ Q.D))
    have hd : d.numerator=K := original_linear_unitary_nine_rootSection_numerator
      Q e h split hm i j hij ha hb hi hj d hdK hH hlarge
    let ek : K ≃* d.numerator := MulEquiv.subgroupCongr hd.symm
    let f : K →* d.EffectiveCarrier := (QuotientGroup.mk' d.effectiveDenominator).comp ek.toMonoidHom
    have hf : Function.Surjective f := (QuotientGroup.mk'_surjective _).comp ek.surjective
    have hder : ⁅K,K⁆ ≤ M := (unitaryNineSubgroup_large_quotient_kernel Q split i j
      hsource.1 hsource.2.1 hsource.2.2.1 f hf hlarge).2
    have hYC : Y ≤ centralizer (K : Set (X ⧸ Q.D)) :=
      unitaryNineSubgroup_fixed_central Q split hm i j hij hsource.2.2.2 hab
        (hder.trans ((hfixed _).2.1.ge.trans inf_le_right))
    have hKR : K ≤ simpleRemainder Q split j := hd ▸ d.le_radical
    have hRN : rankOne Q split j ≤ normalizer (K : Set (X ⧸ Q.D)) := hd ▸ d.normalized
    let C := (center K).map K.subtype
    let c := subgroupSection Q split j C ((map_subtype_le _).trans hKR)
      (hRN.trans (normalizer_le_normalizer_characteristic_image _ (center K)))
    have hCS : c.numerator ≤ centralizer (rankOneScalar Q split j : Set (X ⧸ Q.D)) :=
      (map_subtype_le _).trans (hd ▸ hscalar)
    have hYC' : Y ≤ c.numerator := by
      intro y hy
      exact ⟨⟨y,hsource.2.2.2 hy⟩,mem_center_iff.mpr
        (fun k => Subtype.ext (hYC hy k k.property)),rfl⟩
    let A := rootFrattiniAt Q split j (Q.simple i)
    have hAcard : Nat.card A=2^b := unitary_rootFrattini_card Q split J hb hcard hconj j hKj μ _
    have hAne : A ≠ ⊥ := by
      intro he
      have hn : 1 < Nat.card A := hAcard ▸ Nat.one_lt_pow (by omega) (by decide)
      rw [he,Nat.card_unique] at hn
      omega
    obtain ⟨x,hx⟩ := ne_bot_iff_exists_ne_one.mp hAne
    have hxroot : (x : X ⧸ Q.D) ∈ rootAt Q split j (Q.simple i) := map_subtype_le _ x.property
    have hAK : A ≤ K := le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_sup_left))
    have hxY : (x : X ⧸ Q.D) ∈ Y :=
      ⟨hKR (hAK x.property),((hfixed _).2.1.ge x.property).2⟩
    have hbig := original_scalar_crossed_bound Q e h split hm i j hij hb hodd J hcard hconj
      hmodel hKj c rfl hCS ⟨x,hxroot⟩ (fun he => hx (Subtype.ext (congrArg (fun z : rootAt Q split j (Q.simple i) => (z : X ⧸ Q.D)) he))) (hYC' hxY)
    have hsmall : Nat.card c.EffectiveCarrier ≤ 2^(7*b) :=
      (Nat.card_le_card_of_surjective (QuotientGroup.mk' c.effectiveDenominator)
        (QuotientGroup.mk'_surjective _)).trans (by
          change Nat.card ((center K).map K.subtype) ≤ _
          rw [card_map_of_injective K.subtype_injective]
          exact hcenter)
    exact (not_le_of_gt (Nat.pow_lt_pow_right (by decide : 1 < 2)
      (by omega : 7*b < 8*b))) (hbig.trans hsmall)
  rcases hj with ⟨F,hF,hfin,J,hcard,hconj,hmodel⟩ | ⟨F,hF,hfin,J,hcard,hconj,hmodel⟩
  · exact applyModel J hcard hconj (Or.inl hmodel)
  · exact applyModel J hcard hconj (Or.inr hmodel)

/-- The projective section persists through every actual lower-central term.
The eight-b bound and escape from the nine-b subgroup are proved internally. -/
theorem original_linear_unitary_scalar_lower_persistence
    (hm : rotationOrder Q=8) (i j : Fin 2) (hij : i ≠ j)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hj : ClassicalGroup.IsPSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b) ∨
      IsSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b))
    (hKj : simpleRemainder Q split j ≤ localKernel Q j) :
    ∀ n : ℕ, let d := unitaryScalarLowerSection Q split j hKj n
      ¬ IsPGroup 2 d.action.range ∧
      2^(8*b) ≤ Nat.card d.EffectiveCarrier ∧
      ¬ d.numerator ≤ unitaryNineSubgroup Q split i j := by
  have hodd := (original_linear_unitary_all_quadratic_degree Q e h split hm i j hij ha hb hi hj).1
  have hfix := (original_linear_unitary_cubic_fixed_roots Q e h split hm i j hij ha hb hi hj).2
  have hd := original_linear_unitary_derived_bounds Q e h split hm i j hij ha hb hi hj
  let V := simpleRemainder Q split j
  let lower := unitaryScalarLowerSection Q split j hKj
  have applyModel {F : Type} [Field F] [Finite F] (J : HermitianForm 3 F)
      (hcard : Nat.card F=(2^b)^2) (hconj : ∀ x,J.conj x=x^(2^b))
      (hmodel : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
        Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
      ∀ n : ℕ, ¬ IsPGroup 2 (lower n).action.range ∧
        2^(8*b) ≤ Nat.card (lower n).EffectiveCarrier ∧
        ¬ (lower n).numerator ≤ unitaryNineSubgroup Q split i j := by
    let := h.finite_local j
    obtain ⟨Tj,hTj⟩ := h.sylow j
    obtain ⟨μ,σ,hσ,hsquare⟩ := regular_unitary_cover_of_factor Q e h split J hb hcard hconj
      j hKj hmodel.symm
    have hroot : Nat.card (simpleRoot Q split j)=(2^b)^3 := by
      rcases hmodel with ⟨⟨ν⟩⟩ | ⟨⟨ν⟩⟩
      · exact projectiveUnitary_simpleRoot_card Q e h split j Tj hTj J hb hcard hconj ν
      · exact specialUnitary_simpleRoot_card Q e h split j Tj hTj J hb hcard hconj ν
    have hsmall : b=1 → Nonempty (rankOne Q split j ≃* J.specialSubgroup) ∨
        Nonempty (rankOne Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J) := by
      intro _
      rcases hmodel with ⟨⟨ν⟩⟩ | ⟨⟨ν⟩⟩
      · have hc := projectiveUnitary_simpleRoot_card_eq_quotientSylow Q e h split j Tj hTj
          J hb hcard hconj ν
        exact Or.inr ⟨(regularFactorRootEquiv Q e h split j Tj hTj hKj hc).trans ν⟩
      · have hc := specialUnitary_simpleRoot_card_eq_quotientSylow Q e h split j Tj hTj
          J hb hcard hconj ν
        exact Or.inl ⟨(regularFactorRootEquiv Q e h split j Tj hTj hKj hc).trans ν⟩
    have large (n : ℕ) (hn : ¬ IsPGroup 2 (lower n).action.range) :
        2^(8*b) ≤ Nat.card (lower n).EffectiveCarrier :=
      unitary_scalar_section_card_bound Q split J hb hodd hcard hconj j hKj μ σ hσ
        hroot hsmall (lower n) inf_le_right hn
    have escape (n : ℕ) (hn : ¬ IsPGroup 2 (lower n).action.range) :
        ¬ (lower n).numerator ≤ unitaryNineSubgroup Q split i j :=
      original_linear_unitary_scalar_section_not_le_nine Q e h split hm i j hij ha hb hi hj
        (lower n) inf_le_right (unitary_scalar_lower_cartan_normalized Q split j hKj n) (large n hn)
    have hn : ∀ n : ℕ, ¬ IsPGroup 2 (lower n).action.range := by
      intro n
      induction n with
      | zero =>
        have hZ := unitary_scalar_le_threeCore Q split J j hKj μ σ hσ hsquare
        have hne := unitary_root_commutator_ne_bot Q split J hb hcard hconj j hKj μ
        obtain ⟨x,hx,hxd⟩ := unitary_scalar_derived_crossed_witness Q split hm i j hij hKj
          hZ (fun w => (hfix w).2.1) hne
        exact unitary_scalar_crossed_action_not_two Q split J hb hcard hconj hm i j hij hKj
          σ hσ hroot hsmall (lower 0) rfl x hx hxd
      | succ n ih =>
        have hWD : V.lowerCentralSeries (n+1) ≤ ⁅V,V⁆ :=
          V.lowerCentralSeries_antitone (show 1 ≤ n+1 by omega)
        have hWM := hWD.trans hd.1
        have hWR := (rankOne_le_parabolic Q split j).trans
          (unitary_radical_lower_normalized Q split j hKj (n+1))
        have hesc : ¬ V.lowerCentralSeries (n+1) ≤ unitaryNineSubgroup Q split i j :=
          fun hh => escape n ih (inf_le_left.trans hh)
        have hc : 2^(6*b) ≤ Nat.card (V.lowerCentralSeries (n+2)) :=
          (original_linear_unitary_next_commutator Q e h split hm i j hij ha hb hi hj
            (V.lowerCentralSeries (n+1)) hWM hWR hesc).2.trans
              (Nat.card_le_card_of_surjective (QuotientGroup.mk' (frattini (V.lowerCentralSeries (n+2))))
                (QuotientGroup.mk'_surjective _))
        have hCD : V.lowerCentralSeries (n+2) ≤ ⁅V,V⁆ :=
          V.lowerCentralSeries_antitone (show 1 ≤ n+2 by omega)
        have hprod := relIndex_mul_relIndex (⊥ : Subgroup (X ⧸ Q.D))
          (V.lowerCentralSeries (n+2)) ⁅V,V⁆ bot_le hCD
        rw [relIndex_bot_left,relIndex_bot_left] at hprod
        have hquot : (V.lowerCentralSeries (n+2)).relIndex ⁅V,V⁆ ≤ 2^(7*b) := by
          apply Nat.le_of_mul_le_mul_left (c:=2^(6*b)) ?_ (by positivity)
          calc
            2^(6*b)*(V.lowerCentralSeries (n+2)).relIndex ⁅V,V⁆ ≤
                Nat.card (V.lowerCentralSeries (n+2))*(V.lowerCentralSeries (n+2)).relIndex ⁅V,V⁆ :=
              Nat.mul_le_mul_right _ hc
            _ = Nat.card (⁅V,V⁆ : Subgroup (X ⧸ Q.D)) := hprod
            _ ≤ 2^(13*b) := hd.2.1
            _ = 2^(6*b)*2^(7*b) := by rw [←pow_add]; congr 1; omega
        exact unitary_scalar_section_persistence Q split J hb hodd hcard hconj j hKj
          μ σ hσ hroot hsmall (lower n) (lower (n+1)) rfl
          (unitary_scalar_lower_le Q split j hKj n) inf_le_right ih
          (((unitary_scalar_lower_quotient_le Q split j hKj n).trans hquot).trans_lt
            (Nat.pow_lt_pow_right (by decide) (by omega : 7*b < 8*b)))
    exact fun n => ⟨hn n,large n (hn n),escape n (hn n)⟩
  rcases hj with ⟨F,hF,hfin,J,hcard,hconj,hmodel⟩ | ⟨F,hF,hfin,J,hcard,hconj,hmodel⟩
  · exact applyModel J hcard hconj (Or.inl hmodel)
  · exact applyModel J hcard hconj (Or.inr hmodel)

/-- Fong--Seitz (6F)'s linear/unitary pair is impossible. The actual scalar
section persists through the nilpotent radical's entire lower-central series. -/
theorem original_linear_unitary_pair_false
    (hm : rotationOrder Q=8) (i j : Fin 2) (hij : i ≠ j)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hj : ClassicalGroup.IsPSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b) ∨
      IsSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b)) : False := by
  have hKj := original_unitary_remainder_regular Q e h split hm i j hij ha hb hi hj
  let V := simpleRemainder Q split j
  let : Group.IsNilpotent V := (split.isTwo.to_le (show V ≤ split.U from inf_le_left)).isNilpotent
  apply lowerCentralSeries_card_contradiction V (c:=2^(8*b))
    (by exact (by decide : 2 ≤ 2^1).trans (Nat.pow_le_pow_right (by decide) (by omega)))
  intro n
  have hl := (original_linear_unitary_scalar_lower_persistence Q e h split hm i j hij
    ha hb hi hj hKj n).2.1
  let d := unitaryScalarLowerSection Q split j hKj n
  exact hl.trans ((Nat.card_le_card_of_surjective (QuotientGroup.mk' d.effectiveDenominator)
    (QuotientGroup.mk'_surjective _)).trans (card_le_of_le
      (inf_le_left.trans (V.lowerCentralSeries_antitone (show n ≤ n+1 by omega)))))

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
