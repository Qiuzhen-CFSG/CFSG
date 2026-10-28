module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.UnitaryScalarSection
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.UnitaryProjectiveDegree
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.UnitaryNineQuotient
import all Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.UnitaryCubicFixed

/-!
# The actual unitary derived radical escapes the nine-b subgroup

In Fong--Seitz I (6F), printed p.47, an invariant candidate inside the
nine-b root subgroup must equal that subgroup by the projective eight-b
bound and the proper-subgroup index gap. Its large elementary quotient
then puts its derived group in the middle Frattini root. The cubic fixed
radical is consequently central. A nonidentity crossed-root element in
this center forces another projective eight-b section, contradicting the
seven-b bound for the center.

The argument applies directly to the scalar-fixed derived section and
hence to the whole derived radical. It does not assume irreducibility of
the entire Frattini action. Original endpoint maps, the full Borel, both
orientations, scalar conventions and degree one are retained. Lower-central
persistence and the final (6F) contradiction are subsequent source steps.
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

private theorem original_scalar_crossed_bound
    (hm : rotationOrder Q=8) (i j : Fin 2) (hij : i ≠ j)
    {b : ℕ} (hb : 0 < b) (hodd : Odd b)
    {F : Type} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hcard : Nat.card F=(2^b)^2) (hconj : ∀ x,J.conj x=x^(2^b))
    (hmodel : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup))
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (d : RootSection Q split j) (hden : d.denominator=⊥)
    (hd : d.numerator ≤ centralizer (rankOneScalar Q split j : Set (X ⧸ Q.D)))
    (x : rootAt Q split j (Q.simple i)) (hx : x ≠ 1)
    (hxd : (x : X ⧸ Q.D) ∈ d.numerator) :
    2^(8*b) ≤ Nat.card d.EffectiveCarrier := by
  let := h.finite_local j
  obtain ⟨Tj,hTj⟩ := h.sylow j
  obtain ⟨μ,σ,hσ,_⟩ := regular_unitary_cover_of_factor Q e h split J hb hcard hconj
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
  exact unitary_scalar_crossed_section_card_bound Q split J hb hodd hcard hconj hm i j hij
    hKj μ σ hσ hroot hsmall d hden hd x hx hxd

omit [Group G] e h in
private theorem scalar_derived_cartan_normalized (j : Fin 2)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j) :
    Q.tits.B ⊓ Q.tits.N ≤ normalizer
      ((unitaryScalarDerivedSection Q split j hKj).numerator : Set (X ⧸ Q.D)) := by
  have hH : Q.tits.B ⊓ Q.tits.N ≤
      normalizer (rankOneScalar Q split j : Set (X ⧸ Q.D)) :=
    (rankOne_torus_normalizes Q split j).trans
      (normalizer_le_normalizer_characteristic_image _ (center _))
  exact (le_inf (inf_le_left.trans ((Q.tits.B_le_standardParabolic _).trans
    (radical_commutator_normalized Q split j hKj)))
      (hH.trans (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf

/-- The actual scalar-fixed derived section is not contained in the nine-b
root subgroup. No representation or irreducibility premise is added. -/
theorem original_linear_unitary_scalar_derived_not_le_nine
    (hm : rotationOrder Q=8) (i j : Fin 2) (hij : i ≠ j)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hj : ClassicalGroup.IsPSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b) ∨
      IsSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b))
    (hKj : simpleRemainder Q split j ≤ localKernel Q j) :
    ¬ (unitaryScalarDerivedSection Q split j hKj).numerator ≤
      unitaryNineSubgroup Q split i j := by
  have hodd := (original_linear_unitary_all_quadratic_degree Q e h split hm i j hij ha hb hi hj).1
  have hsource := original_linear_unitary_nine_subgroup Q e h split hm i j hij ha hb hi hj
  have hfixed := (original_linear_unitary_cubic_fixed_roots Q e h split hm i j hij ha hb hi hj).2
  have hab := original_linear_unitary_cubic_radical_abelian Q e h split hm i j hij ha hb hi hj
  have hcenter := (original_linear_unitary_nine_subgroup_control Q e h split hm i j hij ha hb hi hj).1
  have applyModel {F : Type} [Field F] [Finite F] (J : HermitianForm 3 F)
      (hcard : Nat.card F=(2^b)^2) (hconj : ∀ x,J.conj x=x^(2^b))
      (hmodel : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
        Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
      ¬ (unitaryScalarDerivedSection Q split j hKj).numerator ≤
        unitaryNineSubgroup Q split i j := by
    intro hdK
    obtain ⟨_,μ,hZ,hY,hmoving,hker,ρ,hfaith,hsquare,hlarge⟩ :=
      original_linear_unitary_projective_degree Q e h split hm i j hij ha hb hi J hcard hconj hmodel
    let d := unitaryScalarDerivedSection Q split j hKj
    let K := unitaryNineSubgroup Q split i j
    let M := rootFrattiniAt Q split j (Q.simple i*Q.simple j*Q.simple i)
    let Y := simpleRemainder Q split j ⊓ centralizer (cartanThreeCore Q : Set (X ⧸ Q.D))
    have hd : d.numerator=K := original_linear_unitary_nine_rootSection_numerator
      Q e h split hm i j hij ha hb hi hj d hdK (scalar_derived_cartan_normalized Q split j hKj) hlarge
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
      (map_subtype_le _).trans (hd ▸ (show d.numerator ≤
        centralizer (rankOneScalar Q split j : Set (X ⧸ Q.D)) from inf_le_right))
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

/-- The full derived radical escapes the nine-b root subgroup, at the
literal original linear/unitary source factors. -/
theorem original_linear_unitary_derived_not_le_nine
    (hm : rotationOrder Q=8) (i j : Fin 2) (hij : i ≠ j)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hj : ClassicalGroup.IsPSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b) ∨
      IsSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b)) :
    ¬ ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ ≤
      unitaryNineSubgroup Q split i j := by
  have hKj : simpleRemainder Q split j ≤ localKernel Q j := by
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
  exact fun hd => original_linear_unitary_scalar_derived_not_le_nine Q e h split hm i j hij
    ha hb hi hj hKj (inf_le_left.trans hd)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
