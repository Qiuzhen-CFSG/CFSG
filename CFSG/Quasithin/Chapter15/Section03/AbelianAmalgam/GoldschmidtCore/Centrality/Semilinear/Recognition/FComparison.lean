module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.ModelBounds
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.ComponentComparison

/-!
# Exhaustive comparison of the full F.6.18 and B.5.6 alternatives

Rank one at three excludes actual cubic products, extraspecial three-groups,
alternating central quotients and M₁₂ sections. The remaining F.6.18 rows
supply a quasisimple actual generalized Fitting subgroup and small Sylows.
Its inclusion in the offender subgroup yields the derived B-side component
models. Dihedral versus elementary Sylows and the odd-field order formula
exclude the odd rank-one rows except (6); defining-prime cubes exclude the
odd degree-three rows. In row (6), the component fills the ambient group,
and the original B-side equivalence supplies SL₃(2).

Both classifications remain full universal input implications. Every reduced
list below is proved from those implications; none is an input assumption.
The full group and module alternatives are retained in the exported result.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, F.6.18,
pp.309--310, B.5.1/B.5.6, pp.99--105, and 15.3.68, pp.1154--1155.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open FSource
universe u v
variable {D : Type u} [Group D] [Finite D]

private theorem no_triple_alternating (hr : primeRank 3 D ≤ 1) {n : ℕ} (hn : 6 ≤ n)
    (h : TripleAlternating D n) : False := by
  obtain ⟨e⟩ := h.quotient
  exact no_alternating_section hr ⊤ hn
    (e.toMonoidHom.comp ((QuotientGroup.mk' _).comp (topEquiv : (⊤ : Subgroup D) ≃* D).toMonoidHom))
    (e.surjective.comp ((QuotientGroup.mk'_surjective _).comp (topEquiv : (⊤ : Subgroup D) ≃* D).surjective))

private theorem no_triple_symmetric (hr : primeRank 3 D ≤ 1) {n : ℕ} (hn : 6 ≤ n)
    (h : TripleSymmetric D n) : False :=
  no_triple_alternating
    ((primeRank_le_of_injective 3 (commutator D).subtype Subtype.val_injective).trans hr)
    hn h.derived

private theorem degreeThree_comap {A B : Type u} [Group A] [Group B]
    {p : ℕ} (e : A ≃* B) (h : DegreeThree p B) : DegreeThree p A := by
  cases h with
  | linear F hc hs a => exact .linear F hc hs (e.trans a)
  | projectiveLinear F hc hs a => exact .projectiveLinear F hc hs (e.trans a)
  | unitary F J hc hf hs a => exact .unitary F J hc hf hs (e.trans a)
  | projectiveUnitary F J hc hf hs a => exact .projectiveUnitary F J hc hf hs (e.trans a)

private def fittingTopEquiv (h : generalizedFitting D = ⊤) : generalizedFitting D ≃* D :=
  (MulEquiv.subgroupCongr h).trans topEquiv

private inductive SurvivingRow (S : Sylow 2 D) : Prop
  | primeLinear (F : FieldParameter.{u}) (degree : F.degree = 1)
      (congruence : F.prime % 24 = 11 ∨ F.prime % 24 = 13)
      (component : generalizedFitting D ≃* PSL(2,F.Carrier))
  | dihedral (component : generalizedFitting D = ⊤)
      (sylow : S ≃* DihedralGroup 4)
  | squareLinear (data : FieldExtensionRow (D := D))
  | degreeThree (p : ℕ) (prime : p.Prime) (congruence : p % 8 = 3 ∨ p % 8 = 5)
      (model : DegreeThree p (generalizedFitting D))

private theorem full_F_rank_one {G₁ G₂ : Subgroup D} {S : Sylow 2 D}
    (hr : primeRank 3 D ≤ 1) (h : FSource.Alternative G₁ G₂ S) :
    IsQuasisimple (generalizedFitting D) ∧ Nat.card S ≤ 128 ∧ SurvivingRow S := by
  cases h with
  | one _ _ _ hn => exact (hn (threeCore_cyclic hr)).elim
  | two hm =>
    rcases hm with hm | hm
    · obtain ⟨e⟩ := hm
      exact (no_symmetricThree_product hr e).elim
    · obtain ⟨N, _, he, _⟩ := hm
      exact (no_extraspecial_three hr N he).elim
  | three h _ _ _ =>
    have hc : Nat.card h.field.Carrier = h.field.prime := by
      rw [h.field.card, h.degree, pow_one]
    have ho : Odd (Nat.card h.field.Carrier) := by
      rw [hc, Nat.odd_iff]
      have hm := h.congruence
      omega
    exact (no_cubic_product hr
      (by rw [Nat.card_congr h.firstEquiv.toEquiv]; exact three_dvd_odd_pslTwo ho)
      (by rw [Nat.card_congr h.secondEquiv.toEquiv]; simp [C])
      ((h.first ⊔ h.second).subtype.comp h.product.toMonoidHom)
      (Subtype.val_injective.comp h.product.injective)).elim
  | four F hn hm e ht hq hes _ _ =>
    obtain ⟨es⟩ := hes
    refine ⟨hq, ?_, .primeLinear F hn hm ((fittingTopEquiv ht).trans e)⟩
    rw [Nat.card_congr es.toEquiv]
    norm_num [E4, C, Nat.card_prod]
  | five F hn hm _ e hq hes _ _ =>
    obtain ⟨es⟩ := hes
    refine ⟨hq, ?_, .primeLinear F hn hm e⟩
    rw [Nat.card_congr es.toEquiv, DihedralGroup.nat_card]
    norm_num
  | six hm ht hq hes _ _ =>
    obtain ⟨es⟩ := hes
    rcases hm with hm | _
    · exact (no_triple_alternating hr (by decide) hm).elim
    · refine ⟨hq, ?_, .dihedral ht es⟩
      rw [Nat.card_congr es.toEquiv, DihedralGroup.nat_card]
      norm_num
  | seven hm _ _ _ _ =>
    rcases hm with hm | h
    · obtain ⟨e⟩ := hm
      have hu := hr
      rw [primeRank_equiv 3 e] at hu
      have hl := alternatingGroup.TwoThreeCycles.two_le_primeRank (n := 7) (by decide)
      omega
    · exact (no_triple_alternating hr (by decide) h).elim
  | eight hm hq hes _ _ =>
    obtain ⟨es⟩ := hes
    rcases hm with hm | hm
    · obtain ⟨h⟩ := hm
      exact (no_triple_symmetric hr (by decide) h).elim
    · obtain ⟨h⟩ := hm
      refine ⟨hq, ?_, .squareLinear h⟩
      rw [Nat.card_congr es.toEquiv, Nat.card_prod, DihedralGroup.nat_card]
      norm_num [C]
  | nine hm _ _ _ _ =>
    rcases hm with hm | hm
    · obtain ⟨e⟩ := hm
      exact (no_symmetric_section hr ⊤ (by decide)
        (e.toMonoidHom.comp (topEquiv : (⊤ : Subgroup D) ≃* D).toMonoidHom)
        (e.surjective.comp (topEquiv : (⊤ : Subgroup D) ≃* D).surjective)).elim
    · obtain ⟨h⟩ := hm
      exact (no_triple_symmetric hr (by decide) h).elim
  | ten p hp hm h ht hq hes _ _ =>
    obtain ⟨es⟩ := hes
    refine ⟨hq, ?_, .degreeThree p hp hm (degreeThree_comap (fittingTopEquiv ht) h)⟩
    rw [Nat.card_congr es.toEquiv, RegularWreathProduct.card]
    norm_num [C]
  | eleven h hq hs _ _ =>
    refine ⟨hq, ?_, .degreeThree h.prime h.prime_isPrime h.congruence h.model.model⟩
    rw [extension_card hs]
    norm_num [C4Square, E4, C, Nat.card_prod]
  | twelve e _ _ _ _ =>
    exact (no_mathieuTwelve_section hr ⊤ (e.toMonoidHom.comp (topEquiv : (⊤ : Subgroup D) ≃* D).toMonoidHom)
      (e.surjective.comp (topEquiv : (⊤ : Subgroup D) ≃* D).surjective)).elim
  | thirteen _ e _ _ _ _ =>
    exact (no_mathieuTwelve_section hr (generalizedFitting D) e.toMonoidHom e.surjective).elim

private theorem odd_model_not_small (F : FieldParameter.{u})
    (ho : Odd F.prime) (hc : 9 ≤ Nat.card F.Carrier)
    (e : generalizedFitting D ≃* PSL(2,F.Carrier))
    (h : (∃ B : BinaryField, Nonempty (generalizedFitting D ≃* SL(2,B.Carrier))) ∨
      Nonempty (generalizedFitting D ≃* SL(3,ZMod 2)) ∨
      Nonempty (generalizedFitting D ≃* alternatingGroup (Fin 5))) : False := by
  have hodd : Odd (Nat.card F.Carrier) := by rw [F.card]; exact ho.pow
  have hl := pslTwo_order_ge_360 hodd hc
  have noA (a : generalizedFitting D ≃* alternatingGroup (Fin 5)) : False := by
    rw [Nat.card_congr (e.symm.trans a).toEquiv, nat_card_alternatingGroup] at hl
    norm_num [Nat.factorial] at hl
  rcases h with h | h | h
  · obtain ⟨B, ⟨a⟩⟩ := h
    obtain ⟨b⟩ := odd_linearTwo_binary_alternatingFive B
      ⟨F.prime, F.degree, F.prime_isPrime, ho, F.degree_pos, F.card⟩ a e
    exact noA b
  · obtain ⟨a⟩ := h
    rw [Nat.card_congr (e.symm.trans a).toEquiv, Matrix.PSL3Two.card_SL] at hl
    omega
  · obtain ⟨a⟩ := h
    exact noA a

private theorem binaryTwo_not_dihedralEight (B : BinaryField)
    (e : D ≃* SL(2,B.Carrier)) (S : Sylow 2 D) (es : S ≃* DihedralGroup 4) : False := by
  let R := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let : IsElementaryAbelian 2 R := linearTwo_sylow_elementary B R
  let er : S ≃* R := e.subgroupMap _
  let x : R := er (es.symm (DihedralGroup.r 1))
  have hs : x ^ 2 = 1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 R) x
  have hx : orderOf x = 4 := by
    rw [show x = er (es.symm (DihedralGroup.r 1)) from rfl,
      er.orderOf_eq, es.symm.orderOf_eq, DihedralGroup.orderOf_r_one]
  have hd := orderOf_dvd_of_pow_eq_one hs
  rw [hx] at hd
  norm_num at hd

private theorem alternatingFive_not_dihedralEight
    (e : D ≃* alternatingGroup (Fin 5)) (S : Sylow 2 D) (es : S ≃* DihedralGroup 4) : False := by
  let R := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hr : Nat.card R = 4 := by
    rw [R.card_eq_multiplicity,
      show Nat.card (alternatingGroup (Fin 5)) = 60 by
        rw [nat_card_alternatingGroup, Nat.card_fin]; norm_num]
    decide +kernel
  have he : Nat.card R = Nat.card S := card_map_of_injective e.injective
  rw [he, Nat.card_congr es.toEquiv, DihedralGroup.nat_card] at hr
  omega

/-- The actual dihedral Sylow and full ambient component suffice for the
rank-one comparison. No local-generator model is required. -/
theorem dihedral_classification_comparison
    (S : Sylow 2 D) (es : S ≃* DihedralGroup 4)
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W)
    (hr : primeRank 3 D ≤ 1) (hne : offenderSubgroup ρ ≠ ⊥)
    (hcore : pCore 2 D = ⊥)
    (hq : IsQuasisimple (generalizedFitting D)) (ht : generalizedFitting D = ⊤)
    (hb : SourceAlternative (ρ.comp (offenderSubgroup ρ).subtype)) :
    offenderSubgroup ρ = ⊤ ∧ Nonempty (D ≃* SL(3,ZMod 2)) := by
  have hs : Nat.card S ≤ 128 := by
    rw [Nat.card_congr es.toEquiv, DihedralGroup.nat_card]
    norm_num
  have hb' := fitting_source_rank_one ρ hr hne hcore hq S hs hb
  rcases hb' with ⟨_, B, _, ⟨e⟩⟩ | ⟨hi, ⟨e⟩⟩ | ⟨_, ⟨e⟩⟩
  · exact (binaryTwo_not_dihedralEight B ((fittingTopEquiv ht).symm.trans e) S es).elim
  · exact ⟨hi.symm.trans ht, ⟨(fittingTopEquiv ht).symm.trans e⟩⟩
  · exact (alternatingFive_not_dihedralEight ((fittingTopEquiv ht).symm.trans e) S es).elim

/-- Exhaust the full F-side list against the derived full B-side list.
The equivalence is inherited from B.5.1 on the actual component. -/
theorem full_classification_comparison
    {G₁ G₂ : Subgroup D} {S : Sylow 2 D}
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W)
    (hr : primeRank 3 D ≤ 1) (hne : offenderSubgroup ρ ≠ ⊥)
    (hcore : pCore 2 D = ⊥)
    (hf : FSource.Alternative G₁ G₂ S)
    (hb : SourceAlternative (ρ.comp (offenderSubgroup ρ).subtype)) :
    offenderSubgroup ρ = ⊤ ∧ Nonempty (D ≃* SL(3,ZMod 2)) := by
  obtain ⟨hq, hs, hrow⟩ := full_F_rank_one hr hf
  have hb' := fitting_source_rank_one ρ hr hne hcore hq S hs hb
  have hmodels : (∃ B : BinaryField, Nonempty (generalizedFitting D ≃* SL(2,B.Carrier))) ∨
      Nonempty (generalizedFitting D ≃* SL(3,ZMod 2)) ∨
      Nonempty (generalizedFitting D ≃* alternatingGroup (Fin 5)) := by
    rcases hb' with ⟨_, B, _, he⟩ | ⟨_, he⟩ | ⟨_, he⟩
    · exact Or.inl ⟨B, he⟩
    · exact Or.inr (Or.inl he)
    · exact Or.inr (Or.inr he)
  cases hrow with
  | primeLinear F hn hm e =>
    exact (odd_model_not_small F (Nat.odd_iff.mpr (by omega))
      (by rw [F.card, hn, pow_one]; omega) e hmodels).elim
  | squareLinear h =>
    exact (odd_model_not_small h.field (Nat.odd_iff.mpr (by have := h.congruence; omega))
      (by rw [h.field.card, h.degree]; have h3 : 3 ≤ h.field.prime := by have := h.congruence; omega
          nlinarith) h.componentEquiv hmodels).elim
  | degreeThree p hp hm h =>
    have hp2 : p ≠ 2 := by omega
    rcases hmodels with hmodels | hmodels | hmodels
    · obtain ⟨B, ⟨e⟩⟩ := hmodels
      have hd := degreeThree_prime_cube hp h
      rw [Nat.card_congr e.toEquiv] at hd
      exact (linearTwo_no_odd_prime_cube B
        (linearTwo_degree_le_seven (generalizedFitting D) B e S hs) hp hp2 hd).elim
    · obtain ⟨e⟩ := hmodels
      exact (degreeThree_not_binaryThree hp hp2 h e).elim
    · obtain ⟨e⟩ := hmodels
      exact (degreeThree_not_alternatingFive hp hp2 h e).elim
  | dihedral ht es =>
    rcases hb' with ⟨_, B, _, ⟨e⟩⟩ | ⟨hi, ⟨e⟩⟩ | ⟨_, ⟨e⟩⟩
    · exact (binaryTwo_not_dihedralEight B ((fittingTopEquiv ht).symm.trans e) S es).elim
    · exact ⟨hi.symm.trans ht, ⟨(fittingTopEquiv ht).symm.trans e⟩⟩
    · exact (alternatingFive_not_dihedralEight ((fittingTopEquiv ht).symm.trans e) S es).elim

/-- Apply the two full universal classifications. This keeps both source
conclusions, proves that the actual offender subgroup fills D, and constructs
the actual binary degree-three equivalence. -/
theorem recognition_of_full_classifications {K : GroupClass.{u}}
    (sourceF : FSource.ClassificationInput K) (sourceB : GeneralClassificationInput.{u,v} K)
    (G₁ G₂ : Subgroup D) (triple : ChapterF.IsGoldschmidtTriple G₁ G₂)
    (cover : ThreePrimeSQTKQuotient K D)
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W)
    (hyp : FFHypothesis K (ρ.comp (offenderSubgroup ρ).subtype))
    (hr : primeRank 3 D ≤ 1) (hne : offenderSubgroup ρ ≠ ⊥)
    (hcore : pCore 2 D = ⊥) :
    (∃ S : Sylow 2 D, G₁ ⊓ G₂ = (S : Subgroup D) ∧
      (FSource.Alternative G₁ G₂ S ∨ FSource.Alternative G₂ G₁ S)) ∧
    SourceAlternative (ρ.comp (offenderSubgroup ρ).subtype) ∧
    offenderSubgroup ρ = ⊤ ∧ Nonempty (D ≃* SL(3,ZMod 2)) := by
  obtain ⟨S, hS, hf⟩ := sourceF D G₁ G₂ triple cover
  have hb := sourceB _ _ _ hyp
  refine ⟨⟨S, hS, hf⟩, hb, ?_⟩
  rcases hf with hf | hf
  · exact full_classification_comparison ρ hr hne hcore hf hb
  · exact full_classification_comparison ρ hr hne hcore hf hb

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
