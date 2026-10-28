module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponent.FittingComparison
public import Theory.SpecificGroups.SL2.BinaryOddRank
/-!
# Excluding chi-zero models in the actual F.6.18 fitting subgroup

Assuming a chi-zero block makes its two-core quotient simple, hence identifies
that quotient with its nontrivial image in the prime-to-three quotient. Binary
SL₂ and A₅ have three-rank at most one; a two-group quotient preserves this
bound. The full F.6.18 rows then contradict the actual component model, using
odd-field Sylows, alternating sections, or defining-prime cubes. Both corrected
source rows are included.

Source: Aschbacher--Smith 14.6.10(5), printed p.1029, and F.6.18,
printed pp.309--310.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section06
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace F618ChiZero
open FSource
universe u
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
    ((_root_.primeRank_le_of_injective 3 (commutator D).subtype Subtype.val_injective).trans hr)
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

private theorem odd_binary_impossible (F : FieldParameter.{u})
    (ho : Odd F.prime) (hc : 9 ≤ Nat.card F.Carrier)
    (e : generalizedFitting D ≃* PSL(2,F.Carrier))
    (B : BinaryField) (b : generalizedFitting D ≃* SL(2,B.Carrier)) : False := by
  have hodd : Odd (Nat.card F.Carrier) := by rw [F.card]; exact ho.pow
  have hl := pslTwo_order_ge_360 hodd hc
  obtain ⟨a⟩ := odd_linearTwo_binary_alternatingFive B
    ⟨F.prime,F.degree,F.prime_isPrime,ho,F.degree_pos,F.card⟩ b e
  rw [Nat.card_congr (e.symm.trans a).toEquiv,nat_card_alternatingGroup] at hl
  norm_num [Nat.factorial] at hl

/-- Under the derived three-rank bound, no full source row has a binary
SL₂ generalized Fitting subgroup. No representation premise is needed. -/
theorem source_not_binary_fitting {A C : Subgroup D} {S : Sylow 2 D}
    (hr : primeRank 3 D ≤ 1) (h : FSource.SourceAlternative A C S)
    (B : BinaryField) (b : generalizedFitting D ≃* SL(2,B.Carrier)) : False := by
  rcases h with (h | h) | h
  · obtain ⟨_,hs,hrow⟩ := full_F_rank_one hr h
    cases hrow with
    | primeLinear F hn hm e =>
      exact odd_binary_impossible F (Nat.odd_iff.mpr (by omega))
        (by rw [F.card,hn,pow_one]; omega) e B b
    | dihedral ht es =>
      exact binaryTwo_not_dihedralEight B ((fittingTopEquiv ht).symm.trans b) S es
    | squareLinear r =>
      have hm := r.congruence
      exact odd_binary_impossible r.field (Nat.odd_iff.mpr (by omega))
        (by rw [r.field.card,r.degree]; have h3 : 3 ≤ r.field.prime := by omega
            nlinarith) r.componentEquiv B b
    | degreeThree p hp hm hmodel =>
      have hd := degreeThree_prime_cube hp hmodel
      rw [Nat.card_congr b.toEquiv] at hd
      exact linearTwo_no_odd_prime_cube B
        (linearTwo_degree_le_seven (generalizedFitting D) B b S hs) hp (by omega) hd
  · obtain ⟨h⟩ := h
    exact binaryTwo_not_dihedralEight B
      ((fittingTopEquiv h.component).symm.trans b) S h.sylow.some
  · obtain ⟨h⟩ := h
    have hm := h.congruence
    exact odd_binary_impossible h.field (Nat.odd_iff.mpr (by omega))
      (by rw [h.field.card,h.degree]; have h3 : 3 ≤ h.field.prime := by omega
          nlinarith) h.componentEquiv B b

/-- The temporary binary model itself supplies the required three-rank
bound when the quotient by the actual fitting subgroup is a two-group. -/
theorem source_not_binary_of_two_quotient {A C : Subgroup D} {S : Sylow 2 D}
    (h : FSource.SourceAlternative A C S)
    (hquot : IsPGroup 2 (D ⧸ generalizedFitting D))
    (B : BinaryField) (b : generalizedFitting D ≃* SL(2,B.Carrier)) : False := by
  have hz : primeRank 3 (D ⧸ generalizedFitting D) = 0 := by
    apply PrimeRank.eq_zero_iff_not_dvd_card.mpr
    obtain ⟨n,hn⟩ := hquot.exists_card_eq
    rw [hn]
    exact fun hd => (by norm_num : ¬ 3 ∣ 2) (Nat.Prime.dvd_of_dvd_pow (by decide) hd)
  have hr := primeRank_le_ker_add (p := 3) (QuotientGroup.mk' (generalizedFitting D))
  rw [QuotientGroup.ker_mk',hz,add_zero,primeRank_equiv 3 b] at hr
  exact source_not_binary_fitting
    (hr.trans (Matrix.SL2.binary_odd_primeRank_le_one (by decide))) h B b

private theorem chiZero_binary_quotient {J : Type*} [Group J] [Finite J]
    (hq : IsQuasisimple (J ⧸ pCore 2 J)) (hc : ChapterC.IsChiZeroBlock J) :
    ∃ B : BinaryField, Nonempty ((J ⧸ pCore 2 J) ≃* SL(2,B.Carrier)) := by
  rcases hc with ⟨n,hn,_,F,_,_,hF,_,hm⟩ | hc | hc
  · obtain ⟨b⟩ := hm.quotient_iso
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    let : Algebra (ZMod 2) F := ZMod.algebra _ _
    exact ⟨{ Carrier := F, degree := n, degree_pos := by omega, card_eq := hF },⟨b⟩⟩
  · obtain ⟨b⟩ := hc.2.2.quotient_iso
    have hcard : Nat.card (J ⧸ pCore 2 J) = 3 := by
      rw [Nat.card_congr b.toEquiv,nat_card_alternatingGroup]
      norm_num
    let := hq
    let : IsCyclic (J ⧸ pCore 2 J) := isCyclic_of_prime_card hcard
    have hsub : Subsingleton (J ⧸ pCore 2 J) := inferInstance
    have hcard' : Nat.card (J ⧸ pCore 2 J) = 1 := Nat.card_unique
    omega
  · obtain ⟨b⟩ := hc.2.2.quotient_iso
    exact ⟨BinaryField.four,⟨b.trans alternatingFiveLinearEquiv⟩⟩

/-- The actual two-core quotient cannot be binary SL₂: its simple model
maps isomorphically to the nontrivial selected component in the quotient. -/
theorem not_binary_quotient_of_two_quotient {J : Type*} [Group J] [Finite J]
    (K : Subgroup J) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hi : IsComponent (J ⧸ pPrimeCore 3 J) (K.map (QuotientGroup.mk' (pPrimeCore 3 J))))
    (heq : K.map (QuotientGroup.mk' (pPrimeCore 3 J)) =
      generalizedFitting (J ⧸ pPrimeCore 3 J))
    {A C : Subgroup (J ⧸ pPrimeCore 3 J)} {S : Sylow 2 (J ⧸ pPrimeCore 3 J)}
    (hsource : FSource.SourceAlternative A C S)
    (hquot : IsPGroup 2 ((J ⧸ pPrimeCore 3 J) ⧸
      generalizedFitting (J ⧸ pPrimeCore 3 J)))
    (B : BinaryField) (b : (K ⧸ pCore 2 K) ≃* SL(2,B.Carrier)) : False := by
  let := hq
  have hz : center (K ⧸ pCore 2 K) = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hh := (centerCongr b ⟨x,hx⟩).property
    change b x ∈ center SL(2,B.Carrier) at hh
    rw [Theory.PSL2.sl2_center_eq_bot] at hh
    apply mem_bot.mpr
    apply b.injective
    exact (mem_bot.mp hh).trans b.map_one.symm
  let : IsSimpleGroup ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) :=
    IsQuasisimple.simple
  let : IsSimpleGroup (K ⧸ pCore 2 K) :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.isSimpleGroup
  let : IsQuasisimple (K.map (QuotientGroup.mk' (pPrimeCore 3 J))) := hi.2
  let : IsSimpleGroup ((K.map (QuotientGroup.mk' (pPrimeCore 3 J))) ⧸
      center (K.map (QuotientGroup.mk' (pPrimeCore 3 J)))) := IsQuasisimple.simple
  let : Nontrivial (K.map (QuotientGroup.mk' (pPrimeCore 3 J))) :=
    (QuotientGroup.mk'_surjective (center _)).nontrivial
  let f := twoCoreToThreePrimeImage K hK.subnormal
  have hf := twoCoreToThreePrimeImage_surjective K hK.subnormal
  let a := (MulEquiv.ofBijective f ⟨f.injective_of_surjective_of_simple hf,hf⟩).trans
    (MulEquiv.subgroupCongr heq)
  exact source_not_binary_of_two_quotient hsource hquot B (a.symm.trans b)

/-- Apply the full row exclusion to the literal image of the original K.
The sole structural premise is the two-group quotient by F*, supplied by
the source two-residual theorem; no ambient three-rank premise is imposed. -/
theorem not_chiZero_of_two_quotient {J : Type*} [Group J] [Finite J]
    (K : Subgroup J) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hi : IsComponent (J ⧸ pPrimeCore 3 J) (K.map (QuotientGroup.mk' (pPrimeCore 3 J))))
    (heq : K.map (QuotientGroup.mk' (pPrimeCore 3 J)) =
      generalizedFitting (J ⧸ pPrimeCore 3 J))
    {A C : Subgroup (J ⧸ pPrimeCore 3 J)} {S : Sylow 2 (J ⧸ pPrimeCore 3 J)}
    (hsource : FSource.SourceAlternative A C S)
    (hquot : IsPGroup 2 ((J ⧸ pPrimeCore 3 J) ⧸
      generalizedFitting (J ⧸ pPrimeCore 3 J))) : ¬ ChapterC.IsChiZeroBlock K := by
  intro hc
  obtain ⟨B,⟨b⟩⟩ := chiZero_binary_quotient hq hc
  exact not_binary_quotient_of_two_quotient K hK hq hi heq hsource hquot B b

end F618ChiZero
end CFSG.Quasithin.Chapter14.Section06
