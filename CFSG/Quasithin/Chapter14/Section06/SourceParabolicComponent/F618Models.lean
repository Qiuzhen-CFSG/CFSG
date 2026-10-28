module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponent.Input
public import Theory.GroupTheory.GeneralizedFitting.TwoCoreImageComparison
public import Theory.GroupTheory.SimpleSectionSolvableReduction
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.ChiZeroQuotient
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.ModelBounds
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.Complete

/-!
# Marked F.6.18 on the original parabolic quotient

The original source supplies the SQTK cover and the retained Goldschmidt
triple modulo its prime-to-three core. Apply the completed corrected F.6.18
classification with both original parabolic images and their common Sylow.
The cyclic three-core excludes the first row, and the selected component
excludes the solvable second row. In the product row, perfectness puts every
component in the first factor; its simple odd-prime model identifies that
factor with the same selected component and excludes chi-zero blocks.
In every other row the component is exactly the generalized Fitting subgroup.
The intrinsic two-core quotient and its image retain a canonical isomorphism
of central quotients, with the commuting formula on representatives.

Source: Aschbacher--Smith 14.6.10(5), printed p.1029, comparing C.2.7 with
F.6.18, pp.309--310. Exclusion of chi-zero blocks in the remaining
quasisimple rows and the final rank-three argument are separate steps.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section06
open ChapterF SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
variable {G : Type*} [Group G] [Finite G]

private theorem f618_two_solvable {D : Type*} [Group D] [Finite D]
    (hm : Nonempty (D ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∨
      ∃ N : Subgroup D, ∃ _ : N.Normal, IsExtraspecial 3 N ∧ Nat.card N = 27 ∧
        Monoid.exponent N = 3 ∧ Nonempty ((D ⧸ N) ≃* FSource.E4)) :
    Group.IsSolvable D := by
  rcases hm with hm | ⟨N,_,hN,_,_,⟨e⟩⟩
  · obtain ⟨e⟩ := hm
    let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
    let : Group.IsSolvable (Equiv.Perm (Fin 3)) := Group.isSolvable_of_isSolvable_injective
      (Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb (by decide : 3 ≤ 4)))
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  · let : Group.IsNilpotent N := hN.isPGroup.isNilpotent
    let : Group.IsSolvable (D ⧸ N) :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    exact (Group.isSolvable_iff_subgroup_quotient N).mpr ⟨inferInstance,inferInstance⟩

private theorem f618_product_component {D : Type*} [Group D] [Finite D]
    {S : Sylow 2 D} (r : FSource.ProductRow S) {K : Subgroup D}
    (hK : IsComponent D K) : K = r.first := by
  let := hK.2
  let : Group.IsNilpotent (D ⧸ pResidual 2 D) :=
    (isPGroup_quotient_pResidual 2).isNilpotent
  have hKR : K ≤ r.first ⊔ r.second :=
    ((le_solvableResidual_of_isPerfect K).trans
      (solvableResidual_le_of_solvable_quotient (pResidual 2 D))).trans_eq r.residual
  let f : K →* r.first × r.second := r.product.symm.toMonoidHom.comp (inclusion hKR)
  let χ : K →* FSource.C 3 :=
    r.secondEquiv.toMonoidHom.comp ((MonoidHom.snd r.first r.second).comp f)
  let : Group.IsPerfect χ.range := Group.IsPerfect.range χ
  have hχ (x : K) : χ x = 1 :=
    congrArg Subtype.val (Subsingleton.elim (χ.rangeRestrict x) 1)
  have hs (x : K) : (f x).2 = 1 := by
    apply r.secondEquiv.injective
    exact (hχ x).trans r.secondEquiv.map_one.symm
  have hKF : K ≤ r.first := by
    intro k hk
    let x : K := ⟨k,hk⟩
    have he := congrArg (fun y : (r.first ⊔ r.second : Subgroup D) => (y : D))
      (r.product.apply_symm_apply (inclusion hKR x))
    change (r.product (f x) : D) = k at he
    rw [r.product_apply,hs x,Subgroup.coe_one,mul_one] at he
    exact he ▸ (f x).1.property
  have hp : 3 < r.field.prime := by have hc := r.congruence; omega
  have hcard : 3 < Nat.card r.field.Carrier := by
    rw [r.field.card,r.degree,pow_one]
    exact hp
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) r.field.Carrier) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  have hfirst : IsSimpleGroup r.first := r.firstEquiv.isSimpleGroup
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hfirst
      (hK.subgroupOf hKF).1 with hb | ht
  · exact (hK.isCComponent.ne_bot (by
      rw [← map_subgroupOf_eq_of_le hKF,hb,Subgroup.map_bot])).elim
  · exact le_antisymm hKF (subgroupOf_eq_top.mp ht)

private theorem chiZero_not_f618_product_model {D J : Type*}
    [Group D] [Finite D] [Group J] [Finite J] {S : Sylow 2 D}
    (r : FSource.ProductRow S) (hc : ChapterC.IsChiZeroBlock J)
    (e : (J ⧸ pCore 2 J) ≃* r.first) : False := by
  let a := e.trans r.firstEquiv
  have hcard : Nat.card r.field.Carrier = r.field.prime := by
    rw [r.field.card,r.degree,pow_one]
  have ho : Odd r.field.prime := by rw [Nat.odd_iff]; have hh := r.congruence; omega
  rcases hc with ⟨n,hn,_,F,_,_,hF,_,hm⟩ | hc | hc
  · obtain ⟨b⟩ := hm.quotient_iso
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    let : Algebra (ZMod 2) F := ZMod.algebra _ _
    let field : Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.BinaryField :=
      { Carrier := F, degree := n, degree_pos := by omega, card_eq := hF }
    obtain ⟨c⟩ := odd_linearTwo_binary_alternatingFive field
      ⟨r.field.prime,1,r.field.prime_isPrime,ho,by decide,by simpa using hcard⟩ b a
    exact primeRow_not_alternatingFive r.field.prime_isPrime hcard r.congruence
      (a.symm.trans c)
  · obtain ⟨b⟩ := hc.2.2.quotient_iso
    have hb := pslTwo_order_ge_660 (hcard ▸ ho)
      (show 11 ≤ Nat.card r.field.Carrier by rw [hcard]; have hh := r.congruence; omega)
    rw [Nat.card_congr (a.symm.trans b).toEquiv,nat_card_alternatingGroup] at hb
    norm_num [Nat.factorial] at hb
  · obtain ⟨b⟩ := hc.2.2.quotient_iso
    exact primeRow_not_alternatingFive r.field.prime_isPrime hcard r.congruence
      (a.symm.trans b)

private theorem f618_product_excludes_chiZero {D J : Type*}
    [Group D] [Finite D] [Group J] [Finite J] {S : Sylow 2 D}
    (r : FSource.ProductRow S) (K : Subgroup J) (hK : K.IsCComponent)
    (hi : IsComponent (J ⧸ pPrimeCore 3 J) (K.map (QuotientGroup.mk' (pPrimeCore 3 J))))
    (e : (K.map (QuotientGroup.mk' (pPrimeCore 3 J))) ≃* r.first) :
    ¬ ChapterC.IsChiZeroBlock K := by
  intro hc
  let : IsSimpleGroup (K ⧸ pCore 2 K) := hc.quotient_simple
  let : IsQuasisimple (K.map (QuotientGroup.mk' (pPrimeCore 3 J))) := hi.2
  let : IsSimpleGroup ((K.map (QuotientGroup.mk' (pPrimeCore 3 J))) ⧸
      center (K.map (QuotientGroup.mk' (pPrimeCore 3 J)))) := IsQuasisimple.simple
  let : Nontrivial (K.map (QuotientGroup.mk' (pPrimeCore 3 J))) :=
    (QuotientGroup.mk'_surjective (center _)).nontrivial
  let f := twoCoreToThreePrimeImage K hK.subnormal
  have hf := twoCoreToThreePrimeImage_surjective K hK.subnormal
  let j := MulEquiv.ofBijective f ⟨f.injective_of_surjective_of_simple hf,hf⟩
  exact chiZero_not_f618_product_model r hc (j.trans e)

private theorem f618_source_component_cases {D : Type*} [Group D] [Finite D]
    {A B K : Subgroup D} {S : Sylow 2 D}
    (hK : IsComponent D K) (hc : IsCyclic (pCore 3 D))
    (hr : FSource.SourceAlternative A B S) :
    (∃ r : FSource.ProductRow S, K = r.first) ∨
      (K = generalizedFitting D ∧ IsQuasisimple (generalizedFitting D)) := by
  have hns : ¬ Group.IsSolvable D := by
    intro hs
    let := hs
    exact hK.isCComponent.not_isSolvable inferInstance
  have hq : Nonempty (FSource.ProductRow S) ∨ IsQuasisimple (generalizedFitting D) := by
    rcases hr with (hr | hr) | hr
    · cases hr with
      | one _ _ _ hn => exact (hn hc).elim
      | two hm => exact (hns (f618_two_solvable hm)).elim
      | three r _ _ _ => exact Or.inl ⟨r⟩
      | four _ _ _ _ _ hq _ _ _ => exact Or.inr hq
      | five _ _ _ _ _ hq _ _ _ => exact Or.inr hq
      | six _ _ hq _ _ _ => exact Or.inr hq
      | seven _ hq _ _ _ => exact Or.inr hq
      | eight _ hq _ _ _ => exact Or.inr hq
      | nine _ hq _ _ _ => exact Or.inr hq
      | ten _ _ _ _ _ hq _ _ _ => exact Or.inr hq
      | eleven _ hq _ _ _ => exact Or.inr hq
      | twelve _ hq _ _ _ => exact Or.inr hq
      | thirteen _ _ hq _ _ _ => exact Or.inr hq
    · exact Or.inr hr.some.quasisimple
    · exact Or.inr hr.some.quasisimple
  rcases hq with hp | hq
  · exact Or.inl ⟨hp.some,f618_product_component hp.some hK⟩
  · exact Or.inr ⟨hK.eq_of_le ⟨(inferInstance : (generalizedFitting D).Normal).isSubnormal,hq⟩
      (component_le_generalizedFitting D K hK),hq⟩

private theorem f618_component_central_quotient {J : Type*} [Group J] [Finite J]
    (K : Subgroup J) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hi : IsComponent (J ⧸ pPrimeCore 3 J) (K.map (QuotientGroup.mk' (pPrimeCore 3 J)))) :
    let q := QuotientGroup.mk' (pPrimeCore 3 J)
    ∃ e : ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) ≃*
        ((K.map q) ⧸ center (K.map q)),
      ∀ k : K, e (QuotientGroup.mk' (center (K ⧸ pCore 2 K))
        (QuotientGroup.mk' (pCore 2 K) k)) =
          QuotientGroup.mk' (center (K.map q)) (q.subgroupMap K k) := by
  let := hq
  let : IsQuasisimple (K.map (QuotientGroup.mk' (pPrimeCore 3 J))) := hi.2
  let : IsSimpleGroup ((K.map (QuotientGroup.mk' (pPrimeCore 3 J))) ⧸
      center (K.map (QuotientGroup.mk' (pPrimeCore 3 J)))) := IsQuasisimple.simple
  let : Nontrivial (K.map (QuotientGroup.mk' (pPrimeCore 3 J))) :=
    (QuotientGroup.mk'_surjective (center _)).nontrivial
  exact ⟨IsQuasisimple.centralQuotientEquiv (twoCoreToThreePrimeImage K hK.subnormal)
    (twoCoreToThreePrimeImage_surjective K hK.subnormal), fun _ => rfl⟩

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (hindex : (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u).relIndex
        (T : Subgroup G) = 2)
    (hmove : ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G))
    (hproduct : ∀ t ∈ (T : Subgroup G), t ∉ suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u →
        ¬ Mc.pCoreIn 2 ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G))
    (hU3 : Mc ⊓ normalizer (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u : Set G) =
        (T : Subgroup G))
    (hlocal : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
      (H ⊓ centralizer ({u} : Set G)))

include hG hempty hM hunique hmany hcard e hab H hH hu hindex hmove hproduct hU3 hlocal


/-- The complete F.6.18 source alternatives on the literal prime-to-three quotient. -/
theorem source_parabolic_quotient_f618
    (hcoreIndex : 4 < (H.pCoreIn 2).relIndex (T : Subgroup G))
    (hrank : 4 ≤ Nat.log 2 ((centralizer (H.pCoreIn 2 : Set G)).relIndex
      (conjugateSpanBy (localModule T M) H)))
    (I I2 : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (hSI2 : (T : Subgroup G) ⊓ I ≤ I2) (hI2H : I2 ≤ H)
    (hquot2 : Nonempty ((I2 ⧸ pCore 2 I2) ≃* Equiv.Perm (Fin 3)))
    (hout : ¬ I ⊓ M ≤ Mc)
    (hgen : ((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)) ⊔ I2 = I) :
    let I1 := (pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)
    let q := QuotientGroup.mk' (pPrimeCore 3 I)
    let A := (I1.subgroupOf I).map q
    let B := (I2.subgroupOf I).map q
    IsGoldschmidtTriple A B ∧ IsCyclic (pCore 3 (I ⧸ pPrimeCore 3 I)) ∧
      ∃ S : Sylow 2 (I ⧸ pPrimeCore 3 I), A ⊓ B = (S : Subgroup _) ∧
        (FSource.SourceAlternative A B S ∨ FSource.SourceAlternative B A S) := by
  obtain ⟨ht,hc⟩ := source_parabolic_quotient_preparation hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal hcoreIndex hrank
    I I2 hI hSI2 hI2H hquot2 hout hgen
  have hsq : IsSQTK KnownSimple.IsKnownSimple I := by
    let N := normalizer (I.pCoreIn 2 : Set G)
    have hIN : I ≤ N := I.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
    have hN : IsTwoLocal N := ⟨I.pCoreIn 2,hI.1.1,isPGroup_pCoreIn 2 I,rfl⟩
    exact (IsSQTK.equiv (subgroupOfEquivOfLe hIN)).mp
      ((hG.twoLocal_sqtk hN).subgroup (I.subgroupOf N))
  exact ⟨ht,hc,FSource.sourceClassification_knownSimple_complete _ _ _ ht
    { Cover := I, sqtk := hsq, equiv := MulEquiv.refl _ }⟩

/-- The same original component is either in the explicit product branch or
is exactly the generalized Fitting subgroup of the source quotient. -/
theorem source_parabolic_f618_component
    (hcoreIndex : 4 < (H.pCoreIn 2).relIndex (T : Subgroup G))
    (hrank : 4 ≤ Nat.log 2 ((centralizer (H.pCoreIn 2 : Set G)).relIndex
      (conjugateSpanBy (localModule T M) H)))
    (I I2 : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (hSI2 : (T : Subgroup G) ⊓ I ≤ I2) (hI2H : I2 ≤ H)
    (hquot2 : Nonempty ((I2 ⧸ pCore 2 I2) ≃* Equiv.Perm (Fin 3)))
    (hout : ¬ I ⊓ M ≤ Mc)
    (hgen : ((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)) ⊔ I2 = I) :
    let I1 := (pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)
    let q := QuotientGroup.mk' (pPrimeCore 3 I)
    let A := (I1.subgroupOf I).map q
    let B := (I2.subgroupOf I).map q
    ∃ K : Subgroup I, K.IsCComponent ∧ K.Normal ∧
      generalizedFitting K = pCore 2 K ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
      ¬ K.map I.subtype ≤ I ⊓ M ∧ IsComponent (I ⧸ pPrimeCore 3 I) (K.map q) ∧
      (∃ e : ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) ≃*
          ((K.map q) ⧸ center (K.map q)),
        ∀ k : K, e (QuotientGroup.mk' (center (K ⧸ pCore 2 K))
          (QuotientGroup.mk' (pCore 2 K) k)) =
            QuotientGroup.mk' (center (K.map q)) (q.subgroupMap K k)) ∧
      ∃ S : Sylow 2 (I ⧸ pPrimeCore 3 I), A ⊓ B = (S : Subgroup _) ∧
        (FSource.SourceAlternative A B S ∨ FSource.SourceAlternative B A S) ∧
        ((∃ r : FSource.ProductRow S, K.map q = r.first ∧ ¬ ChapterC.IsChiZeroBlock K) ∨
          (K.map q = generalizedFitting (I ⧸ pPrimeCore 3 I) ∧
            IsQuasisimple (generalizedFitting (I ⧸ pPrimeCore 3 I)))) := by
  obtain ⟨K,hK,hn,hfit,himage⟩ := source_parabolic_characteristic_two_cComponent
    hG T hempty hM hunique hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal
    hcoreIndex hrank I I2 hI hSI2 hI2H hquot2 hout hgen
  let : K.Normal := hn
  have hq := source_parabolic_component_twoCore_quasisimple hG T hempty hM hunique
    hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal
    I I2 hI hSI2 hI2H hquot2 hout hgen K hK himage
  have ho := source_parabolic_component_outside hG T hempty hM hunique hmany hcard e
    hab H hH u hu hindex hmove hproduct hU3 hlocal hcoreIndex hrank
    I I2 hI hSI2 hI2H hquot2 hout hgen K hK himage
  obtain ⟨_,hc,S,hS,hsource⟩ := source_parabolic_quotient_f618 hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal hcoreIndex hrank
    I I2 hI hSI2 hI2H hquot2 hout hgen
  refine ⟨K,hK,hn,hfit,hq,ho,himage,f618_component_central_quotient K hK hq himage,S,hS,hsource,?_⟩
  rcases hsource.elim (f618_source_component_cases himage hc)
      (f618_source_component_cases himage hc) with ⟨r,hr⟩ | hq
  · exact Or.inl ⟨r,hr,f618_product_excludes_chiZero r K hK himage (MulEquiv.subgroupCongr hr)⟩
  · exact Or.inr hq

end CFSG.Quasithin.Chapter14.Section06
