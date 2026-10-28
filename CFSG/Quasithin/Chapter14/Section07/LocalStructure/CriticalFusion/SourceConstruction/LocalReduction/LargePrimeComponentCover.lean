module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeEndpointEnlargement
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Equivalences
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Models.NaturalOdd.Outer
public import Theory.SpecificGroups.PSL3Two.PerfectCentralCover
public import Theory.SpecificGroups.PSL3Two.Automorphisms
public import Theory.GroupTheory.PCoreNormalizerAction
public import Theory.GroupTheory.PResidual.PrimeToTransport
public import Theory.GroupTheory.CComponent.ResidualImage
public import Theory.GroupTheory.CComponent.SimpleImageKernel

/-!
# The full component cover above the common eight-group

A component mapping onto Aut(C)=L₃(2) is normal in N_G(C), and its
literal action kernel is its solvable radical. Pass to its intrinsic O₂
quotient using the actual image in N_G(C)/O₂(N_G(C)). In the quasisimple
case cyclic odd Sylow transfer removes the central cover. In the
nonquasisimple case A.3.6 gives a natural SL₂(p) extension or the
nilpotent SL₂(5) alternative. The latter cannot surject onto a group of
order 168; the radical quotient and natural kernel orders force p=7.

For the full natural plane extension over F₇, restriction of automorphisms to its
characteristic elementary kernel has inner kernel and image in GL₂(7).
Both orders are prime to five. This proves the automorphism restriction
needed in the two-factor branch without erasing the E₄₉ attachment or
assuming that the extension splits. The other canonical dihedral factors
normalize the full central preimage of the selected displacement plane.
Their literal lifted five-residuals therefore commute with the selected
component modulo its original two-core. LargePrimeComponentCoverSource
applies these results to the original selected witness. The simultaneous cubic branch and
subsequent ambient five-core exclusions remain open.
Source: Aschbacher–Smith A.3.6, 1.2.1(4), and 14.7.6, printed
pp.43–45,504,1044–1045, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin CFSG.Quasithin.Chapter1.Section02
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
universe u

private theorem central_fitting_quasisimple {E : Type u} [Group E] [Finite E]
    {B : Subgroup E} (hB : B.IsCComponent)
    (hf : fittingSubgroup B ≤ center B) : IsQuasisimple B := by
  have hr : solvableRadical B = center B := le_antisymm
    (solvableRadical_le_center_of_fitting_le_center hf)
    (le_solvableRadical (center B) inferInstance
      (Group.isSolvable_of_comm fun a b => Subtype.ext (mem_center_iff.mp a.property b).symm))
  let := hB.perfect
  let := hB.isSimpleGroup_quotient_solvableRadical
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hr).symm.isSimpleGroup⟩

private theorem natural_seven_of_simple_image {B : Type u} [Group B] [Finite B]
    (hn : A36Natural B) (hc : A36Common B)
    (he : Nat.card (B ⧸ solvableRadical B) = 168) :
    LocalModels.NaturalSL2Action B (generalizedFitting B) 7 := by
  obtain ⟨p,hp,hp3,ha⟩ := hn.2
  have hFcard : Nat.card (fittingSubgroup B) = p ^ 2 := by
    rw [←hn.1]
    exact (Chapter1.RadicalStructure.natural_elementary ha).2
  have hindex : (fittingSubgroup B).relIndex (solvableRadical B) = 2 := by
    rcases hc.2.2.1 with h | h
    · exact h.2.2
    · rcases h.2.2 with h | h <;> rw [hFcard] at h <;> nlinarith
  have horder : Nat.card (B ⧸ fittingSubgroup B) = 336 := by
    have hm := relIndex_mul_index
      (le_solvableRadical (fittingSubgroup B) inferInstance inferInstance)
    rw [hindex,index_eq_card,index_eq_card,he] at hm
    exact hm.symm
  obtain ⟨F,_,_,hcard,v,e,hact⟩ := ha
  have ho : p * (p ^ 2 - 1) = 336 := by
    have hh := Nat.card_congr e.toEquiv
    rw [hn.1,horder,Atlas.card_sl_two,hcard] at hh
    exact hh.symm
  have hp7 : p = 7 := by
    have hlow : 7 ≤ p := by
      by_contra hh
      have hp6 : p ≤ 6 := by omega
      interval_cases p <;> norm_num at ho
    have hupp : p ≤ 7 := by
      by_contra hh
      have hp8 : 8 ≤ p := by omega
      have hs64 : 64 ≤ p ^ 2 := by nlinarith
      have hs63 : 63 ≤ p ^ 2 - 1 := by omega
      have hmul := Nat.mul_le_mul hp8 hs63
      omega
    omega
  rw [← hp7]
  exact ⟨F,inferInstance,inferInstance,hcard,v,e,hact⟩

/-- A C-component with simple image SL₃(2) has either that full quotient
or the natural plane extension over F₇; the action kernel is not discarded. -/
theorem common_eight_component_image_alternatives
    {E : Type u} [Group E] [Finite E] {κ : GroupClass.{u}}
    (hE : IsSQTK κ E) (hO : pCore 2 E = ⊥)
    (B : Subgroup E) (hB : B.IsCComponent)
    (f : B →* Matrix.PSL3Two.SL) (hf : Function.Surjective f) :
    Nonempty (B ≃* Matrix.PSL3Two.SL) ∨
      (generalizedFitting B = fittingSubgroup B ∧
        LocalModels.NaturalSL2Action B (generalizedFitting B) 7) := by
  let : IsSimpleGroup Matrix.PSL3Two.PSL :=
    Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)
  let : IsSimpleGroup Matrix.PSL3Two.SL := Matrix.PSL3Two.equiv.isSimpleGroup
  have htop : (⊤ : Subgroup B).IsCComponent := by
    simpa only [subgroupOf_self] using hB.subgroupOf le_rfl
  have hk := kernel_eq_solvableRadical_of_top_isCComponent htop f hf
  have he : Nat.card (B ⧸ solvableRadical B) = 168 := by
    rw [←hk,Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv,
      Matrix.PSL3Two.card_SL]
  by_cases hfit : fittingSubgroup B ≤ center B
  · left
    let : IsQuasisimple B := central_fitting_quasisimple hB hfit
    have hker : f.ker ≤ center B := by
      rw [hk]
      exact solvableRadical_le_center_of_fitting_le_center hfit
    have hBcore : pCore 2 B = ⊥ := by
      rw [pCore_subnormal_eq_comap 2 hB.subnormal,hO]
      exact B.ker_subtype
    let cov : PerfectCentralCovering.Cover B Matrix.PSL3Two.SL :=
      { toMonoidHom := f, surjective := hf, ker_le_center := hker, isPerfect := inferInstance }
    exact ⟨Matrix.PSL3Two.centralCoverEquiv cov hBcore⟩
  · obtain ⟨hs,hc⟩ := ChapterA.Section03.NoncentralFitting.structure_of_noncentral hE hO hB hfit
    rcases hs with hn | hn
    · exact Or.inr ⟨hn.1,natural_seven_of_simple_image hn hc he⟩
    · exfalso
      have hle : generalizedFitting B ≤ f.ker := by
        rw [hn.1,hk]
        exact le_solvableRadical _ inferInstance inferInstance
      let g := QuotientGroup.lift (generalizedFitting B) f hle
      have hg : Function.Surjective g := QuotientGroup.lift_surjective_of_surjective _ _ hf _
      have hd := card_dvd_of_surjective g hg
      obtain ⟨F,_,_,hcard,⟨e⟩⟩ := hn.2.2.1
      rw [Matrix.PSL3Two.card_SL,Nat.card_congr e.toEquiv,Atlas.card_sl_two,hcard] at hd
      norm_num at hd

/-- The automorphism group of the full natural plane extension over F₇ has
order prime to five, including its pointwise-kernel automorphisms. -/
theorem natural_seven_automorphism_five_free
    {B : Type u} [Group B] [Finite B] [Group.IsPerfect B]
    (hfit : generalizedFitting B = fittingSubgroup B)
    (ha : LocalModels.NaturalSL2Action B (generalizedFitting B) 7) :
    ¬ 5 ∣ Nat.card (MulAut B) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hn : A36Natural B := ⟨hfit,7,by decide,by decide,ha⟩
  have haF : LocalModels.NaturalSL2Action B (fittingSubgroup B) 7 := by
    simpa only [hfit] using ha
  obtain ⟨hel,hcard⟩ := Chapter1.RadicalStructure.natural_elementary haF
  let := hel
  have hBcard : Nat.card B = 49 * 336 := by
    obtain ⟨F,_,_,hF,v,e,hact⟩ := haF
    have hm := (fittingSubgroup B).card_mul_index
    rw [hcard,index_eq_card,Nat.card_congr e.toEquiv,Atlas.card_sl_two,hF] at hm
    exact hm.symm
  let r := MulAut.characteristic (fittingSubgroup B)
  have hk : r.ker ≤ MulAut.innerSubgroup B :=
    Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Models.NaturalOdd.restriction_kernel hn
  have hinner : Nat.card (MulAut.innerSubgroup B) ∣ Nat.card B :=
    card_dvd_of_surjective (MulAut.conj : B →* MulAut B).rangeRestrict
      (MulAut.conj : B →* MulAut B).rangeRestrict_surjective
  have hker : ¬ 5 ∣ Nat.card r.ker := by
    intro hd
    have hdB := hd.trans ((card_dvd_of_le hk).trans hinner)
    rw [hBcard] at hdB
    norm_num at hdB
  let e := IsElementaryAbelian.mulAutLinearEquivOfCard (fittingSubgroup B) hcard
  have hAut : Nat.card (MulAut (fittingSubgroup B)) = 2016 := by
    rw [Nat.card_congr e.toEquiv]
    simpa [Fin.prod_univ_two] using (Matrix.card_GL_field (𝔽 := ZMod 7) 2)
  have hrange : ¬ 5 ∣ Nat.card r.range := by
    intro hd
    have hh := hd.trans (card_subgroup_dvd_card r.range)
    rw [hAut] at hh
    norm_num at hh
  have hm := r.ker.index_mul_card
  rw [index_ker] at hm
  intro hd
  rw [←hm] at hd
  exact (Nat.prime_five.dvd_mul.mp hd).elim hrange hker

/-- Classify the intrinsic two-core quotient of the actual selected component,
retaining its normality, centralizer kernel and full cover in both alternatives. -/
theorem common_eight_component_full_cover
    {G : Type u} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (C : Subgroup G) [IsElementaryAbelian 2 C] (hc : Nat.card C = 8)
    (D : Subgroup (normalizer (C : Set G))) (hD : D.IsCComponent)
    (hm : D.map C.normalizerMonoidHom = ⊤) :
    D.Normal ∧
      (C.normalizerMonoidHom.comp D.subtype).ker = solvableRadical D ∧
      (Nonempty ((D ⧸ pCore 2 D) ≃* Matrix.PSL3Two.PSL) ∨
        (generalizedFitting (D ⧸ pCore 2 D) = fittingSubgroup (D ⧸ pCore 2 D) ∧
          LocalModels.NaturalSL2Action (D ⧸ pCore 2 D)
            (generalizedFitting (D ⧸ pCore 2 D)) 7)) ∧
      ¬ 5 ∣ Nat.card (MulAut (D ⧸ pCore 2 D)) := by
  let N := normalizer (C : Set G)
  let f := C.normalizerMonoidHom.comp D.subtype
  obtain ⟨a⟩ := MulAut.elementaryEight_equiv_PSL3 hc
  let : IsSimpleGroup Matrix.PSL3Two.PSL :=
    Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)
  let : Group.IsPerfect Matrix.PSL3Two.PSL := Atlas.psl_perfect 3 (by decide)
  let : IsSimpleGroup (MulAut C) := a.isSimpleGroup
  let : Group.IsPerfect (MulAut C) :=
    Group.IsPerfect.ofSurjective (f := a.symm.toMonoidHom) a.symm.surjective
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨d,hd,rfl⟩ := hm.ge (mem_top x)
    exact ⟨⟨d,hd⟩,rfl⟩
  have hnormal : D.Normal := hD.normal_of_normal_nonsolvable_image C.normalizerMonoidHom
    (by rw [hm]; infer_instance) (by
      rw [hm]
      intro hs
      let := hs
      have hsol : Group.IsSolvable (MulAut C) :=
        Group.isSolvable_of_surjective
          (f := (topEquiv : (⊤ : Subgroup (MulAut C)) ≃* MulAut C).toMonoidHom)
          topEquiv.surjective
      exact Group.IsPerfect.not_isSolvable (MulAut C) hsol)
  have htopD : (⊤ : Subgroup D).IsCComponent := by
    simpa only [subgroupOf_self] using hD.subgroupOf le_rfl
  have hk := kernel_eq_solvableRadical_of_top_isCComponent htopD f hf
  let g := (a.trans Matrix.PSL3Two.equiv.symm).toMonoidHom.comp f
  have hg : Function.Surjective g :=
    (a.trans Matrix.PSL3Two.equiv.symm).surjective.comp hf
  have hcoreker : pCore 2 D ≤ g.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _
      (a.trans Matrix.PSL3Two.equiv.symm).injective,hk]
    let : Group.IsNilpotent (pCore 2 D) := pCore_isPGroup.isNilpotent
    exact le_solvableRadical _ inferInstance inferInstance
  let Q := D ⧸ pCore 2 D
  let gq : Q →* Matrix.PSL3Two.SL := QuotientGroup.lift _ g hcoreker
  have hgq : Function.Surjective gq := QuotientGroup.lift_surjective_of_surjective _ _ hg _
  have htopQ : (⊤ : Subgroup Q).IsCComponent := by
    let : Group.IsNilpotent (pCore 2 D) := pCore_isPGroup.isNilpotent
    simpa only [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] using
      htopD.map_quotient (pCore 2 D)
  let e := cComponentTwoCoreQuotientEquiv hD
  have hN : N ∈ Chapter1.H G := by
    have hCN : C ≤ N.pCoreIn 2 := le_pCoreIn_of_normalizes
      (IsElementaryAbelian.isPGroup 2 C) C.le_normalizer le_rfl
    intro he
    have hb : C = ⊥ := le_bot_iff.mp (he ▸ hCN)
    rw [hb,card_bot] at hc
    omega
  have hQ : IsSQTK KnownSimple.IsKnownSimple Q := (IsSQTK.equiv e).mpr
    ((Chapter1.Section02.uniqueness_local_quotient_sqtk hG hN).subgroup _)
  have hclass := common_eight_component_image_alternatives hQ
    (pCore_quotient_pCore_eq_bot 2) ⊤ htopQ
      (gq.comp (topEquiv : (⊤ : Subgroup Q) ≃* Q).toMonoidHom)
      (hgq.comp topEquiv.surjective)
  let : Group.IsPerfect D := hD.perfect
  let : Group.IsPerfect Q :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (pCore 2 D))
  refine ⟨hnormal,hk,?_⟩
  rcases hclass with hs | hnat
  · obtain ⟨eqv⟩ := hs
    let eqvQ : Q ≃* Matrix.PSL3Two.PSL := topEquiv.symm.trans (eqv.trans Matrix.PSL3Two.equiv)
    refine ⟨Or.inl ⟨eqvQ⟩,?_⟩
    rw [Nat.card_congr (MulAut.congr eqvQ).toEquiv,Matrix.PSL3Two.Automorphisms.card_aut]
    decide
  · have hn : A36Natural Q :=
      (show A36Natural (⊤ : Subgroup Q) from ⟨hnat.1,7,by decide,by decide,hnat.2⟩).of_mulEquiv topEquiv
    have hfit : generalizedFitting Q = fittingSubgroup Q := hn.1
    have ha7 : LocalModels.NaturalSL2Action Q (generalizedFitting Q) 7 := by
      have hgfit := Theory.GroupTheory.map_generalizedFitting_equiv (topEquiv : (⊤ : Subgroup Q) ≃* Q)
      let b : generalizedFitting (⊤ : Subgroup Q) ≃* generalizedFitting Q :=
        (topEquiv.subgroupMap _).trans (MulEquiv.subgroupCongr hgfit)
      let q := QuotientGroup.congr _ _ topEquiv hgfit
      obtain ⟨F,hF,hfin,hcard,v,r,hact⟩ := hnat.2
      refine ⟨F,hF,hfin,hcard,b.symm.trans v,q.symm.trans r,?_⟩
      intro x y
      change v (b.symm _) = _
      have he : b.symm ⟨x*y*x⁻¹,(inferInstance : (generalizedFitting Q).Normal).conj_mem y y.property x⟩ =
          ⟨topEquiv.symm x * (b.symm y : (⊤ : Subgroup Q)) * (topEquiv.symm x)⁻¹,
            (inferInstance : (generalizedFitting (⊤ : Subgroup Q)).Normal).conj_mem
              (b.symm y) (b.symm y).property (topEquiv.symm x)⟩ := by
        apply Subtype.ext
        rfl
      rw [he,hact]
      rfl
    exact ⟨Or.inr ⟨hfit,ha7⟩,natural_seven_automorphism_five_free hfit ha7⟩

open Chapter12.Section08 CriticalFusion.Source Representation Representation.BinaryOffender
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter14.Section06.OddNormalizer ChapterD
open scoped IsMulCommutative

/-- Every other canonical dihedral factor normalizes the full central
preimage of the selected actor's displacement plane. -/
theorem local_other_factor_normalizes_common
    {G : Type u} [Group G] [Finite G] {H U Z : Subgroup G}
    [IsElementaryAbelian 2 U] (a : LocalQuotientAction H U Z) :
    let := BinaryGroupAction.action a.representation
    ∀ (f : CanonicalFiveDihedralFamily (G := HStar H)
        (V := Multiplicative (Additive (U ⧸ Z.subgroupOf U))))
      (i j : smallSupportFactors (HStar H)
        (Multiplicative (Additive (U ⧸ Z.subgroupOf U))) 2)
      (A : Subgroup (HStar H)) (C : Subgroup G),
      i ≠ j → A ≤ f.factor i →
      C = supportPreimage a (subspaceCommutator a.representation ⊤ A) →
      ((f.factor j).comap (QuotientGroup.mk' (pCore 2 H))).map H.subtype ≤
        normalizer (C : Set G) := by
  intro _
  let := BinaryGroupAction.action a.representation
  intro f i j A C hij hAi hC
  rw [hC]
  apply supportPreimage_normalized a _ _ (map_subtype_le _)
  apply subspaceCommutator_invariant_normalizer a.representation
    (le_subspaceStabilizer _ ⊤ (by intros; trivial))
  apply le_trans _ (Subgroup.centralizer_le_normalizer (A : Set (HStar H)))
  rintro _ ⟨g,hg,rfl⟩ x hx
  obtain ⟨y,hy,hyg⟩ := hg
  have he : y = g := Subtype.ext hyg
  subst y
  exact (f.commute hij x _ (hAi hx) hy).eq

private theorem five_residual_commutator_le_core
    {G : Type u} [Group G] [Finite G] (D B : Subgroup G) [D.Normal]
    (hfree : ¬ 5 ∣ Nat.card (MulAut (D ⧸ pCore 2 D))) :
    ⁅D,(primeToResidual 5 B).map B.subtype⁆ ≤ D.pCoreIn 2 := by
  let hBN : B ≤ normalizer (D : Set G) := le_normalizer_of_normal
  let a := (pCoreNormalizerAction 2 D).comp (inclusion hBN)
  have hk := primeToResidual_le_ker a (Nat.prime_five.coprime_iff_not_dvd.mpr hfree)
  apply commutator_le_core_of_pCoreNormalizerAction_eq_one 2 D _ le_normalizer_of_normal
  rintro ⟨_,b,hb,rfl⟩
  exact hk hb

/-- The full cover and its automorphism bound give the source commutator
containment for the actual lifted second-factor five-residual. -/
theorem local_other_factor_component_commutator
    {G : Type u} [Group G] [Finite G] {H U Z : Subgroup G}
    [IsElementaryAbelian 2 U] (a : LocalQuotientAction H U Z) :
    let := BinaryGroupAction.action a.representation
    ∀ (f : CanonicalFiveDihedralFamily (G := HStar H)
        (V := Multiplicative (Additive (U ⧸ Z.subgroupOf U))))
      (i j : smallSupportFactors (HStar H)
        (Multiplicative (Additive (U ⧸ Z.subgroupOf U))) 2)
      (A : Subgroup (HStar H)) (C : Subgroup G),
      i ≠ j → A ≤ f.factor i →
      C = supportPreimage a (subspaceCommutator a.representation ⊤ A) →
      ∀ (_ : IsElementaryAbelian 2 C), Nat.card C = 8 →
      IsSimpleQTKE KnownSimple.IsKnownSimple G →
      ∀ (D : Subgroup (normalizer (C : Set G))), D.IsCComponent →
        D.map C.normalizerMonoidHom = ⊤ →
        let K2 := ((f.factor j).comap (QuotientGroup.mk' (pCore 2 H))).map H.subtype
        K2 ≤ normalizer (C : Set G) ∧
          ⁅D.map (normalizer (C : Set G)).subtype,(primeToResidual 5 K2).map K2.subtype⁆ ≤
            (D.map (normalizer (C : Set G)).subtype).pCoreIn 2 := by
  intro _
  let := BinaryGroupAction.action a.representation
  intro f i j A C hij hAi hC hCE hc hG D hD hm
  let := hCE
  let K2 := ((f.factor j).comap (QuotientGroup.mk' (pCore 2 H))).map H.subtype
  let N := normalizer (C : Set G)
  have hK2N : K2 ≤ N := local_other_factor_normalizes_common a f i j A C hij hAi hC
  obtain ⟨hn,_,_,hfree⟩ := common_eight_component_full_cover hG C hc D hD hm
  let := hn
  have hh := map_mono (f := N.subtype)
    (five_residual_commutator_le_core D (K2.subgroupOf N) hfree)
  rw [map_commutator,map_embedded_primeToResidual_of_hom,
    map_subgroupOf_eq_of_le hK2N,
    map_pCoreIn_of_injective 2 D N.subtype N.subtype_injective] at hh
  exact ⟨hK2N,hh⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
