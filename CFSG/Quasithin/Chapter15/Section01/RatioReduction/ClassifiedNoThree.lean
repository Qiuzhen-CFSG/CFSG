module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.ClassifiedFactors
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.NoThreeSupport
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.NoncyclicCoreNormal
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.FactorCarrier
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.SupportTransport

/-!
# The classified three-plane factor is excluded in the original local action

The original SQTK cover bounds prime rank before passage to the action image.
A factor with noncyclic odd core is therefore ambient normal: a conjugate
moving involution in a different factor would force its original core to be
cyclic. The corresponding support is an actual M-normal elementary subgroup.

The literal factor embedding then induces an injective map into M/C_M(U_i),
and the equivariant coordinates carry its marked support family to that
quotient action. The completed p.1085 no-invariant-span argument applies with
all normality and quotient-identification premises discharged.

The last theorem constructs the marked support family from the existing D.2.22
classification and excludes dimension six for every noncyclic factor of the
actual source decomposition. No ambient factor normality is assumed.

Source: Aschbacher--Smith 15.1.2, printed pp.1084--1085, using D.2.17(6).
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
open ChapterD ChapterD.RatioDecomposition ChapterD.UniqueFactor ChapterD.FittingConfigurations
variable {G : Type*} [Group G] [Finite G]

theorem source_localAction_factor_actor_normal
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let ρ := imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
    ∀ (U : Submodule (ZMod 2) (Additive (localModule T M)))
      (c : FactorData ρ (Jhat ρ) U) (d : Decomposition c.representation), d.FittingFull →
    ∀ (p : ℕ) [Fact p.Prime], Odd p → ∀ (i : d.Index),
      ¬ IsCyclic (pCore p (d.factor i).Carrier) →
    ∀ (t : (d.factor i).Carrier), orderOf t = 2 →
      t ∉ centralizer (pCore p (d.factor i).Carrier : Set _) →
      (c.ambientFactor d i).actor.Normal := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let ρ := imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
  let f := actionHom M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
  let : (Jhat ρ).Normal := Jhat_normal ρ
  dsimp only
  intro U c d hd p hpFact hp i hncyc t ht hmove
  exact c.factor_actor_normal_of_noncyclic_core d hp f.rangeRestrict f.rangeRestrict_surjective
    ((Chapter3.sqtk_of_mem_H hG (Chapter1.mem_H_of_isTwoLocal hM.1.1.1)).stronglyQuasithin
      p hpFact.out hp)
    (source_localAction_factor_starred_sylow hG T hempty hM hmany hJ U c d hd)
    i hncyc t ht hmove

theorem source_localAction_no_three_support_factor
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let ρ := imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
    ∀ (U : Submodule (ZMod 2) (Additive (localModule T M)))
      (c : FactorData ρ (Jhat ρ) U) (d : Decomposition c.representation), d.FittingFull →
    ∀ (i : d.Index) (A : Subgroup (d.factor i).Carrier),
      Reduced (d.factor i).action (pCore 3 (d.factor i).Carrier) A 3 →
      SupportFactors (d.factor i).action (pCore 3 (d.factor i).Carrier) 3 → False := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
  let q := (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict
  have hq : Function.Surjective q := MonoidHom.rangeRestrict_surjective _
  have hact (m : M) (v : Additive V) :
      ((ρ (q m) v).toMul : G) = (m:G) * v.toMul * (m:G)⁻¹ := rfl
  dsimp only
  intro U c d hd i A h ds
  let : IsElementaryAbelian 3 (pCore 3 (d.factor i).Carrier) := h.elementary
  have hncyc : ¬ IsCyclic (pCore 3 (d.factor i).Carrier) := by
    intro hc
    let := hc
    have hh := IsElementaryAbelian.exponent_dvd_p 3 (pCore 3 (d.factor i).Carrier)
    rw [IsCyclic.exponent_eq_card,h.card_core] at hh
    norm_num at hh
  let : IsElementaryAbelian 2 A := h.starred.1.2.1.2
  let : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).mpr h.starred.1.2.1.1
  obtain ⟨a,ha⟩ := exists_ne (1 : A)
  have ha1 : (a : (d.factor i).Carrier) ≠ 1 := fun he => ha (Subtype.ext he)
  have ha2 : orderOf (a : (d.factor i).Carrier) = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := 2)
      (a : (d.factor i).Carrier) a.property) ha1
  have ham : (a : (d.factor i).Carrier) ∉ centralizer (pCore 3 (d.factor i).Carrier : Set _) := by
    intro hh
    have hm : (a : (d.factor i).Carrier) ∈ A ⊓ centralizer (pCore 3 (d.factor i).Carrier : Set _) :=
      ⟨a.property,hh⟩
    rw [h.actor_faithful] at hm
    exact ha1 hm
  let F := c.ambientFactor d i
  let : IsElementaryAbelian 3 (pCore 3 F.Carrier) := h.elementary
  let : F.actor.Normal := source_localAction_factor_actor_normal hG T hempty hM hmany hJ
    U c d hd 3 (by decide) i hncyc a ha2 ham
  let hVM := localModule_le T hM.1.2
  let W := F.internalSubgroup hVM ρ
  let : W.Normal := F.internalSubgroup_normal hVM ρ q hact
  let r := F.internalProjection hVM ρ q hq hact
  let j := r.comp F.embedding.groupMap
  have hj : Function.Injective j := F.internalProjection_factor_injective hVM ρ q hq hact
  let P := (pCore 3 F.Carrier).map j
  let : P.Normal := F.internalProjection_core_normal hVM ρ q hq hact 3
  let : IsElementaryAbelian 3 P := IsElementaryAbelian.map j
  let σ := NormalElementaryQuotient.representation W (QuotientGroup.mk' _)
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  let e := F.internalSpaceEquiv hVM ρ
  have he (g : F.Carrier) (v : F.Space) : e (F.action g v) = σ (j g) (e v) :=
    F.internalProjection_intertwines hVM ρ q hq hact g v
  let ds' : SupportFactors σ P 3 := ds.map F.action σ j hj e he
  exact source_no_three_support_component hG T hempty hM hJ hu hne W P ds'
theorem source_localAction_factor_noncyclic_finrank_ne_six
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let ρ := imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
    ∀ (U : Submodule (ZMod 2) (Additive (localModule T M)))
      (c : FactorData ρ (Jhat ρ) U) (d : Decomposition c.representation), d.FittingFull →
    ∀ (i : d.Index) (A : Subgroup (d.factor i).Carrier),
      A ∈ QhatStar (d.factor i).action → 1 < rank A →
      Module.finrank (ZMod 2) (d.factor i).Space ≠ 6 := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let D := internalActionImage M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
  let ρ := imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
  let f := actionHom M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
  let := source_localAction_isSolvable hG T hempty hM
  let : (Jhat ρ).Normal := Jhat_normal ρ
  dsimp only
  intro U c d hd i A hA hArank hdim
  let F := d.factor i
  let j : F.Carrier →* D := (Jhat ρ).subtype.comp F.embedding.groupMap
  let : Group.IsSolvable F.Carrier := Group.isSolvable_of_isSolvable_injective
    (f := j) ((Jhat ρ).subtype_injective.comp F.embedding.group_injective)
  obtain ⟨B,r,hB,hr⟩ := c.factor_cover d
    (Chapter3.sqtk_of_mem_H hG (Chapter1.mem_H_of_isTwoLocal hM.1.1.1))
    f.rangeRestrict f.rangeRestrict_surjective i
  obtain ⟨s,h,ds,_,hsdim,_,_⟩ := SourceReduction.source_noncyclic_global_configurations F.action
    hB r hr F.faithful hA hArank (generalizedFitting_eq_fitting_of_solvable F.Carrier)
    (c.factor_twoCore d (source_localAction_twoCore hG T hM) i) (hd i) F.generated
  have hdimF : Module.finrank (ZMod 2) F.Space = 6 := hdim
  have hs : s = 3 := by omega
  subst s
  exact source_localAction_no_three_support_factor hG T hempty hM hmany hJ hu hne U c d hd i A h ds

end CFSG.Quasithin.Chapter15.Section01
