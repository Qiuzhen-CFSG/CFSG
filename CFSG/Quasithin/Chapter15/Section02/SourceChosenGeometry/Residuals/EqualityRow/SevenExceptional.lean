module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EqualityRow.SevenGeometry
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EqualityRow.Alternating
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EqualityRow.NonlinearTripleSix
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.ExceptionalSeven

/-!
# The exceptional four-dimensional A₇ action on the original plane

Inner radical action puts the full central preimage into M intersect I.
The rank-two residual excludes its cubic center, so the actual core-to-star
map is injective.  The original seed gives a nonzero vector fixed by K;
its elementary nine-group cannot inject into the A₇ stabilizer of order 168.
This excludes the actual moved-section action directly in the equality row.

Source: Aschbacher--Smith, proof of 15.2.23, printed pp.1116--1117,
refs/quasithin.pdf. The original U, QI and star markings are retained.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open Section01 ComponentCatalogue PlaneUniquenessPreceding PlaneUniquenessPreceding.LinearThree TerminalLinear
open ChapterD ChapterD.UniqueFactor
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}

/-- Inner radical action excludes a cubic center in the original full core quotient. -/
theorem ResidualInput.normalized_core_center_card_one_of_inner
    (r : ResidualInput hsource H B)
    (hI : PlaneEscapes Mc ⁅V,B⁆ I) (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (s : Normalized H M I X)
    (hi : ∀ x : (M ⊓ I).pCoreIn 2,
      pCoreNormalizerAction 2 X (inclusion s.radical_normalizes x) ∈
        MulAut.innerSubgroup (X ⧸ pCore 2 X)) :
    Nat.card (center (X ⧸ pCore 2 X)) = 1 := by
  let h := normalized_component_input (hsource := hsource) hI hcore s
  rcases coreQuotient_center_card_from_source h with hz | hz
  · exact hz
  let C := centralCorePreimage X
  let K := residual H
  have hCI : C ≤ I := (map_subtype_le _).trans s.component.1
  have hCM : C ≤ M :=
    (normalized_center_preimage_le_intersection_of_inner (hsource := hsource)
      hI hcore s hi).trans inf_le_left
  have hKC : K ≤ normalizer (C : Set G) := s.residual_normalizes.trans
    (normalizer_le_normalizer_characteristic_image X (centralPreimage (pCore 2 X)))
  have hc : 3 ∣ Nat.card C := by
    have hh := (centralPreimage (pCore 2 X)).card_map_dvd (QuotientGroup.mk' (pCore 2 X))
    rw [map_centralPreimage,hz] at hh
    simpa only [C,centralCorePreimage,card_map_of_injective X.subtype_injective] using hh
  have hd := r.residual_intersection_three_dvd hI hCI hKC hc
  have ht : IsPGroup 2 (K ⊓ C : Subgroup G) := by
    apply (isPGroup_pCoreIn 2 K).to_le
    rw [←r.residual_intersection_eq_core]
    exact inf_le_inf_left K hCM
  obtain ⟨k,hk⟩ := ht.exists_card_eq
  rw [hk] at hd
  exact ((by norm_num : ¬ (3 : ℕ) ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)).elim

/-- The actual exceptional action identifies the full core quotient with A₇. -/
theorem ResidualInput.normalized_exceptionalSeven_core_model
    (r : ResidualInput hsource H B)
    (hI : PlaneEscapes Mc ⁅V,B⁆ I) (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (selection : Normalized H M I X)
    (hCJ : starImage X ((M ⊓ I).pCoreIn 2) X ≤
      offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))
    (s : MovedSection
      ((starRepresentation X ((M ⊓ I).pCoreIn 2)).comp
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))).subtype)
      ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))))
    (hf : Function.Injective s.action)
    (e : ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
      (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = 4) :
    Function.Injective (coreToStar selection.radical_normalizes) ∧
      Nonempty ((X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 7)) := by
  let h := normalized_component_input (hsource := hsource) hI hcore selection
  have hz := r.normalized_core_center_card_one_of_inner hI hcore selection
    (fun r => alternatingSeven_four_normalizer_inner h hCJ s hf e hd r
      (selection.radical_normalizes r.property) (((M ⊓ I).pCoreIn 2).le_normalizer r.property))
  have hk : (coreToStar selection.radical_normalizes).ker = ⊥ := by
    apply bot_unique
    exact (coreToStar_ker_central_from_source h).trans_eq ((eq_bot_iff_card _).mpr hz)
  have hinj := (coreToStar selection.radical_normalizes).ker_eq_bot_iff.mp hk
  exact ⟨hinj,⟨(MulEquiv.ofBijective (coreToStar selection.radical_normalizes)
    ⟨hinj,coreToStar_surjective selection.radical_normalizes⟩).trans
      ((subgroupOfEquivOfLe hCJ).symm.trans e)⟩⟩

/-- The full exceptional A₇ moved-section branch is impossible in the equality row. -/
theorem ResidualInput.normalized_exceptionalSeven_false_of_eq
    (r : ResidualInput hsource H B)
    (heq : partnerSpan H Mc = residual H)
    (hI : PlaneEscapes Mc ⁅V,B⁆ I) (hfit : generalizedFitting I = pCore 2 I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (selection : Normalized H M I X)
    (hCJ : starImage X ((M ⊓ I).pCoreIn 2) X ≤
      offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))
    (s : MovedSection
      ((starRepresentation X ((M ⊓ I).pCoreIn 2)).comp
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))).subtype)
      ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))))
    (hf : Function.Injective s.action)
    (e : ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
      (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = 4) : False := by
  let R := (M ⊓ I).pCoreIn 2
  let J := X ⊔ R
  let Joff := offenderSubgroup (starRepresentation X R)
  let L := (starImage X R X).subgroupOf Joff
  let η : L ≃* starImage X R X := subgroupOfEquivOfLe hCJ
  let h := normalized_component_input (hsource := hsource) hI hcore selection
  let eA := η.symm.trans e
  let eC := alternatingStarCoreCenterEquiv h (by decide : 5 ≤ 7) eA
  have hzC : Nat.card (center (X ⧸ pCore 2 X)) ≤ 3 := by
    rcases coreQuotient_center_card_from_source h with hc | hc <;> omega
  have hn := alternating_component_normalized (hsource := hsource) hI selection.toSelected
    hzC (Or.inr rfl) eC
  have hout := r.alternating_component_not_le_partner_of_eq heq hI hcore selection (Or.inr rfl) eC
  have hK := r.alternating_star_residual_le_M1 hI hcore selection (Or.inr rfl) eA
  have hseed : ¬ U X ⁅V,B⁆ ⊓ ⁅V,B⁆ ≤ centralizer (X : Set G) := by
    intro hh
    apply hout
    have hX : X ≤ M1 X ⁅V,B⁆ := by
      rw [← EqualityRow.Linear.U_seed_centralizer r hI hfit selection.component.1 hn]
      exact le_inf le_rfl (le_centralizer_iff.mp hh)
    exact hX.trans ((EqualityRow.Linear.M1_le_partner_intersection r hI selection.component.1).trans inf_le_left)
  obtain ⟨u,hu,hnc⟩ := SetLike.not_le_iff_exists.mp hseed
  have hUJ : U X ⁅V,B⁆ ≤ J :=
    (EqualityRow.Linear.U_le_intersection_radical r hI hfit selection.component.1).trans le_sup_right
  have hm : (⟨u,hUJ hu.1⟩ : J) ∈ ⁅starV X R,X.subgroupOf J⁆ :=
    r.original_U_le_star_moved hI hfit selection.component.1 hn hout h hu.1
  let v : Additive (starV X R) :=
    Additive.ofMul ⟨⟨u,hUJ hu.1⟩,commutator_le_left _ _ hm⟩
  have hv : v ∈ s.space.toSubmodule := by
    let : IsElementaryAbelian 2 (⁅starV X R,X.subgroupOf J⁆ : Subgroup J) :=
      IsElementaryAbelian.of_injective (inclusion (commutator_le_left (starV X R) (X.subgroupOf J)))
        (inclusion_injective _)
    rw [s.space_eq]
    change v ∈ subspaceCommutator ((starRepresentation X R).comp Joff.subtype) ⊤ L
    rw [subspaceCommutator_comp_map, map_subgroupOf_eq_of_le hCJ]
    change v ∈ subspaceCommutator (starRepresentation X R) ⊤
      ((X.subgroupOf J).map (QuotientGroup.mk' (starKernel X R)))
    exact (NormalElementaryQuotient.movedEquiv (starV X R)
      (QuotientGroup.mk' (starKernel X R)) (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _) (X.subgroupOf J)
      (Additive.ofMul ⟨⟨u,hUJ hu.1⟩,hm⟩)).property
  let z : s.space.toSubmodule ⧸ s.central.toSubmodule := Submodule.Quotient.mk ⟨v,hv⟩
  have hz : z ≠ 0 := by
    intro he
    have hc : (⟨v,hv⟩ : s.space.toSubmodule) ∈ s.central.toSubmodule :=
      by
        change Submodule.Quotient.mk (⟨v,hv⟩ : s.space.toSubmodule) = 0 at he
        simpa only [Submodule.Quotient.mk_eq_zero] using he
    rw [s.central_eq] at hc
    apply hnc
    intro x hx
    have hh := congrArg (fun w : s.space.toSubmodule => ((w.val.toMul : J) : G))
      (hc (η.symm (toStarImage X R ⟨x,hx⟩)))
    change (((starRepresentation X R
      (QuotientGroup.mk' (starKernel X R) (⟨x,mem_sup_left hx⟩ : J)) v).toMul : J) : G) = u at hh
    rw [starRepresentation_apply] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  let K := residual H
  have hKX : K ≤ X := hK.trans inf_le_left
  let f : K →* alternatingGroup (Fin 7) := e.toMonoidHom.comp
    (η.symm.toMonoidHom.comp ((toStarImage X R).comp (inclusion hKX)))
  let σ := (s.action.comp L.subtype).comp e.symm.toMonoidHom
  have hσ : Function.Injective σ := hf.comp (Subtype.val_injective.comp e.symm.injective)
  have hfix (k : K) : σ (f k) z = z := by
    let l : L := η.symm (toStarImage X R (inclusion hKX k))
    change s.central.quotientRepresentation (L.subtype (e.symm (e l))) z = z
    apply (congrArg (fun y : L => s.central.quotientRepresentation (L.subtype y) z)
      (e.symm_apply_apply l)).trans
    change Submodule.Quotient.mk (s.space.toRepresentation
      (L.subtype l) ⟨v,hv⟩) = Submodule.Quotient.mk ⟨v,hv⟩
    congr 1
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    change (((starRepresentation X R
      (QuotientGroup.mk' (starKernel X R) (⟨k,mem_sup_left (hKX k.property)⟩ : J)) v).toMul : J) : G) = u
    rw [starRepresentation_apply]
    change (k : G) * u * (k : G)⁻¹ = u
    rw [← r.residual_centralizes_plane k.property u hu.2, mul_inv_cancel_right]
  have hi := (r.normalized_exceptionalSeven_core_model hI hcore selection hCJ s hf e hd).1
  have hker : IsPGroup 2 f.ker := by
    apply ((pCore_isPGroup (p := 2) (G := X)).comap_of_injective
      (inclusion hKX) (inclusion_injective hKX)).to_le
    intro k hk
    apply (QuotientGroup.eq_one_iff (N := pCore 2 X) (inclusion hKX k)).mp
    apply hi
    change coreToStar selection.radical_normalizes
      (QuotientGroup.mk' (pCore 2 X) (inclusion hKX k)) =
        coreToStar selection.radical_normalizes 1
    rw [map_one, coreToStar_mk]
    apply η.symm.injective
    apply e.injective
    change e (η.symm (toStarImage X R (inclusion hKX k))) = 1 at hk
    simpa only [map_one] using hk
  obtain ⟨A,hA,hcard⟩ := exists_elementaryAbelian_card_primeRank (G := K) (p := 3)
  let := hA
  have hdis := (IsElementaryAbelian.isPGroup 3 A).disjoint_of_coprime hker
    (by decide : Nat.Coprime 3 2)
  let fA := f.comp A.subtype
  have hfA : Function.Injective fA := by
    apply (injective_iff_map_eq_one fA).mpr
    intro a ha
    apply Subtype.ext
    exact mem_bot.mp (hdis.eq_bot.le ⟨a.property,ha⟩)
  let t : A →* BinaryAlternatingSevenControl.pointStabilizer σ z :=
    fA.codRestrict _ (fun a => (BinaryAlternatingSevenControl.mem_pointStabilizer σ z (fA a)).mpr (hfix a))
  have ht : Function.Injective t := fun a b hh => hfA (congrArg Subtype.val hh)
  have hdiv := Subgroup.card_dvd_of_injective t ht
  rw [hcard,r.residual_rank_two,BinaryAlternatingSevenControl.pointStabilizer_card σ hσ hd hz] at hdiv
  norm_num at hdiv


end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
