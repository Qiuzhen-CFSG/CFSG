module
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.Residual
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import CFSG.Quasithin.ChapterA.Section04.Intersection
public import Theory.GroupTheory.Fitting.OutsideComponent
public import Theory.GroupTheory.CoprimeCentralizerDirectProduct
public import Theory.GroupTheory.Commutator.CentralizingComplement
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Mathlib.GroupTheory.SchurZassenhaus

/-!
# Generalized-Fitting centrality in the original rank-two branch

The Fitting preimage modulo the two-core has an odd complement. Its displacement
on the omega-center of the two-core is a normal elementary two-subgroup. If
nontrivial, it contains a central involution of the original Sylow subgroup.
The local group fixes that involution, contradicting the disjoint fixed and
displacement subgroups for the odd complement. Empty faithful local components
supply the remaining component centrality through the existing residual theorem.

The proof only needs that the local group centralizes the whole Sylow
omega-center; the order-two hypothesis used in the printed proof is unnecessary.
Both the intrinsic preimage and its literal ambient image are retained.

Source: Aschbacher–Smith, 14.6.1(5), printed p.1020 of refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section06
open Chapter15.Section03
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem fittingPreimage_centralizes_omegaCore
    (T : Sylow 2 G) {H : Subgroup G} (hTH : (T : Subgroup G) ≤ H)
    (hHZ : H ≤ centralizer (centralInvolutions T : Set G)) :
    twoFittingCore H ≤ centralizer (omegaOneCenterAmbient (pCore 2 H) : Set H) := by
  let R := pCore 2 H
  let W := omegaOneCenterAmbient R
  let F := twoFittingCore H
  let S := T.subtype hTH
  let : W.Normal := by
    let : (omega₁ (center R) (p := 2)).Characteristic := omega₁_characteristic _
    unfold W omegaOneCenterAmbient
    infer_instance
  let : IsElementaryAbelian 2 W := omegaOneCenterAmbient_elementaryAbelian R
  have hRW : R ≤ centralizer (W : Set H) := by
    apply le_centralizer_iff.mp
    intro w hw
    exact ((mem_omegaOneCenterAmbient_iff R w).mp hw).2.2
  have hRF : R ≤ F := twoCore_le_twoFittingCore
  let K := R.subgroupOf F
  have hKp : IsPGroup 2 K := pCore_isPGroup.comap_subtype
  have hKindex : K.index = Nat.card (fittingSubgroup (H ⧸ R)) := by
    rw [index_eq_card, ← natCard_map_mk'_eq F R]
    rw [show F.map (QuotientGroup.mk' R) = fittingSubgroup (H ⧸ R) from
      map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective R) _]
  have hFitcop : Nat.Coprime 2 (Nat.card (fittingSubgroup (H ⧸ R))) :=
    (pPrimeCore_coprime_card (p := 2) (G := H ⧸ R)).of_dvd_right
      (card_dvd_of_le (fitting_le_pPrimeCore_of_pCore_eq_bot 2
        (pCore_quotient_pCore_eq_bot 2)))
  have hKcop : Nat.Coprime (Nat.card K) K.index := by
    obtain ⟨n, hn⟩ := hKp.exists_card_eq
    rw [hn,hKindex]
    exact hFitcop.pow_left n
  obtain ⟨A₀,hA₀⟩ := exists_right_complement'_of_coprime hKcop
  let A := A₀.map F.subtype
  have hAodd : Nat.Coprime 2 (Nat.card A) := by
    rw [card_map_of_injective F.subtype_injective, ← hA₀.symm.index_eq_card, hKindex]
    exact hFitcop
  have hgen : R ⊔ A = F := by
    have hh := congrArg (fun B : Subgroup F => B.map F.subtype) hA₀.sup_eq_top
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hRF,
      ← MonoidHom.range_eq_map, range_subtype] at hh
    exact hh
  have hAcomm : ⁅W,A⁆ = ⁅W,F⁆ :=
    commutator_eq_of_centralizing_sup hgen hRW le_normalizer_of_normal
  have hcop : Nat.Coprime (Nat.card A) (Nat.card W) := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 W).exists_card_eq
    rw [hn]
    exact hAodd.symm.pow_right n
  have hd : Disjoint ⁅W,F⁆ (W ⊓ centralizer (A : Set H)) := by
    rw [← hAcomm]
    exact commutator_disjoint_centralizer_of_coprime W A le_normalizer_of_normal hcop
  have hD : ⁅W,F⁆ = ⊥ := by
    by_contra hne
    let D := ⁅W,F⁆
    have hDW : D ≤ W := commutator_le_left _ _
    have hDS : D ≤ (S : Subgroup H) :=
      hDW.trans ((IsElementaryAbelian.isPGroup 2 W).le_sylow_of_normal S)
    let : Nontrivial D := (nontrivial_iff_ne_bot D).mpr hne
    let : Nontrivial (D.subgroupOf (S : Subgroup H)) :=
      (subgroupOfEquivOfLe hDS).toEquiv.nontrivial
    let : Fact (IsPGroup 2 S) := ⟨S.isPGroup'⟩
    obtain ⟨x,hxne,hxc⟩ :=
      exists_nontrivial_center_mem_normal (D.subgroupOf (S : Subgroup H)) (p := 2)
    have hxW : ((x : S) : H) ∈ W := hDW x.property
    have hxZ : (((x : S) : H) : G) ∈ centralInvolutions T := by
      apply (mem_omegaOneCenterAmbient_iff _ _).mpr
      refine ⟨(x : S).property, ?_, ?_⟩
      · exact congrArg H.subtype (elemPow_eq_one_of_isElementaryAbelian (p := 2) _ hxW)
      · intro t ht
        exact congrArg (fun s : S => ((s : H) : G))
          ((mem_center_iff.mp hxc) ⟨⟨t,hTH ht⟩,ht⟩)
    have hxA : ((x : S) : H) ∈ centralizer (A : Set H) := by
      intro a ha
      apply H.subtype_injective
      exact (hHZ a.property _ hxZ).symm
    have hxone : ((x : S) : H) = 1 :=
      mem_bot.mp (hd.eq_bot ▸ (show ((x : S) : H) ∈ ⁅W,F⁆ ⊓
        (W ⊓ centralizer (A : Set H)) from ⟨x.property,hxW,hxA⟩))
    exact hxne (Subtype.ext (Subtype.ext hxone))
  exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hD)

/-- Original 14.6.1(5), for the actual local group centralizing the Sylow omega-center. -/
theorem generalizedFittingPreimage_centralizes_omegaCore
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {H : Subgroup G} (hH : H ∈ Chapter1.HOver G (T : Set G))
    (hHZ : H ≤ centralizer (centralInvolutions T : Set G)) :
    (generalizedFitting (H ⧸ pCore 2 H)).comap (QuotientGroup.mk' (pCore 2 H)) ≤
      centralizer (omegaOneCenterAmbient (pCore 2 H) : Set H) := by
  have hf := fittingPreimage_centralizes_omegaCore T hH.2 hHZ
  have hr := InitialSource.residual_le_centralizer_omegaCore
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) hG T hempty hH
  by_contra hout
  obtain ⟨K,hK,_,hKC⟩ := exists_cComponent_outside_of_fitting_preimage_le _ hf hout
  let := hK.perfect
  exact hKC ((le_solvableResidual_of_isPerfect K).trans hr)

/-- The same source centralization in the ambient group, for the original
member of `H(T,M)` and the original generalized-Fitting preimage. -/
theorem source_generalizedFittingPreimage_centralizes_omegaCore
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {H M : Subgroup G} (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (hHZ : H ≤ centralizer (centralInvolutions T : Set G)) :
    ChapterA.Section04.twoGeneralizedFittingPreimage H ≤
      centralizer (omegaOneCenterAmbient (H.pCoreIn 2) : Set G) := by
  have hc := generalizedFittingPreimage_centralizes_omegaCore hG T hempty hH.1 hHZ
  rintro x ⟨y,hy,rfl⟩ w hw
  change w ∈ omegaOneCenterAmbient ((pCore 2 H).map H.subtype) at hw
  rw [omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective] at hw
  obtain ⟨v,hv,rfl⟩ := hw
  exact congrArg H.subtype (hc hy v hv)

end CFSG.Quasithin.Chapter14.Section06

