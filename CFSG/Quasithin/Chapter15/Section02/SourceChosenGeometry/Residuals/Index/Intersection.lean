module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.Index.NormalAction
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.Index.Components
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Theory.GroupTheory.PrimeRankZero

/-!
# Full support from the original intersection

In the equality row Kc = K, the actual wreath quotient makes the original
Sylow subgroup maximal in H. Hence H ∩ M = T, and the intersection M ∩ Mc
meets K only inside O₂(K). The full normalizer action on K/O₂(K) is a
two-group. Consequently the two-residual of M ∩ Mc commutes with K modulo
O₂(K). Their disjoint images contribute independent three-ranks, so the
ambient bound two forces M ∩ Mc to have order prime to three.

Its literal O^{3′} residual is therefore trivial. In the other rows the
component residual calculation already gives centralization of Z. Together
these arguments exclude the literal proper-support alternative and construct
the parent's geometry on [V,B], without an index or Held-exclusion premise.

The full equality Kc = O^{3′}(Mc) in the equality row and ambient exclusion
of Held from the short structural list remain with this residual-geometry
owner. The parent `qt-e-152-plane-geometry` discharges the earlier source
hypotheses collected in `ResidualInput`.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
15.2.12(4)--(5), printed p.1111. The argument above proves the intersection
consequence directly before the full partner residual identity.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open Chapter1 Chapter13.Section08.Components.Swapped.LinearThree
open Section01 Section03 Section03.InitialSource ChapterD ChapterD.UniqueFactor
open ResidualCentralizerRank

private theorem coprime_of_normal_factor_disjoint
    {A : Type*} [Group A] [Finite A] (J K : Subgroup A) [K.Normal]
    (hi : J ⊓ K ≤ K.pCoreIn 2)
    (hc : ⁅(pResidual 2 J).map J.subtype,K⁆ ≤ K.pCoreIn 2)
    (hK : 2 ≤ primeRank 3 K) (hA : primeRank 3 A ≤ 2) :
    Nat.Coprime 3 (Nat.card J) := by
  let Q := K.pCoreIn 2
  let : Q.Normal := inferInstanceAs (((pCore 2 K).map K.subtype).Normal)
  let q := QuotientGroup.mk' Q
  let R := (pResidual 2 J).map J.subtype
  have hq : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact isPGroup_pCoreIn 2 K
  have hcomm : R.map q ≤ centralizer (K.map q : Set (A ⧸ Q)) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [← map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hc
  have hd : R.map q ⊓ K.map q = ⊥ := by
    apply _root_.eq_bot_iff.mpr
    rintro x ⟨⟨r,hr,rfl⟩,hk⟩
    have hrK : r ∈ K := by
      have hh : r ∈ (K.map q).comap q := hk
      rwa [comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr (pCoreIn_le 2 K)] at hh
    exact (QuotientGroup.eq_one_iff r).mpr (hi ⟨map_subtype_le _ hr,hrK⟩)
  have hs := primeRank_sum_le_of_residual_images (p := 3) (by decide) q hq J K
    hcomm (by rw [hd,card_bot]; exact Nat.coprime_one_right _)
  have hb := (primeRank_quotient_le_of_isTwoGroup 3 (by decide) Q
    (isPGroup_pCoreIn 2 K)).trans hA
  have hz : primeRank 3 J = 0 := by omega
  exact Nat.prime_three.coprime_iff_not_dvd.mpr (PrimeRank.eq_zero_iff_not_dvd_card.mp hz)

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B : Subgroup G}

/-- The source wreath has no subgroup strictly between the fixed Sylow and H. -/
theorem ResidualInput.intersection_eq_sylow {h : ChosenSmallSource T M Mc V}
    (d : ResidualInput h H B) : H ⊓ M = (T : Subgroup G) := by
  let S := T.subtype d.outside.1.1.2
  let f : H →* WreathModel.W :=
    (d.quotient.some.trans matrixWreathEquiv).toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hf : Function.Surjective f := (d.quotient.some.trans matrixWreathEquiv).surjective.comp
    (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 H := by
    ext x
    change (d.quotient.some.trans matrixWreathEquiv) (QuotientGroup.mk' (pCore 2 H) x) = 1 ↔ _
    rw [← (d.quotient.some.trans matrixWreathEquiv).map_one,
      (d.quotient.some.trans matrixWreathEquiv).injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  have hm := isCoatom_comap_of_surjective hf (wreath_two_sylow_isCoatom (S.mapSurjective hf))
  change IsCoatom (((S : Subgroup H).map f).comap f) at hm
  rw [comap_map_eq_self (hk ▸ pCore_isPGroup.le_sylow_of_normal S)] at hm
  have ht : (S : Subgroup H) ≤ M.subgroupOf H := fun _ hx => h.maximal.1.2 hx
  rcases hm.le_iff.mp ht with he | he
  · have hHM : H ≤ M := by
      intro x hx
      have hxM : (⟨x,hx⟩ : H) ∈ M.subgroupOf H := he.symm ▸ trivial
      exact hxM
    exact (d.outside.1.2 hHM).elim
  · have hh := congrArg (Subgroup.map H.subtype) he
    change (M.subgroupOf H).map H.subtype =
      ((T : Subgroup G).subgroupOf H).map H.subtype at hh
    rw [subgroupOf_map_subtype, map_subgroupOf_eq_of_le d.outside.1.1.2] at hh
    simpa only [inf_comm] using hh

private theorem two_subgroup_le_core {A : Type*} [Group A]
    (U : Subgroup A) (hU : IsPGroup 2 U) (hA : IsPGroup 3 (A ⧸ pCore 2 A)) :
    U ≤ pCore 2 A := by
  let q := QuotientGroup.mk' (pCore 2 A)
  have hd := (hU.map q).disjoint_of_coprime (hA.to_subgroup ⊤) (by decide)
  have hz : U.map q = ⊥ := by simpa only [disjoint_top] using hd
  simpa only [q, QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hz

/-- In the equality row, the original intersection has order prime to three. -/
theorem ResidualInput.intersection_three_free_of_eq {h : ChosenSmallSource T M Mc V}
    (d : ResidualInput h H B) (he : partnerSpan H Mc = residual H) :
    Nat.Coprime 3 (Nat.card (M ⊓ Mc : Subgroup G)) := by
  have hHM : H ≤ Mc :=
    (source_centralizing_HStar_le_seed_centralizer h.ambient T h.maximal
      d.outside h.centralizing).trans (centralizer_le_partner T h.partner)
  have hKM : residual H ≤ Mc := (map_subtype_le _).trans hHM
  let K := (residual H).subgroupOf Mc
  let J := M.subgroupOf Mc
  let e : K ≃* residual H := subgroupOfEquivOfLe hKM
  let eQ := QuotientGroup.congr (pCore 2 K) (pCore 2 (residual H)) e (pCore_map_iso 2 e)
  let a := eQ.trans (residualQuotientEquiv H d.quotient.some)
  let : IsElementaryAbelian 3 (K ⧸ pCore 2 K) :=
    IsElementaryAbelian.of_injective a.toMonoidHom a.injective
  have hcard : Nat.card (K ⧸ pCore 2 K) = 3 ^ 2 :=
    (Nat.card_congr a.toEquiv).trans WreathModel.cubicBase_card
  let : K.Normal := normal_subgroupOf_of_le_normalizer (partner_normalizes_of_eq H Mc he)
  have htwo : IsPGroup 2 ((J ⊓ K).subgroupOf K) := by
    let f : ((J ⊓ K).subgroupOf K) →* T :=
      { toFun := fun x => ⟨((x : K) : Mc), by
          apply d.intersection_eq_sylow.le
          exact ⟨(map_subtype_le (pResidual 2 H)) x.val.property, x.property.1⟩⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    apply T.isPGroup'.of_injective f
    intro x y hxy
    have hh := congrArg (fun z : T => (z : G)) hxy
    exact Subtype.ext (Subtype.ext (Subtype.ext hh))
  have hi : J ⊓ K ≤ K.pCoreIn 2 := by
    have hh := map_mono (f := K.subtype)
      (two_subgroup_le_core ((J ⊓ K).subgroupOf K) htwo
        (IsElementaryAbelian.isPGroup 3 (K ⧸ pCore 2 K)))
    rwa [map_subgroupOf_eq_of_le (show J ⊓ K ≤ K from inf_le_right)] at hh
  let R := (pResidual 2 J).map J.subtype
  let f := (partnerQuotientAction H Mc he).comp J.subtype
  have hp : IsPGroup 2 f.range := by
    apply d.normalizer_quotient_action_two.to_le
    rintro _ ⟨x,rfl⟩
    exact ⟨inclusion (partner_normalizes_of_eq H Mc he) (x : Mc),rfl⟩
  have hk : R ≤ (partnerQuotientAction H Mc he).ker := by
    have hh := pResidual_le_ker_of_isPGroup 2 f.rangeRestrict hp
    rw [MonoidHom.ker_rangeRestrict] at hh
    rintro x ⟨y,hy,rfl⟩
    exact hh hy
  have hc : ⁅R,K⁆ ≤ K.pCoreIn 2 := by
    apply commutator_le.mpr
    intro x hx y hy
    let yK : residual H := ⟨(y : G),hy⟩
    let n := inclusion (partner_normalizes_of_eq H Mc he) x
    let y' := (residual H).normalizerMonoidHom n yK
    have hf : QuotientGroup.mk' (pCore 2 (residual H)) y' =
        QuotientGroup.mk' (pCore 2 (residual H)) yK := by
      have hh := DFunLike.congr_fun (show partnerQuotientAction H Mc he x = 1 from hk hx)
        (QuotientGroup.mk' (pCore 2 (residual H)) yK)
      change quotientAut (pCore 2 (residual H))
        ((residual H).normalizerMonoidHom n) (QuotientGroup.mk' _ yK) = _ at hh
      simpa only [quotientAut_apply_mk, MulAut.one_apply] using hh
    have hz : y' * yK⁻¹ ∈ pCore 2 (residual H) := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' (pCore 2 (residual H)) (y' * yK⁻¹) = 1
      rw [map_mul,map_inv,hf,mul_inv_cancel]
    have hzG : (⁅x,y⁆ : Mc).val ∈ (residual H).pCoreIn 2 :=
      ⟨y' * yK⁻¹,hz,rfl⟩
    have hecore : (K.pCoreIn 2).map Mc.subtype = (residual H).pCoreIn 2 := by
      rw [map_pCoreIn_of_injective 2 K Mc.subtype Mc.subtype_injective,
        map_subgroupOf_eq_of_le hKM]
    rw [← hecore] at hzG
    obtain ⟨z,hz,hzx⟩ := hzG
    exact (show z = ⁅x,y⁆ from Subtype.ext hzx) ▸ hz
  have hrK : 2 ≤ primeRank 3 K := by
    let : IsElementaryAbelian 3 (⊤ : Subgroup (K ⧸ pCore 2 K)) :=
      IsElementaryAbelian.of_injective (⊤ : Subgroup (K ⧸ pCore 2 K)).subtype
        (⊤ : Subgroup (K ⧸ pCore 2 K)).subtype_injective
    have hr : 2 ≤ primeRank 3 (K ⧸ pCore 2 K) :=
      IsElementaryAbelian.primeRank_ge_of_card ⊤ (by simpa only [card_top] using hcard)
    exact hr.trans (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup)
  have hcJ := coprime_of_normal_factor_disjoint J K hi hc hrK
    ((h.ambient.twoLocal_sqtk (partner_mem_overgroups h).1.1).stronglyQuasithin
      3 Nat.prime_three (by decide))
  have heJ : J.map Mc.subtype = M ⊓ Mc := subgroupOf_map_subtype M Mc
  have hc : Nat.card J = Nat.card (M ⊓ Mc : Subgroup G) :=
    (Nat.card_congr (J.equivMapOfInjective Mc.subtype Mc.subtype_injective).toEquiv).trans
      (Nat.card_congr (MulEquiv.subgroupCongr heJ).toEquiv)
  rwa [hc] at hcJ

/-- In the equality row the literal intersection residual is trivial. -/
theorem ResidualInput.intersection_residual_eq_bot_of_eq
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B)
    (he : partnerSpan H Mc = residual H) : threePrimeResidual (M ⊓ Mc) = ⊥ := by
  have hc := d.intersection_three_free_of_eq he
  have hz : primeToResidual 3 (M ⊓ Mc : Subgroup G) = ⊥ := by
    apply bot_unique
    apply primeToResidual_le
    simpa only [index_bot] using hc
  rw [threePrimeResidual_eq,hz,Subgroup.map_bot]

/-- Every original residual row gives the intersection centralization needed
for proper-support exclusion, independently of the short model list. -/
theorem ResidualInput.intersection_centralizes_source
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B) :
    threePrimeResidual (M ⊓ Mc) ≤ M ⊓ centralizer (centralInvolutions T : Set G) := by
  by_cases he : partnerSpan H Mc = residual H
  · rw [d.intersection_residual_eq_bot_of_eq he]
    exact bot_le
  · exact d.intersection_centralizes (d.residual_equality_of_ne he)

/-- The literal proper-support alternative in original 15.2.12(5) is impossible. -/
theorem ResidualInput.not_proper
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B) :
    letI := localModule_elementary_from_source h.ambient T
      ⟨Chapter1.mem_H_of_isTwoLocal h.maximal.1.1.1,h.maximal.1.2⟩
    ¬ ∃ U : Submodule (ZMod 2) (Additive (localModule T M)),
      SourceCases.Proper T M Mc (localModule T M)
        (imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)) U ∧
      V = (Subgroup.toAddSubgroup.symm U.toAddSubgroup).map (localModule T M).subtype :=
  not_proper_of_intersection_centralizes h d.intersection_centralizes_source

/-- The chosen module is the full local module, in all original residual rows. -/
theorem ResidualInput.full
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B) : V = localModule T M :=
  full_of_intersection_centralizes h d.intersection_centralizes_source

/-- The actual commutator plane supplies the parent geometry with no
remaining index or model-exclusion premise. -/
theorem ResidualInput.geometry
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B) :
    ChosenPlaneGeometry h H ⁅V,B⁆ := d.geometry_of_full d.full

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
