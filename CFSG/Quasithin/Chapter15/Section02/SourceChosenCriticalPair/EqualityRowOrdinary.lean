module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.EqualityRowJanko
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.TerminalModels.LinearTwo
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.TerminalModels.LinearThree
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.Alternating

/-!
# Ordinary-component exclusions without a partner residual identity

The actual wreath residual has nontrivial two-core. Its normalizer contains
H, whose unique maximal two-local overgroup is Mc. This controls C_G(K)
directly. Two-perfectness makes K normalize every ordinary component of an
escaping overgroup. For maximal-Sylow PSL₂ models its action is trivial,
contradicting this centralizer bound. Full-rank models place K inside the
literal component residual, giving rank two in the marked fixed subgroup.

All statements use the original ResidualInput, marked component and Sylow.
No PlaneUniquenessPreceding packet or Kc = O^{3′}(Mc) is assumed.
Source: Aschbacher--Smith 15.2.24 and the proof of 15.2.15, pp.1117--1118,
refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open Section01 Section03 ChapterA.Section05To06 ChapterD.UniqueFactor
open OrdinaryComponents Candidates.ComponentStructure ClassificationModels
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B I : Subgroup G}
variable {h : ChosenSmallSource T M Mc V}
variable (r : ResidualInput h H B)
include r

/-- The source's two maximal overgroups already give uniqueness for H. -/
theorem ResidualInput.local_unique_direct : maximalTwoLocalOvergroups H = {Mc} := by
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    h.partner ▸ Set.mem_singleton Mc
  ext N
  constructor
  · intro hN
    have hNT : N ∈ maximalTwoLocalOvergroups (T : Subgroup G) :=
      ⟨hN.1,r.outside.1.1.2.trans hN.2⟩
    rw [r.two_overgroups,Set.mem_insert_iff,Set.mem_singleton_iff] at hNT
    rcases hNT with rfl | rfl
    · exact (r.outside.1.2 hN.2).elim
    · exact Set.mem_singleton _
  · rintro rfl
    exact ⟨hMc.1,r.geometry.in_partner⟩

/-- The nontrivial residual two-core controls the entire ambient centralizer. -/
theorem ResidualInput.residual_centralizer_le_partner :
    centralizer (residual H : Set G) ≤ Mc := by
  let Q := (residual H).pCoreIn 2
  have hHK : H ≤ normalizer (residual H : Set G) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pResidual 2 H))
  have hHQ : H ≤ normalizer (Q : Set G) :=
    hHK.trans (normalizer_le_normalizer_characteristic_image (residual H)
      (pCore 2 (residual H)))
  have hN : normalizer (Q : Set G) ≤ Mc :=
    normalizer_le_of_unique_maximalTwoLocal
      (fun N hN hHN => Set.mem_singleton_iff.mp (r.local_unique_direct ▸ ⟨hN,hHN⟩))
      (isPGroup_pCoreIn 2 (residual H))
      (r.mem_Xi.pCoreIn_ne_bot
        (fun A hA N hN hNA hn => Chapter1.lemma_1_1_3_1 hA hN hNA hn)
        (Chapter1.lemma_1_1_4_6 T (h.ambient.evenCharacteristic T))) hHQ
  exact (centralizer_le (pCoreIn_le 2 (residual H))).trans
    ((Subgroup.centralizer_le_normalizer _).trans hN)

/-- In an escaping plane overgroup, the original residual lies in I. -/
theorem ResidualInput.residual_le_plane_escape (hI : PlaneEscapes Mc ⁅V,B⁆ I) :
    residual H ≤ I := by
  apply (le_inf ?_ r.residual_centralizes_plane).trans hI.2.1
  exact (map_subtype_le _).trans r.geometry.in_partner

/-- The order-two source seed marks the literal singleton centralizer. -/
theorem ResidualInput.marked_centralizer_of_seed_card
    (hc : Nat.card (centralInvolutions T) = 2)
    {z : G} (hz : z ∈ centralInvolutions T) (hne : z ≠ 1) :
    orderOf z = 2 ∧ centralizer ({z} : Set G) = Mc := by
  have ho : orderOf z = 2 := by
    have hd : orderOf (⟨z,hz⟩ : centralInvolutions T) ∣ 2 :=
      hc ▸ orderOf_dvd_natCard (⟨z,hz⟩ : centralInvolutions T)
    rw [← Subgroup.orderOf_coe] at hd
    exact ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left (by simpa using hne)
  refine ⟨ho,?_⟩
  have he : zpowers z = centralInvolutions T := eq_of_le_of_card_ge
    (zpowers_le.mpr hz) (by rw [Nat.card_zpowers,ho,hc])
  rw [r.partner_eq_centralizer,←he,zpowers_eq_closure,centralizer_closure]

/-- Two-perfectness fixes the ordinary component in its orbit of length at most two. -/
theorem ResidualInput.ordinary_component_normalizes
    (hI : PlaneEscapes Mc ⁅V,B⁆ I) {L : Subgroup I} (hL : IsComponent I L) :
    residual H ≤ normalizer (L.map I.subtype : Set G) := by
  let K := residual H
  have hKI : K ≤ I := r.residual_le_plane_escape hI
  let A := K.subgroupOf I
  have hpA : IsPPerfect 2 A := (isPPerfect_embedded_pResidual 2 H).of_surjective
    (subgroupOfEquivOfLe hKI).symm.toMonoidHom (subgroupOfEquivOfLe hKI).symm.surjective
  have hAN : A ≤ normalizer (L : Set I) := by
    rcases hL.normal_or_index_two_of_odd_rank_le_two
      (Chapter3.sqtk_of_mem_H h.ambient hI.1).stronglyQuasithin with hn | hi
    · let := hn
      rw [normalizer_eq_top]
      exact le_top
    · let N := normalizer (L : Set I)
      let : N.Normal := normal_of_index_eq_two hi
      have hq : IsPGroup 2 (I ⧸ N) := IsPGroup.of_card (n := 1) (by
        simpa only [← index_eq_card,pow_one] using hi)
      exact (le_pResidual_of_isPPerfect A hpA).trans (sInf_le ⟨inferInstance,hq⟩)
  intro k hk
  exact L.le_normalizer_map I.subtype
    (mem_map_of_mem I.subtype (hAN (show (⟨k,hKI hk⟩ : I) ∈ A from hk)))

/-- The original wreath residual lies in the cubic residual of every escaping I. -/
theorem ResidualInput.residual_le_escape_cubic
    (hI : PlaneEscapes Mc ⁅V,B⁆ I) :
    residual H ≤ (primeToResidual 3 I).map I.subtype := by
  let K := residual H
  have hKI : K ≤ I := r.residual_le_plane_escape hI
  let A := K.subgroupOf I
  let e := subgroupOfEquivOfLe hKI
  let f : A →* H := (inclusion (show K ≤ H from map_subtype_le _)).comp e.toMonoidHom
  have hpi : IsPiGroup twoThreePrimes A :=
    (twoThree_of_wreath H r.quotient.some).of_injective f
      ((inclusion_injective (show K ≤ H from map_subtype_le _)).comp e.injective)
  have hpA : IsPPerfect 2 A := (isPPerfect_embedded_pResidual 2 H).of_surjective
    e.symm.toMonoidHom e.symm.surjective
  have ht : primeToResidual 3 A = ⊤ :=
    (twoResidual_eq_primeToResidual_three hpi).symm.trans ((pResidual_eq_top_iff 2 A).mpr hpA)
  have hA : A ≤ primeToResidual 3 I := by
    have hh := map_primeToResidual_le_of_hom 3 A.subtype
    rw [ht, ← MonoidHom.range_eq_map, range_subtype] at hh
    exact hh
  exact (map_subgroupOf_eq_of_le hKI).symm.le.trans (map_mono hA)

variable {P : Sylow 2 I} {z : G}
variable (c : ComponentData (T := T) (Mc := Mc) I P z)

/-- The literal source K gives rank two in the component's marked fixed subgroup. -/
theorem ResidualInput.fixed_three_rank_of_full_component_direct
    (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (hc : Nat.card (centralInvolutions T) = 2)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (hcenter : center c.component = ⊥) (hr : 2 ≤ primeRank 3 c.component)
    (ho : IsPGroup 2 (MulAut.Outer c.component))
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹) :
    2 ≤ primeRank 3 a.fixedSubgroup := by
  let K := residual H
  have hKL : K ≤ c.component.map I.subtype := by
    rw [component_eq_cubic_residual (hsource := h) c hI hcenter hr ho]
    exact r.residual_le_escape_cubic hI
  let e := c.component.equivMapOfInjective I.subtype I.subtype_injective
  let f : K →* c.component := e.symm.toMonoidHom.comp (inclusion hKL)
  have hf (k : K) : ((f k : I) : G) = k := by
    exact congrArg Subtype.val (e.apply_symm_apply ⟨k,hKL k.property⟩)
  have hfix (k : K) : f k ∈ a.fixedSubgroup := by
    rw [MulAut.mem_fixedSubgroup]
    apply Subtype.ext
    apply Subtype.ext
    rw [ha,hf]
    have hkMc : (k : G) ∈ Mc := r.geometry.in_partner (map_subtype_le _ k.property)
    have hkz : (k : G) * z = z * k := mem_centralizer_singleton_iff.mp
      ((r.marked_centralizer_of_seed_card hc hz hzne).2.ge hkMc)
    rw [←hkz,mul_inv_cancel_right]
  let g := f.codRestrict a.fixedSubgroup hfix
  have hg : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    exact (hf x).symm.trans ((congrArg (fun w : a.fixedSubgroup => ((w.val : I) : G)) hxy).trans (hf y))
  have he := residualQuotientEquiv H r.quotient.some
  have hl : 2 ≤ primeRank 3 K := by
    have helem : IsElementaryAbelian 3 (Chapter1.XiQuotient K) :=
      IsElementaryAbelian.of_injective he.toMonoidHom he.injective
    let := helem
    have hrq : primeRank 3 (Chapter1.XiQuotient K) = 2 := by
      rw [← IsElementaryAbelian.log_card_eq_primeRank (p := 3),
        Nat.card_congr he.toEquiv,
        Chapter13.Section08.Components.Swapped.LinearThree.WreathModel.cubicBase_card]
      decide
    rw [←hrq]
    exact primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup
  exact hl.trans (_root_.primeRank_le_of_injective 3 g hg)

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
