module

public import CFSG.Quasithin.Chapter16.Section01To02.CoverAndSylowElimination.CoverStructure
public import CFSG.Quasithin.Chapter16.Section01To02.CoverAndSylowElimination.PairAction

/-!
# Placing the covered Suzuki Sylow omega subgroup

First conjugate the external involution inside N_H(L), whose index in H is
 two. The starred action assertion then puts Ω₁(T_L) in Hᵍ. Sylow conjugacy
inside Hᵍ places it in Tᵍ while retaining g outside H. Its relative normalizer
of Lᵍ has index at most two, hence cannot lie in Z(L), whose index is eight.
Normalizer control and the two-component action place its commuting conjugate
omega subgroup in both component normalizers.

All conjugators and the relative-normalizer witness are retained in the
exported placement. No placement conclusion is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of Lemma 16.2.11, printed p.1176.
-/

public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter16 CFSG.Quasithin.ChapterI.Section06To08
namespace CFSG.Quasithin.Chapter16.CoverAndSylowElimination
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z u : G} {L : Subgroup G}

private theorem conjugate_into_sylow (M A : Subgroup G) (P : Sylow 2 M)
    (hp : IsPGroup 2 A) (hAM : A ≤ M) :
    ∃ k ∈ M, conjSubgroup A k ≤ (P : Subgroup M).map M.subtype := by
  obtain ⟨Q, hQ⟩ := (hp.comap_subtype (K := M)).exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq M Q P
  refine ⟨k, k.property, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  have haQ : (⟨a, hAM ha⟩ : M) ∈ Q := hQ ha
  have haP : MulAut.conj k (⟨a, hAM ha⟩ : M) ∈ P := by
    rw [← hk]
    exact mem_map_of_mem _ haQ
  exact ⟨_, haP, rfl⟩

omit [Finite G] in
private theorem conj_normalizer (A : Subgroup G) (g : G) :
    conjSubgroup (normalizer (A : Set G)) g = normalizer (conjSubgroup A g : Set G) :=
  map_equiv_normalizer_eq A (MulAut.conj g)

/-- Conjugating inside the index-two stabilizer retains the original component
and puts the external involution in the chosen Sylow subgroup. -/
theorem EarlierConclusions.external_involution_in_sylow
    (h : EarlierConclusions T z u L) :
    ∃ g ∉ localComponentNormalizer z L, ∃ i : G,
      orderOf i = 2 ∧ i ∈ conjSubgroup L g ∧
        i ∈ (T : Subgroup G) ⊓ normalizer (L : Set G) := by
  let H := localComponentNormalizer z L
  let N := (normalizer (L : Set G)).subgroupOf H
  have hNi : N.index = 2 := h.index_local
  let : N.Normal := normal_of_index_eq_two hNi
  obtain ⟨P, hP⟩ := (T.subtype h.sylow_le).exists_subgroupOf_eq_of_normal N
  obtain ⟨g, hg, i, hi, hiL, hiN⟩ := h.external_involution
  let iN : N := ⟨⟨i, hiN.1⟩, hiN.2⟩
  have hp : IsPGroup 2 (zpowers iN) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, ← orderOf_injective N.subtype N.subtype_injective,
      ← orderOf_injective H.subtype H.subtype_injective]
    change orderOf i = 2 ^ 1
    simpa using hi)
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq N Q P
  have hiP : MulAut.conj k iN ∈ P := by
    rw [← hk]
    exact mem_map_of_mem _ (hQ (mem_zpowers iN))
  have hiT : MulAut.conj ((k : H) : G) i ∈ T := by
    change MulAut.conj k iN ∈ (P : Subgroup N) at hiP
    rw [hP] at hiP
    exact hiP
  refine ⟨((k : H) : G) * g, ?_, MulAut.conj ((k : H) : G) i,
    (MulAut.conj ((k : H) : G)).orderOf_eq i |>.trans hi, ?_, hiT, ?_⟩
  · intro hkg
    exact hg ((H.mul_mem_cancel_left (k : H).property).mp hkg)
  · rw [← conjSubgroup_conjSubgroup]
    exact mem_map_of_mem _ hiL
  · exact (normalizer (L : Set G)).mul_mem
      ((normalizer (L : Set G)).mul_mem k.property hiN.2)
      ((normalizer (L : Set G)).inv_mem k.property)

private theorem align_sylow (h : EarlierConclusions T z u L)
    {A : Subgroup G} (hA : IsPGroup 2 A)
    {g : G} (hg : g ∉ localComponentNormalizer z L)
    (hAH : A ≤ conjSubgroup (localComponentNormalizer z L) g) :
    ∃ g' ∉ localComponentNormalizer z L, A ≤ conjSubgroup (T : Subgroup G) g' := by
  let H := localComponentNormalizer z L
  let Tg := T.mapSurjective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).surjective
  have hTg : (Tg : Subgroup G) ≤ conjSubgroup H g := conjSubgroup_mono h.sylow_le g
  obtain ⟨k, hk, hAk⟩ := conjugate_into_sylow (conjSubgroup H g) A
    (Tg.subtype hTg) hA hAH
  have hm : ((Tg.subtype hTg : Sylow 2 (conjSubgroup H g)) : Subgroup _).map
      (conjSubgroup H g).subtype = (Tg : Subgroup G) :=
    map_subgroupOf_eq_of_le hTg
  rw [hm] at hAk
  refine ⟨k⁻¹ * g, ?_, ?_⟩
  · intro hkg
    have hk' : g⁻¹ * k * g ∈ H := mem_conjSubgroup_iff.mp hk
    have hh := H.mul_mem hkg hk'
    have he : k⁻¹ * g * (g⁻¹ * k * g) = g := by group
    exact hg (he ▸ hh)
  · have hh := conjSubgroup_mono hAk k⁻¹
    rw [conjSubgroup_inv] at hh
    change A ≤ conjSubgroup (conjSubgroup (T : Subgroup G) g) k⁻¹ at hh
    rwa [conjSubgroup_conjSubgroup] at hh

/-- Sylow conjugacy retains an external conjugator and places the whole omega
subgroup in the conjugate ambient Sylow subgroup. -/
theorem CoverStructure.exists_omega_in_conjugate_sylow
    (hs : CoverStructure T L) (h : EarlierConclusions T z u L) :
    ∃ g ∉ localComponentNormalizer z L,
      sylowOmega T L ≤ conjSubgroup (T : Subgroup G) g := by
  obtain ⟨g, hg, i, hi, hiL, hiN⟩ := h.external_involution_in_sylow
  have hi2 : i ^ 2 = 1 := hi ▸ pow_orderOf_eq_one i
  let : IsElementaryAbelian 2 (zpowers i) := IsElementaryAbelian.zpowers_of_pow_eq_one hi2
  let : IsElementaryAbelian 2 (sylowOmega T L) := hs.elementary
  have hiC := (hs.elementary_normalizer_action 1 (zpowers i) inferInstance
    (by simpa only [conjSubgroup_one] using zpowers_le.mpr hiN)).2
  rw [conjSubgroup_one] at hiC
  have hZC : sylowOmega T L ≤ centralizer (zpowers i : Set G) :=
    le_centralizer_iff.mpr hiC
  have hine : zpowers i ≠ ⊥ := by
    intro he
    have hi1 : i = 1 := mem_bot.mp (he ▸ mem_zpowers i)
    simp [hi1] at hi
  have hiH := h.conjugate_centralizer_control g
    (IsElementaryAbelian.isPGroup 2 (zpowers i)) hine
    ((zpowers_le.mpr hiL).trans (conjSubgroup_mono le_sup_right g))
  exact align_sylow h (IsElementaryAbelian.isPGroup 2 (sylowOmega T L)) hg (hZC.trans hiH)

/-- The external conjugate can be placed in both component normalizers;
the chosen intermediate subgroup is exactly N_{Ω₁(T_L)}(Lᵍ). -/
theorem CoverStructure.placement (hs : CoverStructure T L)
    (h : EarlierConclusions T z u L) : CoverPlacement T z u L := by
  obtain ⟨g, hg, hZT⟩ := hs.exists_omega_in_conjugate_sylow h
  let Z := sylowOmega T L
  let X := Z ⊓ normalizer (conjSubgroup L g : Set G)
  let V := conjSubgroup Z g
  let : IsElementaryAbelian 2 Z := hs.elementary
  have hXe : IsElementaryAbelian 2 X := by
    refine {
      toIsMulCommutative := .of_setLike_mul_comm fun a ha b hb =>
        congrArg Subtype.val ((IsMulCommutative.is_comm (M := Z)).comm
          ⟨a, ha.1⟩ ⟨b, hb.1⟩)
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
    intro a
    apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian (A := Z) a.val a.property.1
  let : IsElementaryAbelian 2 X := hXe
  have hpX : IsPGroup 2 X := IsElementaryAbelian.isPGroup 2 X
  have hXN : X ≤ conjSubgroup ((T : Subgroup G) ⊓ normalizer (L : Set G)) g := by
    change X ≤ ((T : Subgroup G) ⊓ normalizer (L : Set G)).map (MulAut.conj g).toMonoidHom
    rw [map_inf _ _ _ (MulAut.conj g).injective]
    change X ≤ conjSubgroup (T : Subgroup G) g ⊓ conjSubgroup (normalizer (L : Set G)) g
    rw [conj_normalizer]
    exact le_inf (inf_le_left.trans hZT) inf_le_right
  have hXV : X ≤ centralizer (V : Set G) :=
    (hs.elementary_normalizer_action g X hXe hXN).2
  have hindex : (normalizer (conjSubgroup L g : Set G)).relIndex
      (conjSubgroup (localComponentNormalizer z L) g) = 2 := by
    rw [← conj_normalizer]
    exact (relIndex_map_map_of_injective _ _ (MulAut.conj g).injective).trans h.index_local
  have hXi : X.relIndex Z ≤ 2 := by
    change (Z ⊓ normalizer (conjSubgroup L g : Set G)).relIndex Z ≤ 2
    rw [inf_relIndex_left]
    have hh := relIndex_le_of_le_right (H := normalizer (conjSubgroup L g : Set G))
      (hZT.trans (conjSubgroup_mono h.sylow_le g)) (by rw [hindex]; decide)
    rwa [hindex] at hh
  have hXC : ¬ X ≤ componentCenter L := by
    intro hXC
    have hh := relIndex_le_of_le_left (L := Z) hXC
      (show X.relIndex Z ≠ 0 from (X.subgroupOf Z).index_ne_zero_of_finite)
    have hc : (componentCenter L).relIndex Z = 8 := hs.center_index
    omega
  have hXne : X ≠ ⊥ := fun he => hXC (he ▸ bot_le)
  have hXL : X ≤ L := inf_le_left.trans (sylowOmega_le.trans inf_le_right)
  have hVC : V ≤ centralizer (X : Set G) := le_centralizer_iff.mpr hXV
  have hVH : V ≤ localComponentNormalizer z L := hVC.trans
    ((centralizer_le_normalizer _).trans
      (h.normalizer_control X hpX hXne (hXL.trans le_sup_right)))
  have hVN : V ≤ normalizer (L : Set G) := hVC.trans
    ((centralizer_le_normalizer _).trans (h.normalizer_noncentral_two_subgroup hpX hXL hXC))
  exact ⟨g, hg, hZT, hXV, hXC, hXi,
    le_inf (le_inf hVH hVN) ((le_inf hVH hVN).trans h.normalizes_swapped)⟩

end CFSG.Quasithin.Chapter16.CoverAndSylowElimination
