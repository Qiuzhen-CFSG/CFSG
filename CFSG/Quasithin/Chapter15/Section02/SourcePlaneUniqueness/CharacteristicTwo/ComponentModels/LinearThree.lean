module

public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.LinearThree.Setup
public import Theory.GroupTheory.WreathTwoCoreQuotient
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison
public import Theory.NumberTheory.BinaryTorusParity
public import Theory.GroupTheory.ConjugateSpanSylow
public import Theory.GroupTheory.WreathTwoOddCoreImageDichotomy
public import Theory.GroupTheory.PResidual.PrimeToPerfect

/-!
# Reductions for the linear-three component branch

For the original outside group H, its wreath quotient gives M ∩ H = T
and K ∩ M = O₂(K), where K is the embedded O²(H). A captured scalar
center in the actual X/O₂(X) quotient then rules out even field degree.

For the binary branch, the full wreath quotient has no S₃ quotient.
Applied to the restriction of the original NI action, this makes the
S-orbit of X equal X. The source component-orbit theorem then gives
normality relative to I, and minimality gives generation by MI and X.
Finally, a core commutator bound gives the containment for the literal
Y1 = O^{3′}(NI) used in the 15.2.22 contradiction.

The opposite-parabolic and distinguished-factor geometry remains explicit
in these reductions. This module does not assert the final branch exclusion.
Source: Aschbacher--Smith, combined manuscript (1 March 2004), proof of
15.2.23, printed p.1116, and 15.2.21--22, pp.1114--1115; refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The original outside subgroup meets M in T: Sylow maximality lifts through its wreath quotient. -/
theorem local_intersection_eq_sylow : M ⊓ H = (T : Subgroup G) := by
  have hTH := d.geometry.outside.1.1.2
  let P := T.subtype hTH
  obtain ⟨e⟩ := d.geometry.quotient
  let ew := RegularWreathProduct.congr SLTwoPermThree.sl2Two_equiv_perm_three.some.symm
    (MulEquiv.refl (Multiplicative (ZMod 2)))
  have hp := WreathTwoResidual.sylow_isCoatom_of_core_quotient P (e.trans ew)
  have hne : (M ⊓ H).subgroupOf H ≠ ⊤ := by
    intro he
    apply d.geometry.outside.1.2
    intro x hx
    have hh : (⟨x,hx⟩ : H) ∈ (M ⊓ H).subgroupOf H := he ▸ mem_top _
    exact hh.1
  have hle : (P : Subgroup H) ≤ (M ⊓ H).subgroupOf H :=
    fun x hx => ⟨hsource.maximal.1.2 hx,x.property⟩
  have he := congrArg (map H.subtype) ((hp.le_iff_eq hne).mp hle)
  change ((M ⊓ H).subgroupOf H).map H.subtype =
    ((T : Subgroup G).subgroupOf H).map H.subtype at he
  simpa only [map_subgroupOf_eq_of_le inf_le_right,
    map_subgroupOf_eq_of_le hTH] using he

/-- The source equality K ∩ M = O₂(K), with K the literal embedded two-residual of H. -/
theorem residual_intersection_eq_core :
    (pResidual 2 H).map H.subtype ⊓ M =
      ((pResidual 2 H).map H.subtype).pCoreIn 2 := by
  let K := (pResidual 2 H).map H.subtype
  have hKH : K ≤ H := map_subtype_le _
  have hHK : H ≤ normalizer (K : Set G) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pResidual 2 H))
  have hcoreM : K.pCoreIn 2 ≤ M :=
    (pCoreIn_mono_of_normalizes hKH hHK).trans
      ((pCoreIn_le_sylow H (T.subtype d.geometry.outside.1.1.2)).trans
        (by
          rintro x ⟨y,hy,rfl⟩
          exact hsource.maximal.1.2 hy))
  apply le_antisymm ?_ (le_inf (pCoreIn_le 2 K) hcoreM)
  have htwo : IsPGroup 2 (K ⊓ M : Subgroup G) := T.isPGroup'.to_le (by
    rw [← local_intersection_eq_sylow d]
    exact le_inf inf_le_right (inf_le_left.trans hKH))
  obtain ⟨e⟩ := d.geometry.quotient
  let ew := RegularWreathProduct.congr SLTwoPermThree.sl2Two_equiv_perm_three.some.symm
    (MulEquiv.refl (Multiplicative (ZMod 2)))
  obtain ⟨er⟩ := WreathTwoResidual.residual_core_quotient_equiv_elementaryNine (e.trans ew)
  let ek : pResidual 2 H ≃* K :=
    (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
  have hc : Nat.card (K ⧸ pCore 2 K) = 9 := by
    rw [← Nat.card_congr (QuotientGroup.congr _ _ ek (pCore_map_iso 2 ek)).toEquiv,
      Nat.card_congr er.toEquiv]
    simp [Nat.card_eq_fintype_card]
  let A := (K ⊓ M).subgroupOf K
  let q := QuotientGroup.mk' (pCore 2 K)
  have hAc : Nat.card (A.map q) = 1 := by
    rcases (htwo.comap_subtype.map q).card_eq_or_dvd with hh | hh
    · exact hh
    · have hd := hh.trans (A.map q).card_subgroup_dvd_card
      rw [hc] at hd
      norm_num at hd
  have hA : A ≤ pCore 2 K := by
    simpa only [q,QuotientGroup.ker_mk'] using
      (Subgroup.map_eq_bot_iff _).mp (Subgroup.card_eq_one.mp hAc)
  intro x hx
  exact mem_map_of_mem K.subtype (hA (show (⟨x,hx.1⟩ : K) ∈ A from hx))

end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree


open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree
variable {G : Type*} [Group G]

private theorem center_not_le_two_image {X : Subgroup G}
    {n : ℕ} {F : Type} [Field F] [Finite F]
    (e : (X ⧸ pCore 2 X) ≃* SL(3,F))
    (hF : Nat.card F = 2 ^ n) (hn : Even n)
    (A : Subgroup X) (hA : IsPGroup 2 A) :
    ¬ center (X ⧸ pCore 2 X) ≤ A.map (QuotientGroup.mk' (pCore 2 X)) := by
  intro hle
  have hs := ((hA.map (QuotientGroup.mk' (pCore 2 X))).to_le hle).of_equiv
    (centerCongr e)
  have hmod : Nat.card F % 3 = 1 := by
    rw [hF,Nat.BinaryTorusParity.two_pow_mod_three,if_pos (Nat.even_iff.mp hn)]
  have hne : center SL(3,F) ≠ ⊥ := fun he =>
    (Matrix.SL3.center_eq_bot_iff_card_mod_three F).mp he hmod
  have hc := Matrix.SL3.card_center_eq_three_of_ne_bot F hne
  rcases hs.card_eq_or_dvd with h | h <;> rw [hc] at h <;> norm_num at h

private theorem central_preimage_not_le_core {X K : Subgroup G}
    {n : ℕ} {F : Type} [Field F] [Finite F]
    (e : (X ⧸ pCore 2 X) ≃* SL(3,F))
    (hF : Nat.card F = 2 ^ n) (hn : Even n) :
    ¬ (centralPreimage (pCore 2 X)).map X.subtype ≤ K.pCoreIn 2 := by
  intro hle
  have hp := (isPGroup_pCoreIn 2 K).to_le hle
  have hp' : IsPGroup 2 (centralPreimage (pCore 2 X)) :=
    hp.of_equiv ((centralPreimage (pCore 2 X)).equivMapOfInjective
      X.subtype X.subtype_injective).symm
  exact center_not_le_two_image e hF hn _ hp' (by rw [map_centralPreimage])

/-- Even field degree and capture of the scalar center in the actual intersection eliminate n > 1. -/
theorem Branch.degree_eq_one_of_center_capture
    {M I H X : Subgroup G} {n : ℕ} {F : Type} [Field F] [Finite F]
    (b : Branch M I X n F)
    (hKM : (pResidual 2 H).map H.subtype ⊓ M =
      ((pResidual 2 H).map H.subtype).pCoreIn 2)
    (hgeometry : 1 < n → Even n ∧
      center (X ⧸ pCore 2 X) ≤
        (((pResidual 2 H).map H.subtype ⊓ M).subgroupOf X).map
          (QuotientGroup.mk' (pCore 2 X))) : n = 1 := by
  by_contra hn
  have hlarge : 1 < n := by have hp := b.positive; omega
  obtain ⟨heven,hcapture⟩ := hgeometry hlarge
  have hp : IsPGroup 2 ((pResidual 2 H).map H.subtype ⊓ M : Subgroup G) := by
    rw [hKM]
    exact isPGroup_pCoreIn 2 _
  obtain ⟨e⟩ := b.ms.1.model
  exact center_not_le_two_image e b.field_card heven _ hp.comap_subtype hcapture

/-- The stronger printed central-preimage containment implies the same degree-one reduction. -/
theorem Branch.degree_eq_one_of_central_preimage
    {M I H X : Subgroup G} {n : ℕ} {F : Type} [Field F] [Finite F]
    (b : Branch M I X n F)
    (hKM : (pResidual 2 H).map H.subtype ⊓ M =
      ((pResidual 2 H).map H.subtype).pCoreIn 2)
    (hgeometry : 1 < n → Even n ∧
      centralCorePreimage X ≤ (pResidual 2 H).map H.subtype ⊓ M) : n = 1 := by
  by_contra hn
  have hlarge : 1 < n := by have hp := b.positive; omega
  obtain ⟨heven,hcapture⟩ := hgeometry hlarge
  obtain ⟨e⟩ := b.ms.1.model
  exact central_preimage_not_le_core e b.field_card heven (hcapture.trans_eq hKM)

variable [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The S-orbit of a C-component is normal relative to I, by the source two-orbit theorem. -/
theorem component_orbit_normalizes (hI : PlaneEscapes Mc ZS I)
    {X : Subgroup G} (hX : X ∈ Chapter1.cComponentsIn I) :
    I ≤ normalizer (conjugateSpanBy X (planeSylow T ZS) : Set G) := by
  obtain ⟨P,hP⟩ := d.sylow_in_escape hI
  have hs := Chapter1.RadicalExclusions.sqtk_of_mem_H hsource.ambient hI.1
  have hQ : IsSQTK KnownSimple.IsKnownSimple (I ⧸ pCore 2 I) := by
    refine ⟨?_,hs.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hs.stronglyQuasithin p hp ho)
  let Y := conjugateSpanBy (X.subgroupOf I) (P : Subgroup I)
  let : Y.Normal := conjugateSpanBy_sylow_normal (X.subgroupOf I) P
    (Chapter1.Section02.proposition_1_2_1_three_orbit_source hQ hX.2)
  have he : Y.map I.subtype = conjugateSpanBy X (planeSylow T ZS) := by
    rw [map_conjugateSpanBy,map_subgroupOf_eq_of_le hX.1,hP]
  rw [← he]
  intro x hx
  apply Y.le_normalizer_map I.subtype
  exact ⟨⟨x,hx⟩,by rw [normalizer_eq_top]; trivial,rfl⟩

/-- An S-fixed C-component is normal relative to the actual escaping I. -/
theorem normal_of_orbit_eq (hI : PlaneEscapes Mc ZS I)
    {X : Subgroup G} (hX : X ∈ Chapter1.cComponentsIn I)
    (he : conjugateSpanBy X (planeSylow T ZS) = X) :
    I ≤ normalizer (X : Set G) := by
  rw [← he]
  exact component_orbit_normalizes d hI hX

/-- Minimality of the original escape gives generation by MI and any subgroup outside Mc. -/
theorem minimal_join (hI : MinimalPlaneEscape Mc ZS I)
    {X : Subgroup G} (hXI : X ≤ I) (hout : ¬ X ≤ Mc) :
    (Mc ⊓ I) ⊔ X = I := by
  rcases d.minimal_intermediate hI le_sup_left (sup_le inf_le_right hXI) with h | h
  · exact (hout (le_sup_right.trans (h.le.trans inf_le_left))).elim
  · exact h

/-- The core commutator bound yields both normalization directions for O^{3′}(M ∩ X) and K2. -/
theorem cubic_residual_commutator_le (hI : PlaneEscapes Mc ZS I)
    {X K2 : Subgroup G} (hXI : X ≤ I)
    (hIX : I ≤ normalizer (X : Set G))
    (hSK2 : planeSylow T ZS ≤ normalizer (K2 : Set G))
    (hK2 : IsPPerfect 2 K2) (hc : ⁅X,K2⁆ ≤ X.pCoreIn 2) :
    let Y := (primeToResidual 3 (M ⊓ X : Subgroup G)).map (M ⊓ X).subtype
    ⁅Y,K2⁆ ≤ Y ⊓ K2 := by
  let Y := (primeToResidual 3 (M ⊓ X : Subgroup G)).map (M ⊓ X).subtype
  have hQS : X.pCoreIn 2 ≤ planeSylow T ZS :=
    (pCoreIn_mono_of_normalizes hXI hIX).trans (d.core_le_plane hI)
  have hQM : X.pCoreIn 2 ≤ M := hQS.trans (inf_le_left.trans hsource.maximal.1.2)
  have he : (pResidual 2 K2).map K2.subtype = K2 := by
    rw [(pResidual_eq_top_iff 2 K2).mpr hK2,←MonoidHom.range_eq_map,range_subtype]
  have hXK2 : X ≤ normalizer (K2 : Set G) := by
    have hh := normalizes_residual_of_commutator_le_two X (planeSylow T ZS) K2
      (X.pCoreIn 2) hSK2 hQS (isPGroup_pCoreIn 2 X)
      (X.le_normalizer.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X)))
      (by simpa only [he] using hc)
    simpa only [he] using hh
  have hK2MX : K2 ≤ normalizer ((M ⊓ X : Subgroup G) : Set G) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    exact ((commutator_mono inf_le_right le_rfl).trans hc).trans
      (le_inf hQM (pCoreIn_le 2 X))
  have hK2Y : K2 ≤ normalizer (Y : Set G) :=
    hK2MX.trans (normalizer_le_normalizer_characteristic_image (M ⊓ X)
      (primeToResidual 3 (M ⊓ X : Subgroup G)))
  exact le_inf (le_normalizer_iff_commutator_le_left.mp hK2Y)
    (le_normalizer_iff_commutator_le_right.mp
      (((map_subtype_le _).trans inf_le_right).trans hXK2))

/-- Transport the commutator bound to the literal Y1 = O^{3′}(NI), retaining its residual identification. -/
theorem Branch.intersection_cubic_residual_commutator_le
    (hI : PlaneEscapes Mc ZS I)
    {X K2 : Subgroup G} {F : Type} [Field F] [Finite F]
    (b : Branch M I X 1 F)
    (hIX : I ≤ normalizer (X : Set G))
    (hSK2 : planeSylow T ZS ≤ normalizer (K2 : Set G))
    (hK2 : IsPPerfect 2 K2) (hc : ⁅X,K2⁆ ≤ X.pCoreIn 2)
    (he : (primeToResidual 3 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype =
      (primeToResidual 3 (M ⊓ X : Subgroup G)).map (M ⊓ X).subtype) :
    let Y := (primeToResidual 3 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype
    ⁅Y,K2⁆ ≤ Y ⊓ K2 := by
  dsimp only
  rw [he]
  exact cubic_residual_commutator_le d hI b.input.component.1 hIX hSK2 hK2 hc

end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree


open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree

abbrev BinaryWreath := RegularWreathProduct
  (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) (Multiplicative (ZMod 2))

private theorem no_symmetricThree_quotient_of_wreath
    {A : Type*} [Group A] [Finite A] (e : A ≃* BinaryWreath)
    (f : A →* Equiv.Perm (Fin 3)) (hf : Function.Surjective f) : False := by
  have hc : Nat.card f.range = 6 := by
    rw [MonoidHom.range_eq_top.mpr hf, Nat.card_congr Subgroup.topEquiv.toEquiv,
      Nat.card_eq_fintype_card, Fintype.card_perm]
    decide
  rcases wreathTwo_oddCore_le_ker_or_nine_dvd_range ⟨e⟩ f with hk | hd
  · have hd := index_dvd_of_le hk
    rw [index_ker, hc, wreathTwo_oddCore_index_eight ⟨e⟩] at hd
    norm_num at hd
  · rw [hc] at hd
    norm_num at hd

private theorem no_symmetricThree_quotient_of_core_wreath
    {A : Type*} [Group A] [Finite A]
    (e : (A ⧸ pCore 2 A) ≃* BinaryWreath)
    (f : A →* Equiv.Perm (Fin 3)) (hf : Function.Surjective f) : False := by
  have htwo : pCore 2 (Equiv.Perm (Fin 3)) = ⊥ := by
    have hh := ker_eq_twoCore_of_surjective_perm_three
      (MonoidHom.id (Equiv.Perm (Fin 3))) Function.surjective_id
      (by simp only [MonoidHom.ker_id]; exact IsPGroup.of_subsingleton 2 _)
    simpa only [MonoidHom.ker_id] using hh.symm
  have hn : ((pCore 2 A).map f).Normal :=
    (inferInstance : (pCore 2 A).Normal).map f hf
  have hm : (pCore 2 A).map f ≤ pCore 2 (Equiv.Perm (Fin 3)) :=
    le_sSup ⟨hn,pCore_isPGroup.map f⟩
  have hk : pCore 2 A ≤ f.ker :=
    (Subgroup.map_eq_bot_iff _).mp (bot_unique (hm.trans_eq htwo))
  exact no_symmetricThree_quotient_of_wreath e
    (QuotientGroup.lift _ f hk)
    (QuotientGroup.lift_surjective_of_surjective _ f hf hk)

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)

include d

-- Exactly the original MX S is used, and the map is restricted from NI.
/-- The full original action on (M ∩ X)S contradicts its wreath quotient when S moves X. -/
theorem component_orbit_eq_of_wreath
    (hI : PlaneEscapes Mc ZS I) {X : Subgroup G}
    (hXI : X ≤ I)
    (hmove : X < conjugateSpanBy X (planeSylow T ZS) →
      Nonempty ((((M ⊓ X) ⊔ planeSylow T ZS : Subgroup G) ⧸
        pCore 2 ((M ⊓ X) ⊔ planeSylow T ZS : Subgroup G)) ≃* BinaryWreath))
    (f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3))
    (hfull : (((M ⊓ X) ⊔ planeSylow T ZS).subgroupOf (M ⊓ I)).map f = ⊤) :
    conjugateSpanBy X (planeSylow T ZS) = X := by
  by_contra he
  have hlt : X < conjugateSpanBy X (planeSylow T ZS) :=
    lt_of_le_of_ne (le_conjugateSpanBy X _) (Ne.symm he)
  obtain ⟨e⟩ := hmove hlt
  have hL : (M ⊓ X) ⊔ planeSylow T ZS ≤ M ⊓ I :=
    sup_le (inf_le_inf_left M hXI)
      (le_inf (inf_le_left.trans hsource.maximal.1.2)
        ((le_sup_right.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_right))
  let g := f.comp (inclusion hL)
  have hg : Function.Surjective g := by
    intro y
    have hy : y ∈ (((M ⊓ X) ⊔ planeSylow T ZS).subgroupOf (M ⊓ I)).map f := by
      rw [hfull]
      trivial
    obtain ⟨x,hx,rfl⟩ := hy
    exact ⟨⟨x.val,hx⟩,rfl⟩
  exact no_symmetricThree_quotient_of_core_wreath e g hg

end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree

namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The nonbinary source consumer, with K ∩ M = O₂(K) discharged from the original wreath quotient. -/
theorem Branch.degree_eq_one_of_source_center_capture
    {X : Subgroup G} {n : ℕ} {F : Type} [Field F] [Finite F]
    (b : Branch M I X n F)
    (hgeometry : 1 < n → Even n ∧
      center (X ⧸ pCore 2 X) ≤
        (((pResidual 2 H).map H.subtype ⊓ M).subgroupOf X).map
          (QuotientGroup.mk' (pCore 2 X))) : n = 1 :=
  b.degree_eq_one_of_center_capture (residual_intersection_eq_core d) hgeometry

/-- The printed central-preimage route, with the source intersection equality discharged. -/
theorem Branch.degree_eq_one_of_source_central_preimage
    {X : Subgroup G} {n : ℕ} {F : Type} [Field F] [Finite F]
    (b : Branch M I X n F)
    (hgeometry : 1 < n → Even n ∧
      centralCorePreimage X ≤ (pResidual 2 H).map H.subtype ⊓ M) : n = 1 :=
  b.degree_eq_one_of_central_preimage (residual_intersection_eq_core d) hgeometry

/-- The actual linear-three component is normal in I once the moved-orbit quotient and restricted action are supplied. -/
theorem Branch.normal_of_wreath
    (hI : PlaneEscapes Mc ZS I)
    {X : Subgroup G} {n : ℕ} {F : Type} [Field F] [Finite F]
    (b : Branch M I X n F)
    (hmove : X < conjugateSpanBy X (planeSylow T ZS) →
      Nonempty ((((M ⊓ X) ⊔ planeSylow T ZS : Subgroup G) ⧸
        pCore 2 ((M ⊓ X) ⊔ planeSylow T ZS : Subgroup G)) ≃* BinaryWreath))
    (f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3))
    (hfull : (((M ⊓ X) ⊔ planeSylow T ZS).subgroupOf (M ⊓ I)).map f = ⊤) :
    I ≤ normalizer (X : Set G) :=
  normal_of_orbit_eq d hI b.input.component
    (component_orbit_eq_of_wreath d hI b.input.component.1 hmove f hfull)

/-- The binary source component is normal in I and generates I together with MI. -/
theorem Branch.binary_normal_join
    (hI : MinimalPlaneEscape Mc ZS I)
    {X : Subgroup G} {F : Type} [Field F] [Finite F]
    (b : Branch M I X 1 F) (hout : ¬ X ≤ Mc)
    (hmove : X < conjugateSpanBy X (planeSylow T ZS) →
      Nonempty ((((M ⊓ X) ⊔ planeSylow T ZS : Subgroup G) ⧸
        pCore 2 ((M ⊓ X) ⊔ planeSylow T ZS : Subgroup G)) ≃* BinaryWreath))
    (f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3))
    (_hker : f.ker = (centralizer (V : Set G)).subgroupOf (M ⊓ I))
    (hfull : (((M ⊓ X) ⊔ planeSylow T ZS).subgroupOf (M ⊓ I)).map f = ⊤) :
    I ≤ normalizer (X : Set G) ∧ (Mc ⊓ I) ⊔ X = I :=
  ⟨b.normal_of_wreath d hI.1 hmove f hfull,
    minimal_join d hI b.input.component.1 hout⟩

/-- The literal commutator containment used at the final 15.2.22 contradiction; the marked geometry remains explicit. -/
theorem Branch.binary_commutator_of_wreath
    (hI : PlaneEscapes Mc ZS I)
    {X K2 : Subgroup G} {F : Type} [Field F] [Finite F]
    (b : Branch M I X 1 F)
    (hmove : X < conjugateSpanBy X (planeSylow T ZS) →
      Nonempty ((((M ⊓ X) ⊔ planeSylow T ZS : Subgroup G) ⧸
        pCore 2 ((M ⊓ X) ⊔ planeSylow T ZS : Subgroup G)) ≃* BinaryWreath))
    (f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3))
    (_hker : f.ker = (centralizer (V : Set G)).subgroupOf (M ⊓ I))
    (hfull : (((M ⊓ X) ⊔ planeSylow T ZS).subgroupOf (M ⊓ I)).map f = ⊤)
    (hSK2 : planeSylow T ZS ≤ normalizer (K2 : Set G))
    (hK2 : IsPPerfect 2 K2) (hc : ⁅X,K2⁆ ≤ X.pCoreIn 2)
    (he : (primeToResidual 3 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype =
      (primeToResidual 3 (M ⊓ X : Subgroup G)).map (M ⊓ X).subtype) :
    let Y := (primeToResidual 3 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype
    ⁅Y,K2⁆ ≤ Y ⊓ K2 :=
  b.intersection_cubic_residual_commutator_le d hI
    (b.normal_of_wreath d hI hmove f hfull) hSK2 hK2 hc he

end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree

namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- Three hypotheses of 15.2.22 for the literal Y1 = O^{3′}(NI).
Its two-perfectness is a residual theorem; Y1 is not asserted to be a two-group. -/
theorem intersection_cubic_residual_basics (hI : PlaneEscapes Mc ZS I) :
    let Y := (primeToResidual 3 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype
    Y ≤ M ⊓ I ∧ IsPPerfect 2 Y ∧
      planeSylow T ZS ≤ normalizer (Y : Set G) := by
  let Y := (primeToResidual 3 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype
  let e : primeToResidual 3 (M ⊓ I : Subgroup G) ≃* Y :=
    (primeToResidual 3 (M ⊓ I : Subgroup G)).equivMapOfInjective
      (M ⊓ I).subtype (M ⊓ I).subtype_injective
  refine ⟨map_subtype_le _,
    (isPPerfect_primeToResidual (G := (M ⊓ I : Subgroup G)) 3 2 (by decide)).of_surjective
      e.toMonoidHom e.surjective, ?_⟩
  have hS : planeSylow T ZS ≤ M ⊓ I :=
    le_inf (inf_le_left.trans hsource.maximal.1.2)
      ((le_sup_right.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_right)
  exact hS.trans ((M ⊓ I).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image (M ⊓ I)
      (primeToResidual 3 (M ⊓ I : Subgroup G))))

omit d in
/-- Relative normality and prime-to-three index give the printed residual
identity O^{3′}(NI) = O^{3′}(M ∩ X), through the literal inclusions. -/
theorem intersection_cubic_residual_eq_of_coprime_index
    {X : Subgroup G} (hXI : X ≤ I)
    (hIX : I ≤ normalizer (X : Set G))
    (hindex : Nat.Coprime 3 ((M ⊓ X).subgroupOf (M ⊓ I)).index) :
    (primeToResidual 3 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype =
      (primeToResidual 3 (M ⊓ X : Subgroup G)).map (M ⊓ X).subtype := by
  let NI := M ⊓ I
  let N := (M ⊓ X).subgroupOf NI
  have hnorm : NI ≤ normalizer (M ⊓ X : Set G) :=
    (le_inf (inf_le_left.trans M.le_normalizer)
      (inf_le_right.trans hIX)).trans inf_normalizer_le_normalizer_inf
  let : N.Normal := normal_subgroupOf_of_le_normalizer hnorm
  have he := congrArg (map NI.subtype)
    (embedded_primeToResidual_eq_of_normal 3 N (primeToResidual_le N hindex))
  have hmap : N.map NI.subtype = M ⊓ X :=
    map_subgroupOf_eq_of_le (inf_le_inf_left M hXI)
  rw [map_embedded_primeToResidual_of_hom 3 N NI.subtype, hmap] at he
  exact he.symm

/-- The original Y1 satisfies the elementary input clauses of 15.2.22 and
its forbidden commutator bound, once the binary marked geometry is supplied.
The remaining 15.2.22 hypotheses (including the distinguished K2, reducibility,
and the three-prime centralizer) must still be established by source assembly. -/
theorem Branch.binary_smallActions_data
    (hI : PlaneEscapes Mc ZS I)
    {X K2 : Subgroup G} {F : Type} [Field F] [Finite F]
    (b : Branch M I X 1 F)
    (hmove : X < conjugateSpanBy X (planeSylow T ZS) →
      Nonempty ((((M ⊓ X) ⊔ planeSylow T ZS : Subgroup G) ⧸
        pCore 2 ((M ⊓ X) ⊔ planeSylow T ZS : Subgroup G)) ≃* BinaryWreath))
    (f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3))
    (hker : f.ker = (centralizer (V : Set G)).subgroupOf (M ⊓ I))
    (hfull : (((M ⊓ X) ⊔ planeSylow T ZS).subgroupOf (M ⊓ I)).map f = ⊤)
    (hSK2 : planeSylow T ZS ≤ normalizer (K2 : Set G))
    (hK2 : IsPPerfect 2 K2) (hc : ⁅X,K2⁆ ≤ X.pCoreIn 2)
    (hindex : Nat.Coprime 3 ((M ⊓ X).subgroupOf (M ⊓ I)).index) :
    let Y := (primeToResidual 3 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype
    (Y ≤ M ⊓ I ∧ IsPPerfect 2 Y ∧
      planeSylow T ZS ≤ normalizer (Y : Set G)) ∧ ⁅Y,K2⁆ ≤ Y ⊓ K2 := by
  have hn := b.normal_of_wreath d hI hmove f hfull
  have he := intersection_cubic_residual_eq_of_coprime_index b.input.component.1 hn hindex
  exact ⟨intersection_cubic_residual_basics d hI,
    b.binary_commutator_of_wreath d hI hmove f hker hfull hSK2 hK2 hc he⟩

end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree
