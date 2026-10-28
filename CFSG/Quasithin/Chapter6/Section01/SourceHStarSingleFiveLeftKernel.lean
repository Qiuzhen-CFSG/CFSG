module

public import CFSG.Quasithin.Chapter6.Section01.SourceHStarSingleFiveOverlap
public import Theory.SpecificGroups.SymmetricFive.LocalTwoCore
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.LowerObstructions.PSL2.ElementaryLift
public import Theory.SpecificGroups.Alternating.FiveSylowMaximal
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalThompson
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalNaturalQuotient

/-!
# The original left omega-orbit in the single-five two-core

The literal left orbit is elementary and normalized by the actual overlap.
Its image in the marked S4 is therefore an even normal two-subgroup. An
image of order four would be an actual elementary lift of an A5 Sylow,
contrary to the original generation parameter one. The only smaller normal
possibility is central, and S4 has trivial center. Thus the whole left
orbit lies in O2(H), so the H-orbit centralizes it and lies in O2(LT).

The elementary subgroup used here exists in the original group. No lifting
of arbitrary elementary quotient subgroups or splitting of H is asserted.
Source: Aschbacher--Smith 6.1.5, p.666, and E.1.1--6, pp.209--211.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
open Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterE.ThompsonAction

namespace CFSG.Quasithin.Chapter6.Source.Hypothesis611

private theorem not_generation_one_of_even_plane
    {H : Type*} [Group H] [Finite H]
    (f : H →* (Equiv.Perm (Fin 5))) (hf : Function.Surjective f)
    (A : Subgroup H) [IsElementaryAbelian 2 A]
    (hA : A.map f ≤ (alternatingGroup (Fin 5))) (hc : Nat.card (A.map f) = 4) :
    ChapterE.generationParameter H ≠ 1 := by
  let D := (A.map f).subgroupOf (alternatingGroup (Fin 5))
  have hp : IsPGroup 2 D := (IsElementaryAbelian.isPGroup 2 A).map f |>.comap_subtype
  obtain ⟨Q,hDQ⟩ := hp.exists_le_sylow
  have hQcard : Nat.card Q = 4 := by
    rw [Q.card_eq_multiplicity,nat_card_alternatingGroup,Nat.card_fin]
    decide +kernel
  have hDcard : Nat.card D = 4 := (Nat.card_congr (subgroupOfEquivOfLe hA).toEquiv).trans hc
  have hDeq : D = (Q : Subgroup (alternatingGroup (Fin 5))) := eq_of_le_of_card_ge hDQ (by rw [hQcard,hDcard])
  have hmap : (Q : Subgroup (alternatingGroup (Fin 5))).map (alternatingGroup (Fin 5)).subtype = A.map f := by
    rw [←hDeq,map_subgroupOf_eq_of_le hA]
  let : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map f
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.subgroupOf hA
  let : IsElementaryAbelian 2 Q := hDeq ▸ inferInstanceAs (IsElementaryAbelian 2 D)
  have hrank : 1 < Group.rank Q := by
    have hd := card_dvd_exponent_pow_rank' Q
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 Q))
    have hl := Nat.le_of_dvd (by positivity : 0 < 2 ^ Group.rank Q) hd
    rw [hQcard] at hl
    by_contra hn
    have hu := pow_le_pow_right' (by decide : 1 ≤ (2 : ℕ)) (Nat.le_of_not_gt hn)
    norm_num at hu
    omega
  let : Group.IsPerfect (alternatingGroup (Fin 5)) := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  intro hgen
  have hg : ChapterE.IsEGenerated 1 H := by
    simpa only [hgen] using ChapterE.isEGenerated_generationParameter_of_pos
      (show 0 < ChapterE.generationParameter H by omega)
  exact ChapterE.ValuesEvenClassical.not_isEGenerated_of_rankOne_quotient_lift
    f hf (alternatingGroup (Fin 5)) (Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 5))) Q
    (Theory.SpecificGroups.Alternating.FiveSylowMaximal.overgroup_le_sylow_normalizer Q)
    (Theory.SpecificGroups.Alternating.FiveSylowMaximal.sylow_normalizer_isCoatom Q).ne_top
    A hmap.symm 1 hrank hg

private theorem pointFour_center_certificate :
    ∀ x : Equiv.Perm (Fin 5), x 4 = 4 →
      (∀ y : Equiv.Perm (Fin 5), y 4 = 4 → y*x*y⁻¹=x) → x=1 := by
  decide +kernel

private theorem elementary_normal_image_trivial
    {D : Type*} [Group D] [Finite D]
    (p : D →* Equiv.Perm (Fin 5)) (hp : Function.Surjective p)
    (hgen : ChapterE.generationParameter D = 1)
    (A : Subgroup D) [IsElementaryAbelian 2 A]
    (S : Sylow 2 (Equiv.Perm (Fin 5)))
    (a : Equiv.Perm (Fin 5))
    (hS : (S : Subgroup _) ≤ ChapterC.SymmetricFive.pointFour.map
      (MulAut.conj a).toMonoidHom)
    (hA : A.map p ≤ ChapterC.SymmetricFive.pointFour.map
      (MulAut.conj a).toMonoidHom)
    (hn : ChapterC.SymmetricFive.pointFour.map (MulAut.conj a).toMonoidHom ≤
      normalizer (A.map p : Set (Equiv.Perm (Fin 5)))) : A.map p = ⊥ := by
  let B := ChapterC.SymmetricFive.pointFour.map (MulAut.conj a).toMonoidHom
  let E := A.map p
  have hE2 : IsPGroup 2 E := (IsElementaryAbelian.isPGroup 2 A).map p
  have hEB : E ≤ B.pCoreIn 2 := le_pCoreIn_of_normalizes hE2 hA hn
  have hcB : Nat.card B = 24 := by
    rw [card_map_of_injective (MulAut.conj a).injective,ChapterC.SymmetricFive.pointFour_card]
  have heven : E ≤ alternatingGroup (Fin 5) := hEB.trans
    (Theory.SpecificGroups.SymmetricFive.LocalTwoCore.core_le_alternating B S hS
      (by rw [hcB]; decide))
  let F := E.subgroupOf (alternatingGroup (Fin 5))
  have hF2 : IsPGroup 2 F := hE2.comap_subtype
  obtain ⟨Q,hFQ⟩ := hF2.exists_le_sylow
  have hcQ : Nat.card Q = 4 := by
    rw [Q.card_eq_multiplicity,nat_card_alternatingGroup,Nat.card_fin]
    decide +kernel
  have hd : Nat.card E ∣ 4 := by
    have hh := card_dvd_of_le hFQ
    rwa [hcQ,Nat.card_congr (subgroupOfEquivOfLe heven).toEquiv] at hh
  have hfour : Nat.card E ≠ 4 := by
    intro hc
    exact not_generation_one_of_even_plane
      p hp A heven hc hgen
  have hsmall : Nat.card E ≤ 2 := by
    have hh := Nat.le_of_dvd (by decide : 0 < 4) hd
    have hn3 : Nat.card E ≠ 3 := by intro he; rw [he] at hd; norm_num at hd
    omega
  by_contra hne
  let : Nontrivial E := E.nontrivial_iff_ne_bot.mpr hne
  have hcE : Nat.card E = 2 := by
    let := Fintype.ofFinite E
    have hh : 1 < Nat.card E := by rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
    omega
  obtain ⟨z,hz,huniq⟩ := (Nat.card_eq_two_iff' (1 : E)).mp hcE
  have hcentral (x : E) (b : Equiv.Perm (Fin 5)) (hb : b ∈ B) : b*x.val*b⁻¹=x.val := by
    by_cases hx : x=1
    · simp [hx]
    have hmem : b*x.val*b⁻¹ ∈ E := (hn hb x.val).mp x.property
    have hne : (⟨b*x.val*b⁻¹,hmem⟩ : E) ≠ 1 := by
      intro he
      apply hx
      apply Subtype.ext
      have hh := congrArg Subtype.val he
      exact (MulAut.conj b).injective (hh.trans (map_one (MulAut.conj b)).symm)
    exact congrArg Subtype.val ((huniq _ hne).trans (huniq x hx).symm)
  have hzB : z.val ∈ B := hA z.property
  obtain ⟨x,hx,hxz⟩ := hzB
  have hxfix : x 4=4 := (ChapterC.SymmetricFive.mem_pointFour_iff x).mp hx
  have hxone : x=1 := pointFour_center_certificate x hxfix (by
    intro y hy
    apply (MulAut.conj a).injective
    have hh := hcentral z ((MulAut.conj a) y)
      (mem_map_of_mem (MulAut.conj a).toMonoidHom ((ChapterC.SymmetricFive.mem_pointFour_iff y).mpr hy))
    rw [←hxz] at hh
    simpa only [map_mul,map_inv,MulEquiv.coe_toMonoidHom] using hh)
  apply hz
  apply Subtype.ext
  simp only [←hxz,hxone,map_one,Subgroup.coe_one]

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V H : Subgroup G} {n : ℕ}
  (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)

theorem hstar_single_five_left_orbit_core
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥) :
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
    letI : U.Normal := (RankOneGeneric.Input.hstar_omega_orbit_reduced
      (h.rankOneInput hout) (h.maximal_eq_normalizer_L ▸ hH)).normal
    letI : IsElementaryAbelian 2 U := (RankOneGeneric.Input.hstar_omega_orbit_reduced
      (h.rankOneInput hout) (h.maximal_eq_normalizer_L ▸ hH)).elementary
    let C := centralizer (U : Set H)
    let q := QuotientGroup.mk' C
    let α := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    let Y := offenderSubgroup α
    ∀ _hqs : IsQuasisimple (generalizedFitting Y),
    ∀ s : MovedSection (α.comp Y.subtype) (generalizedFitting Y),
    ∀ _e : MarkedActionEquiv s.action (offenderSubgroup s.action) (generalizedFitting Y)
      (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5)),
      conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L ≤ H.pCoreIn 2 ∧
      conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H ≤
        (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  intro U C q α Y hqs s e
  obtain ⟨heq,p,hpk,hp,a,hBimage,hJimage,hindex,hnorm⟩ :=
    h.hstar_single_five_overlap hout hH hZH hqs s e
  let hi := h.rankOneInput hout
  have hm := h.omega_natural_fixed_quotient_of_hstar_moves hout hH hZH
  have hLC : ¬ L ≤ RankOneGeneric.omegaCentralizer T := fun hc =>
    RankOneGeneric.natural_quotient_omega_not_fixed hm (le_centralizer_iff.mp hc)
  let hs := hi.omega_span_input hLC
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let UL := conjugateSpanBy Z L
  let UH := conjugateSpanBy Z H
  have hULT : UL ≤ (T : Subgroup G) := hs.reduced_le_sylow
  have hULH : UL ≤ H := hULT.trans hH.1.1.2
  let A := UL.subgroupOf H
  let B := M.subgroupOf H
  let : IsElementaryAbelian 2 UL := hs.reduced.2.1
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf hULH
  have hAB : A ≤ B := fun _ hx => h.sylow_le (hULT hx)
  have hBA : B ≤ normalizer (A : Set H) := by
    intro b hb
    rw [mem_normalizer_iff]
    intro x
    exact (hnorm ⟨b.property,hb⟩).2 x.val
  have himage : A.map p = ⊥ := by
    apply elementary_normal_image_trivial p hp (h.generation_one H hH) A
      ((T.subtype hH.1.1.2).mapSurjective hp) a
    · rw [←hBimage]
      exact map_mono (f := p) (fun _ hx => h.sylow_le hx)
    · rw [←hBimage]
      exact map_mono (f := p) hAB
    · rw [←hBimage]
      exact (map_mono (f := p) hBA).trans (le_normalizer_map p)
  have hAcore : A ≤ pCore 2 H := hpk ▸ (Subgroup.map_eq_bot_iff _).mp himage
  have hULcore : UL ≤ H.pCoreIn 2 := by
    intro x hx
    exact mem_map_of_mem H.subtype (hAcore (show (⟨x,hULH hx⟩ : H) ∈ A from hx))
  have hUHred := hi.hstar_omega_orbit_reduced (h.maximal_eq_normalizer_L ▸ hH)
  have hUHH : UH ≤ H := conjugateSpanBy_le
    (fun _ hz => hH.1.1.2 ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1) H.le_normalizer
  have hfix : UH ≤ centralizer (UL : Set G) := by
    intro x hx u hu
    obtain ⟨v,hv,rfl⟩ := hULcore hu
    exact congrArg H.subtype (hUHred.le_centralizer_pCore (show (⟨x,hUHH hx⟩ : H) ∈ UH.subgroupOf H from hx) v hv)
  refine ⟨hULcore,?_⟩
  intro x hx
  have hxT : x ∈ (T : Subgroup G) :=
    hUHred.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal (T.subtype hH.1.1.2))
      (show (⟨x,hUHH hx⟩ : H) ∈ UH.subgroupOf H from hx)
  let D := L ⊔ (T : Subgroup G)
  have hxD : x ∈ D := (show (T : Subgroup G) ≤ D from le_sup_right) hxT
  apply mem_map_of_mem D.subtype (x := ⟨x,hxD⟩)
  rw [←hs.reduced_centralizer_core]
  intro u hu
  exact Subtype.ext (hfix hx u hu)

end CFSG.Quasithin.Chapter6.Source.Hypothesis611
