module

public import CFSG.Quasithin.Chapter6.Section01.SourceHStarOrbitCentralizer
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.FiveSeedObstruction

/-!
# The actual overlap in the single symmetric-five H-star row

The original whole quotient is S5, with its transposition-four Thompson
marking. Its unique maximal Sylow overgroup is the corresponding point
stabilizer. The omega seed centralizer strictly contains the Sylow: the
marked natural central section supplies the existing cubic fixed-space
obstruction. The relative index three then identifies that centralizer
with the literal overlap H intersect M.

The S4 image is taken modulo the original O2(H), not O2(H intersect M).
No elementary lift or splitting of the original covering group is used.
This is a source constraint on the single row, not its final exclusion.
Source: Aschbacher--Smith 6.1.5 and E.2.3, pp.666--667 and216--217.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
open Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterB.SourceInduction
open CFSG.Quasithin.ChapterE.ThompsonAction

namespace CFSG.Quasithin.Chapter6.Source.Hypothesis611
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V H : Subgroup G} {n : ℕ}
  (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)

include h in
private theorem intrinsic_maximal_eq_overlap
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hp : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤) :
    minimalParabolicMax (T.subtype hH.1.1.2) hp = M.subgroupOf H := by
  let S := T.subtype hH.1.1.2
  have hi := Chapter3.HStar.unique_maximal T h.sylow_le hH
  have hs : (S : Subgroup H) ≤ M.subgroupOf H := fun _ hx => h.sylow_le hx
  have hne : M.subgroupOf H ≠ ⊤ := by
    intro he
    apply hH.1.2
    intro x hx
    exact (show (⟨x,hx⟩ : H) ∈ M.subgroupOf H from he.symm ▸ mem_top _)
  have hcoat : IsCoatom (M.subgroupOf H) := by
    refine ⟨hne,?_⟩
    intro Y hY
    have hm : (M.subgroupOf H).map H.subtype = H ⊓ M := by
      exact (subgroupOf_map_subtype M H).trans (inf_comm M H)
    have hy : H ⊓ M < Y.map H.subtype := by
      rw [←hm]
      exact (map_lt_map_iff_of_injective H.subtype_injective).mpr hY
    have he := (hi.2.1.eq_or_eq hy.le (map_subtype_le Y)).resolve_left hy.ne'
    apply map_injective H.subtype_injective
    rw [he,←MonoidHom.range_eq_map,range_subtype]
  exact (minimalParabolicMax_unique S hp hcoat hs).symm

private theorem sylow_overlap_index_three
    {Q : Type*} [Group Q] [Finite Q]
    (S : Sylow 2 Q) (p : Q →* Equiv.Perm (Fin 5)) (hp : Function.Surjective p)
    (hk : p.ker ≤ S) (B : Subgroup Q) (hSB : (S : Subgroup Q) ≤ B)
    (a : Equiv.Perm (Fin 5))
    (hB : B.map p = ChapterC.SymmetricFive.pointFour.map (MulAut.conj a).toMonoidHom) :
    (S : Subgroup Q).relIndex B = 3 := by
  have hcS : Nat.card ((S : Subgroup Q).map p) = 8 := by
    change Nat.card (S.mapSurjective hp) = 8
    rw [Sylow.card_eq_multiplicity, Nat.card_perm]
    norm_num [Nat.factorial]
    decide +kernel
  have hiS : ((S : Subgroup Q).map p).index = 15 := by
    have hh := ((S : Subgroup Q).map p).card_mul_index
    rw [hcS,Nat.card_perm] at hh
    norm_num [Nat.factorial] at hh
    omega
  have hiB : (B.map p).index = 5 := by
    rw [hB,index_map_of_bijective (MulAut.conj a).bijective,
      ChapterC.SymmetricFive.pointFour_index]
  have hr := relIndex_mul_index (map_mono (f := p) hSB)
  rw [hiS,hiB] at hr
  have he := relIndex_map_map p (S : Subgroup Q) B
  rw [sup_eq_left.mpr hk,sup_eq_left.mpr (hk.trans hSB)] at he
  omega

/-- In the literal single marked-five row, the full omega seed centralizer is
exactly the original maximal overlap. Its image is an actual conjugate S4
inside the same whole S5 quotient, with kernel O2(H) retained. -/
theorem hstar_single_five_overlap
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
      H ⊓ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = H ⊓ M ∧
      ∃ p : H →* Equiv.Perm (Fin 5), p.ker = pCore 2 H ∧ Function.Surjective p ∧
        ∃ a : Equiv.Perm (Fin 5),
          (M.subgroupOf H).map p =
            ChapterC.SymmetricFive.pointFour.map (MulAut.conj a).toMonoidHom ∧
          (elementaryAbelianMaxJ (T.subtype hH.1.1.2 : Subgroup H)).map p =
            (ChapterB.Offenders.D 5).map (MulAut.conj a).toMonoidHom ∧
          (T.subtype hH.1.1.2 : Subgroup H).relIndex (M.subgroupOf H) = 3 ∧
          H ⊓ M ≤ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) ⊓
            normalizer (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L : Set G) := by
  let hi := h.rankOneInput hout
  have hH' : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) :=
    h.maximal_eq_normalizer_L ▸ hH
  let S := T.subtype hH.1.1.2
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let U := (conjugateSpanBy Z H).subgroupOf H
  have hU := hi.hstar_omega_orbit_reduced hH'
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  let α := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let Y := offenderSubgroup α
  change ∀ _hqs : IsQuasisimple (generalizedFitting Y),
    ∀ s : MovedSection (α.comp Y.subtype) (generalizedFitting Y), _
  intro hqs s e
  have hp := hi.hstar_minimal_parabolic hH'
  have hj := hi.hstar_thompson_moves_omega_orbit hH' hZH
  obtain ⟨p,hpSurj,hpk,f,hf,he,hfk⟩ :=
    quasisimple_five_whole_quotient S hp U hU hj q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) hqs s e
  have hpc : p.ker = pCore 2 H := hpk.trans
    (h.hstar_omega_orbit_centralizer_eq_core hout hH hZH)
  have hcon := ChapterC.SymmetricFive.source_natural_quotient_conclusions
    S hp U hU p hpSurj hpk f hf he hj hfk
  obtain ⟨a,ha⟩ := hcon.2.2.1
  have hD : (ChapterB.Offenders.D 5).map (MulAut.conj a).toMonoidHom ≤
      (S : Subgroup H).map p := ha ▸ map_mono (f := p) inf_le_left
  let B := M.subgroupOf H
  have hBmax : minimalParabolicMax S hp = B := h.intrinsic_maximal_eq_overlap hH hp
  have hBpre : B = (ChapterC.SymmetricFive.pointFour.map
      (MulAut.conj a).toMonoidHom).comap p := hBmax.symm.trans
    (ChapterC.SymmetricFive.source_maximal_preimage S hp p hpSurj a hD)
  have hBimage : B.map p = ChapterC.SymmetricFive.pointFour.map
      (MulAut.conj a).toMonoidHom := by rw [hBpre,map_comap_eq_self_of_surjective hpSurj]
  have hSB : (S : Subgroup H) ≤ B := fun _ hx => h.sylow_le hx
  have hindex : (S : Subgroup H).relIndex B = 3 :=
    sylow_overlap_index_three S p hpSurj (hpc ▸ pCore_isPGroup.le_sylow_of_normal S)
      B hSB a hBimage
  let ZH := Z.subgroupOf H
  let N := centralizer (ZH : Set H)
  have hZN : ZH ≤ U := fun _ hz => le_conjugateSpanBy Z H hz
  have hSN : (S : Subgroup H) ≤ N := by
    intro t ht z hz
    apply Subtype.ext
    exact (((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t ht).symm
  have hNB : N ≤ B := by
    intro x hx
    apply hstar_omega_centralizer_le_M hH hZH
    refine ⟨x.property,?_⟩
    intro z hz
    exact congrArg H.subtype (hx ⟨z,hH.1.1.2 ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1⟩ hz)
  have hne : N ≠ (S : Subgroup H) := by
    intro hNS
    exact ChapterB.not_marked_five_movedSection_of_seed U ZH q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
      hZN S hNS Y (generalizedFitting Y) s e
  have hNB_eq : N = B := by
    have hm := relIndex_mul_relIndex (S : Subgroup H) N B hSN hNB
    rw [hindex] at hm
    have hprime : ((S : Subgroup H).relIndex N * N.relIndex B).Prime := hm ▸ Nat.prime_three
    rcases Nat.prime_mul_iff.mp hprime with ⟨_,hrel⟩ | ⟨_,hrel⟩
    · exact le_antisymm hNB (relIndex_eq_one.mp hrel)
    · exact (hne (le_antisymm (relIndex_eq_one.mp hrel) hSN)).elim
  have heq : H ⊓ centralizer (Z : Set G) = H ⊓ M := by
    ext x
    constructor
    · rintro ⟨hx,hxz⟩
      refine ⟨hx,?_⟩
      have hxN : (⟨x,hx⟩ : H) ∈ N := fun z hz => Subtype.ext (hxz z hz)
      exact hNB hxN
    · rintro ⟨hx,hxm⟩
      refine ⟨hx,?_⟩
      have hxN : (⟨x,hx⟩ : H) ∈ N := hNB_eq.symm ▸ hxm
      intro z hz
      exact congrArg H.subtype (hxN ⟨z,hH.1.1.2 ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1⟩ hz)
  refine ⟨heq,p,hpc,hpSurj,a,hBimage,hcon.1.trans ha,hindex,?_⟩
  rw [←heq]
  exact h.hstar_omega_centralizer_normalizes hH
    (h.omega_natural_fixed_quotient_of_hstar_moves hout hH hZH) hZH

end CFSG.Quasithin.Chapter6.Source.Hypothesis611
