module
public import Stellmacher.SectionTen.TenOneSmallCommonCoreElementary
public import Stellmacher.SectionTen.TenOneSmallNeighborhoodQuotient
public import Theory.GroupTheory.Commutator.CentralElementaryFourQuotient

/-!
# The fixed plane of a noncentral common-core point

In the small Section Ten configuration, every point of the literal common-core
subgroup W0 outside the middle center fixes exactly that middle center in the
terminal module. The companion theorem identifies the elements of square one
in its coset of the terminal module. Both retain the original embedded local
group, critical path, order-eight first module, and first SL2(2) quotient.

The common core is elementary of order eight, is normalized by the middle
stabilizer, and contains the central middle plane. If a point outside that
plane centralizes the terminal module, counting shows that all of W0 does.
Local transitivity carries this centralization to every neighboring module,
so W0 is central in their generated neighborhood U. The actual quotient U/W0
has order four and inherits exponent two from U/Zmiddle. A central elementary
four quotient forces the derived subgroup to have order at most two, whereas
the proved native derived subgroup is Zmiddle of order four. Thus the terminal
fixed subgroup is proper; its order-eight ambient module and contained plane
force it to be exactly Zmiddle. Finally two involutions have product of square
one exactly when they commute, giving the coset statement.

Source: Stellmacher (10.1)(a3)(11), Journal of Algebra 190 (1997), printed p.62
of `refs/files/stellmacher-n-group.pdf`. This proves the terminal fixed-plane
and involution-coset step without source-(10), a terminal-core model, or a
terminal residual-containment assumption.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_small_common_core_point_terminal_fixed
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (a : G)
    (ha : a ∈ NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓
      GeneratedNeighborhoodV ctx.Γ middle)
    (haZ : a ∉ ZAt ctx.Γ middle) :
    VAt ctx.Γ ctx.criticalPath.a' ⊓ Subgroup.centralizer ({a} : Set G) =
      ZAt ctx.Γ middle := by
  classical
  let Γ := ctx.Γ
  let U := GeneratedNeighborhoodV Γ middle
  let W0 := NeighborhoodQIntersection Γ (Neighborhood Γ middle) ⊓ U
  let Z := ZAt Γ middle
  let V := VAt Γ ctx.criticalPath.a'
  have hW0U : W0 ≤ U := inf_le_right
  obtain ⟨_,hfirst,hterminal,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hVU : V ≤ U := le_sSup ⟨_,(mem_neighborhood_iff_adjacent Γ).mpr hterminal,rfl⟩
  have hZV : Z ≤ V := nine_seven_neighbor_center_le_module Γ (Γ.adjacent_symm hterminal)
  have hZU : Z ≤ U := hZV.trans hVU
  have hZW0 : Z ≤ W0 := by
    refine le_inf ?_ hZU
    apply le_sInf
    rintro D ⟨neighbor,hneighbor,rfl⟩
    exact (nine_seven_neighbor_center_le_module Γ
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hneighbor))).trans
        (neighbor_join_le_core_of_length_gt_one Γ ctx.criticalPath
          (by rw [ctx.critical_length]; decide) neighbor)
  obtain ⟨hMW0,hW0el,hW0card⟩ := ten_one_small_common_core_elementary ctx middle hpath hsmall hmodel
  change GAt Γ middle ≤ Subgroup.normalizer (W0 : Set G) at hMW0
  change Nat.card W0 = 8 at hW0card
  have hZcard : Nat.card Z = 4 := (sectionTenOpeningData ctx middle hpath).center_card
  have hUcard : Nat.card U = 32 := ten_one_small_neighborhood_card ctx middle hpath hsmall
  have hZcentral : Z ≤ Subgroup.centralizer (U : Set G) := by
    change ZAt ctx.Γ middle ≤ Subgroup.centralizer (GeneratedNeighborhoodV ctx.Γ middle : Set G)
    rw [← ten_one_small_intersection ctx middle hpath hsmall]
    exact ten_one_common_intersection_centralizes ctx middle hpath
  have hZCV : Z ≤ Subgroup.centralizer (V : Set G) :=
    hZcentral.trans (Subgroup.centralizer_le hVU)
  have hVcard : Nat.card V = 8 := by
    obtain ⟨mover,hmove⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity
      middle ((mem_neighborhood_iff_adjacent Γ).mpr hfirst)
      ((mem_neighborhood_iff_adjacent Γ).mpr hterminal)
    change Nat.card (VAt Γ ctx.criticalPath.a') = 8
    rw [← hmove,VAt,v_act,Subgroup.card_map_of_injective (MulAut.conj (mover:G)⁻¹).injective]
    exact hsmall
  have hnot : ¬ V ≤ Subgroup.centralizer ({a} : Set G) := by
    intro hfixed
    have haCV : a ∈ Subgroup.centralizer (V : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact Subgroup.mem_centralizer_singleton_iff.mp (hfixed hv)
    let L := W0 ⊓ Subgroup.centralizer (V : Set G)
    have hZL : Z ≤ L := le_inf hZW0 hZCV
    have haL : a ∈ L := ⟨ha,haCV⟩
    have hLbound : Nat.card L ≤ 8 :=
      (Subgroup.card_le_of_le (show L ≤ W0 from inf_le_left)).trans_eq hW0card
    have hLne : Nat.card L ≠ 4 := by
      intro hfour
      have heq : Z = L := Subgroup.eq_of_le_of_card_ge hZL (by rw [hZcard,hfour])
      apply haZ
      change a ∈ Z
      rw [heq]
      exact haL
    have hLdiv := Subgroup.card_dvd_of_le hZL
    rw [hZcard] at hLdiv
    obtain ⟨factor,hfactor⟩ := hLdiv
    have hLpos := Nat.card_pos (α:=L)
    have hLcard : Nat.card L = 8 := by omega
    have hW0L : W0 ≤ L := (Subgroup.eq_of_le_of_card_ge
      (show L ≤ W0 from inf_le_left) (by rw [hW0card,hLcard])).ge
    have hW0V : W0 ≤ Subgroup.centralizer (V : Set G) := hW0L.trans inf_le_right
    have hall (neighbor : Γ.Vertex) (hneighbor : neighbor ∈ Neighborhood Γ middle) :
        W0 ≤ Subgroup.centralizer (VAt Γ neighbor : Set G) := by
      obtain ⟨mover,hmove⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity
        middle ((mem_neighborhood_iff_adjacent Γ).mpr hterminal) hneighbor
      have hnorm := Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (hMW0 ((GAt Γ middle).inv_mem mover.property))
      change W0.map (MulAut.conj (mover:G)⁻¹).toMonoidHom = W0 at hnorm
      have hmap := (Subgroup.map_mono (f:=(MulAut.conj (mover:G)⁻¹).toMonoidHom) hW0V).trans
        (Subgroup.map_centralizer_le_centralizer_image _ _)
      rw [hnorm] at hmap
      have hv : VAt Γ neighbor = V.map (MulAut.conj (mover:G)⁻¹).toMonoidHom := by
        rw [← hmove]
        exact v_act Γ mover ctx.criticalPath.a'
      change W0 ≤ Subgroup.centralizer (V.map (MulAut.conj (mover:G)⁻¹).toMonoidHom : Set G) at hmap
      rwa [← hv] at hmap
    have hW0Ucent : W0 ≤ Subgroup.centralizer (U : Set G) := by
      apply Subgroup.le_centralizer_iff.mpr
      apply sSup_le
      rintro D ⟨neighbor,hneighbor,rfl⟩
      exact Subgroup.le_centralizer_iff.mp (hall neighbor hneighbor)
    let N := W0.subgroupOf U
    have hNcenter : N ≤ Subgroup.center U := by
      intro n hn
      rw [Subgroup.mem_center_iff]
      intro u
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp (hW0Ucent hn) u u.property
    let _ : N.Normal := Subgroup.normal_subgroupOf_of_le_normalizer
      ((Subgroup.le_centralizer_iff.mp hW0Ucent).trans (Subgroup.centralizer_le_normalizer _))
    have hderived : (commutator U).map U.subtype = Z :=
      (ten_one_small_derived ctx middle hpath hsmall).trans
        (ten_one_small_intersection ctx middle hpath hsmall)
    have hnative : commutator U ≤ N := by
      intro u hu
      apply hZW0
      rw [← hderived]
      exact Subgroup.mem_map_of_mem U.subtype hu
    let _ : IsMulCommutative (U ⧸ N) :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hnative
    obtain ⟨hNZ,hquot,_⟩ := ten_one_small_neighborhood_quotient_elementary ctx middle hpath hsmall
    let _ := hNZ
    let _ := hquot
    let _ : IsElementaryAbelian 2 (U ⧸ N) := ⟨by
      apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      intro q
      obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective N q
      rw [← map_pow]
      apply (QuotientGroup.eq_one_iff _).mpr
      have hz : u^2 ∈ Z.subgroupOf U := by
        apply (QuotientGroup.eq_one_iff _).mp
        change (QuotientGroup.mk' (Z.subgroupOf U)) (u^2) = 1
        rw [map_pow]
        exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 (U ⧸ Z.subgroupOf U)) _
      exact hZW0 hz⟩
    have hquotCard : Nat.card (U ⧸ N) = 4 := by
      have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup N
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW0U).toEquiv,hW0card,hUcard] at hc
      omega
    have hbound := card_commutator_le_two_of_central_elementary_four_quotient N hNcenter hquotCard
    have hderivedCard : Nat.card (commutator U) = 4 := by
      rw [← Subgroup.card_map_of_injective U.subtype_injective,hderived,hZcard]
    omega
  let C := V ⊓ Subgroup.centralizer ({a} : Set G)
  have hZC : Z ≤ C := by
    refine le_inf hZV ?_
    intro z hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (hZcentral hz) a (hW0U ha)).symm
  have hCsmall : Nat.card C < 8 := by
    rw [← hVcard]
    apply lt_of_le_of_ne (Subgroup.card_le_of_le inf_le_left)
    intro heq
    exact hnot ((Subgroup.eq_of_le_of_card_ge inf_le_left heq.ge).ge.trans inf_le_right)
  have hdiv := Subgroup.card_dvd_of_le hZC
  rw [hZcard] at hdiv
  obtain ⟨factor,hfactor⟩ := hdiv
  exact (Subgroup.eq_of_le_of_card_ge hZC (by rw [hZcard]; omega)).symm

public theorem ten_one_small_common_core_coset_square_eq_one_iff
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (a : G)
    (ha : a ∈ NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓
      GeneratedNeighborhoodV ctx.Γ middle)
    (haZ : a ∉ ZAt ctx.Γ middle)
    (v : G) (hv : v ∈ VAt ctx.Γ ctx.criticalPath.a') :
    (a * v)^2 = 1 ↔ v ∈ ZAt ctx.Γ middle := by
  let W0 := NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓
    GeneratedNeighborhoodV ctx.Γ middle
  let _ : IsElementaryAbelian 2 W0 :=
    (ten_one_small_common_core_elementary ctx middle hpath hsmall hmodel).2.1
  have ha2 : a^2=1 := elemPow_eq_one_of_isElementaryAbelian (p:=2) (A:=W0) a ha
  let _ : IsElementaryAbelian 2 (VAt ctx.Γ ctx.criticalPath.firstStep) :=
    ((lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq).longer_case
      (by rw [ctx.critical_length]; decide)).1
  obtain ⟨_,hfirst,hterminal,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  obtain ⟨mover,hmove⟩ := (lemma_seven_one ctx.sectionSeven ctx.Γ).local_transitivity
    middle ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst)
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hterminal)
  let _ : IsElementaryAbelian 2 (VAt ctx.Γ ctx.criticalPath.a') := by
    rw [← hmove,VAt,v_act]
    exact IsElementaryAbelian.map _
  have hv2 : v^2=1 := elemPow_eq_one_of_isElementaryAbelian (p:=2)
    (A:=VAt ctx.Γ ctx.criticalPath.a') v hv
  have hai : a⁻¹=a := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using ha2)
  have hvi : v⁻¹=v := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hv2)
  have hcomm : (a*v)^2=1 ↔ v ∈ Subgroup.centralizer ({a}:Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have hh := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using h)
      simpa only [mul_inv_rev,hai,hvi] using hh
    · intro h
      rw [(show Commute a v from h.symm).mul_pow,ha2,hv2,mul_one]
  have hfixed := ten_one_small_common_core_point_terminal_fixed ctx middle hpath hsmall hmodel a ha haZ
  constructor
  · intro h
    rw [← hfixed]
    exact ⟨hv,hcomm.mp h⟩
  · intro h
    have hh : v ∈ VAt ctx.Γ ctx.criticalPath.a' ⊓ Subgroup.centralizer ({a}:Set G) := by
      rw [hfixed]
      exact h
    exact hcomm.mpr hh.2

end Stellmacher.SectionTen
