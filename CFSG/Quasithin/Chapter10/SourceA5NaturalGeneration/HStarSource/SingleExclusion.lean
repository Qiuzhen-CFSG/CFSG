module
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.HStarSource.AlphaFields
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.SourceBorelDivisors
/-!
# Excluding the single field-sixteen HStar source

The selected single source has normal SL2(16) layer. The normalizer of its
layer Sylow is proper and contains the whole quotient Sylow, even in a
semilinear extension. Its inverse image lies in the original maximal-local
overlap by HStar minimality. The layer Borel forces five to divide the
order of that overlap, contradicting its actual odd Hall three-group.
Thus the same genuine source is paired of field order four. The paired
Borel also forces nine to divide the same actual Hall subgroup's order.

Source: Aschbacher--Smith 10.2.3(4), printed p.746.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterE ChapterE.ThompsonAction ChapterB ChapterB.SourceInduction
open ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
set_option backward.isDefEq.respectTransparency false

omit [Finite G] in
private theorem hstar_proper_overgroup_le_overlap
    {M H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (J : Subgroup H) (hSJ : (T.subtype hH.1.1.2 : Subgroup H) ≤ J) (hJ : J ≠ ⊤) :
    J ≤ M.subgroupOf H := by
  have hTJ : (T : Subgroup G) ≤ J.map H.subtype := by
    have hh := map_mono (f := H.subtype) hSJ
    change ((T : Subgroup G).subgroupOf H).map H.subtype ≤ J.map H.subtype at hh
    rwa [map_subgroupOf_eq_of_le hH.1.1.2] at hh
  have hJH : J.map H.subtype < H := by
    have hh := (map_lt_map_iff_of_injective H.subtype_injective).mpr (lt_top_iff_ne_top.mpr hJ)
    change J.map H.subtype < (⊤ : Subgroup H).map H.subtype at hh
    simpa only [← MonoidHom.range_eq_map,range_subtype] using hh
  exact map_le_iff_le_comap.mp (Chapter3.HStar.proper_overgroup_le T hH hTJ hJH)

/-- The actual paired field-four source forces nine into its actual odd Hall. -/
theorem source_hstar_paired_nine_dvd_hall
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (B : Subgroup H) (hBM : B ≤ D.maximalLocal.subgroupOf H)
    (hHall : IsHallSubgroup {p : Nat.Primes | p.val ≠ 2}
      (B.subgroupOf (D.maximalLocal.subgroupOf H))) :
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
    letI := (source_hstar_omega_orbit_reduced D hH).normal
    letI := (source_hstar_omega_orbit_reduced D hH).elementary
    let C := centralizer (U : Set H)
    let q := QuotientGroup.mk' C
    let hq := QuotientGroup.mk'_surjective C
    let hk := QuotientGroup.ker_mk' C
    let α := NormalElementaryQuotient.representation U q hq hk
    let Y := offenderSubgroup α
    ∀ (d : SourceTwoFactorCase (α.comp Y.subtype)) (K : BinaryField)
      (_hK : Nat.card K.Carrier = 4) (_c : d.MarkedProduct (linearNatural K 2)),
      9 ∣ Nat.card B := by
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
  have hU := source_hstar_omega_orbit_reduced D hH
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = centralizer (U : Set H) := QuotientGroup.ker_mk' C
  dsimp only
  intro d K hK c
  have hd := paired_linear_borel_odd_square_dvd_of_proper_overgroups
    (T.subtype hH.1.1.2) U q hq hk d K c
    (D.maximalLocal.subgroupOf H) (hstar_proper_overgroup_le_overlap hH)
  rw [hK] at hd
  norm_num at hd
  have h9 := nine_dvd_odd_hall_card_of_dvd_card _ hHall hd
  rwa [Nat.card_congr (subgroupOfEquivOfLe hBM).toEquiv] at h9

variable {H : Subgroup G}
variable {F : Type*} [Field F] [CharP F 2]
local instance hstarSingleExclusionAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2
variable
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G),H⁆ ≠ ⊥)
    (hF : Nat.card F = 4)
    (f : alternatingGroup (Fin 5) ≃* SL(2,F))
    (n : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (SL2.BinarySmall.natural.comp
        (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))))

include e hn hH hZH hF f n

theorem source_hstar_paired_four_of_three_hall
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (hzH : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (H : Set G) = ⊥)
    (B : Subgroup H) (hBM : B ≤ D.maximalLocal.subgroupOf H)
    (hHall : IsHallSubgroup {p : Nat.Primes | p.val ≠ 2}
      (B.subgroupOf (D.maximalLocal.subgroupOf H)))
    (hB : IsPGroup 3 B)
    (hlarge : 1 < generationParameter H)
    (hCZ : centralizer ((omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H : Set H) =
      (T.subtype hH.1.1.2 : Subgroup H)) :
    let S := T.subtype hH.1.1.2
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
    letI := (source_hstar_omega_orbit_reduced D hH).normal
    letI := (source_hstar_omega_orbit_reduced D hH).elementary
    let C := centralizer (U : Set H)
    let q := QuotientGroup.mk' C
    let hq := QuotientGroup.mk'_surjective C
    let hk := QuotientGroup.ker_mk' C
    let α := NormalElementaryQuotient.representation U q hq hk
    let Y := offenderSubgroup α
    let σ := α.comp Y.subtype
    letI := offenderSubgroup_normal α
    ∃ (d : SourceTwoFactorCase σ) (K : BinaryField),
        Nat.card K.Carrier = 4 ∧ Nonempty (d.MarkedProduct (linearNatural K 2)) ∧
        ∃ t : S.mapSurjective hq,
          d.first.map (MulAut.conjNormal (t : H ⧸ C)).toMonoidHom = d.second ∧
          d.second.map (MulAut.conjNormal (t : H ⧸ C)).toMonoidHom = d.first := by
  let S := T.subtype hH.1.1.2
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
  have hU := source_hstar_omega_orbit_reduced D hH
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = centralizer (U : Set H) := QuotientGroup.ker_mk' C
  rcases source_hstar_linear_field_alternatives D e hn hH hZH hF f n hz hzH hlarge hCZ with
    ⟨_,c,K,hK,hlinear⟩ | hp
  · have hd := quasisimple_linear_borel_card_dvd_of_proper_overgroups S U q hq hk c.sectionData K
      hlinear (D.maximalLocal.subgroupOf H) (hstar_proper_overgroup_le_overlap hH)
    rw [hK] at hd
    have h5 : 5 ∣ Nat.card (D.maximalLocal.subgroupOf H) := (by decide : 5 ∣ 16*(16-1)).trans hd
    have hBsub : IsPGroup 3 (B.subgroupOf (D.maximalLocal.subgroupOf H)) :=
      hB.of_equiv (subgroupOfEquivOfLe hBM).symm
    exact (five_not_dvd_card_of_odd_three_hall _ hHall hBsub h5).elim
  · exact hp

theorem source_hstar_three_hall_nine_dvd
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (hzH : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (H : Set G) = ⊥)
    (B : Subgroup H) (hBM : B ≤ D.maximalLocal.subgroupOf H)
    (hHall : IsHallSubgroup {p : Nat.Primes | p.val ≠ 2}
      (B.subgroupOf (D.maximalLocal.subgroupOf H)))
    (hB : IsPGroup 3 B)
    (hlarge : 1 < generationParameter H)
    (hCZ : centralizer ((omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H : Set H) =
      (T.subtype hH.1.1.2 : Subgroup H)) : 9 ∣ Nat.card B := by
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
  have hU := source_hstar_omega_orbit_reduced D hH
  let := hU.normal
  let := hU.elementary
  obtain ⟨d,K,hK,⟨c⟩,_⟩ := source_hstar_paired_four_of_three_hall D e hn hH hZH hF f n
    hz hzH B hBM hHall hB hlarge hCZ
  exact source_hstar_paired_nine_dvd_hall D hH B hBM hHall d K hK c

theorem source_hstar_three_hall_card_nine
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (hzH : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (H : Set G) = ⊥)
    (B : Subgroup H) (hBM : B ≤ D.maximalLocal.subgroupOf H)
    (hHall : IsHallSubgroup {p : Nat.Primes | p.val ≠ 2}
      (B.subgroupOf (D.maximalLocal.subgroupOf H)))
    (hB : IsPGroup 3 B)
    (hlarge : 1 < generationParameter H)
    (hCZ : centralizer ((omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H : Set H) =
      (T.subtype hH.1.1.2 : Subgroup H))
    (C : Subgroup G) (hBC : B.map H.subtype ≤ C) (hC : Nat.card C = 9) :
    Nat.card B = 9 := by
  have h9 := source_hstar_three_hall_nine_dvd D e hn hH hZH hF f n
    hz hzH B hBM hHall hB hlarge hCZ
  have hB9 : Nat.card B ∣ 9 := by
    rw [←hC,←card_map_of_injective (K := B) H.subtype_injective]
    exact card_dvd_of_le hBC
  exact Nat.dvd_antisymm hB9 h9

theorem source_hstar_three_hall_eq_torus
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (hzH : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (H : Set G) = ⊥)
    (B : Subgroup H) (hBM : B ≤ D.maximalLocal.subgroupOf H)
    (hHall : IsHallSubgroup {p : Nat.Primes | p.val ≠ 2}
      (B.subgroupOf (D.maximalLocal.subgroupOf H)))
    (hB : IsPGroup 3 B)
    (hlarge : 1 < generationParameter H)
    (hCZ : centralizer ((omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H : Set H) =
      (T.subtype hH.1.1.2 : Subgroup H))
    (C : Subgroup G) (hBC : B.map H.subtype ≤ C) (hC : Nat.card C = 9) :
    B.map H.subtype = C := by
  apply eq_of_le_of_card_ge hBC
  rw [card_map_of_injective H.subtype_injective,
    source_hstar_three_hall_card_nine D e hn hH hZH hF f n
      hz hzH B hBM hHall hB hlarge hCZ C hBC hC,hC]

end CFSG.Quasithin.Chapter10
