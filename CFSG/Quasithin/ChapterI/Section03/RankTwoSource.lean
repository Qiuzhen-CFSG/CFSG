module

public import CFSG.Quasithin.ChapterI.Section03.RankTwoSource.Structure
public import CFSG.Quasithin.ChapterI.Section03.Balance
public import Theory.GroupTheory.PerfectCentralCoverPrimeRank
public import Theory.GroupTheory.GeneralizedFitting.TwoCoreImageComparison

/-!
# Rank-two two-component balance without a B₂ catalogue

The complete earlier A.3.6 alternatives first make the local two-component
quasisimple. Its nonzero GLS 5.22 projection to the central quotient of an
ambient component modulo O(H) is therefore a quasisimple image. Transfer for
perfect central covers preserves the rank-two lower bound. A.3.6 then makes
the pumpup ordinary, and A.3.8 makes it normal, collapsing its actual P-orbit.

The projection is the central-product projection of E(H/O(H)) onto the
simple central quotient of the selected component. Its restriction to L
is nonzero by the normal-closure equality in GLS II 5.22(i)-(ii): otherwise
its normal kernel contains that whole closure, hence the selected component,
contradicting surjectivity onto its nontrivial central quotient. Central
products do not in general project homomorphically to a covering component.

The earlier A.3 implications belong to `qt-a03-sqtk-structure`; the actual
orbit and nonzero projection belong to `qt-i-03-l-balance` (GLS II 5.22).
Every input remains explicit for final discharge by `qt-i-03`. No B₂
property, local quasisimplicity, or normal pumpup is an input.

Source: Aschbacher--Smith I.3.1(3), printed pp.414--415, A.3.6 and A.3.8.
-/

@[expose] public section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.ChapterI.RankTwoSource
universe u

/-- The orbit and nonzero projection consequences of GLS II 5.22. The
projection target is the central quotient of the image of J under the
literal quotient by O(H). This is the simple factor onto which a central
product canonically projects; no lift to the covering component is asserted.
Neither the seed's nor the projection image's quasisimplicity is assumed. -/
def EarlierOrbitProjection (κ : GroupClass.{u}) : Prop :=
  ∀ (H : Type u) [Group H] [Finite H], IsKGroup κ H →
    ∀ P : Subgroup H, IsPGroup 2 P →
      ∀ L : Subgroup (centralizer (P : Set H)), L.IsTwoComponent →
        ∃ J : Subgroup H, J.IsTwoComponent ∧
          componentOrbit (L.map (centralizer (P : Set H)).subtype) (oddELayer H) =
            componentOrbit J P ∧
          ∃ π : L →* (J.map (QuotientGroup.mk' (pPrimeCore 2 H)) ⧸
            center (J.map (QuotientGroup.mk' (pPrimeCore 2 H)))), π.range ≠ ⊥

/-! The following generic lemma is the corrected projection step used after
the ambient orbit has been constructed.  It deliberately targets the simple
central quotient of the orbit image, rather than a covering component. -/

theorem componentOrbit_centralQuotient_restriction_nontrivial
    {G : Type u} [Group G] [Finite G] {L A : Subgroup G}
    (hL : IsComponent G L) :
    ∃ π : L →* (componentOrbit L A ⧸ center (componentOrbit L A)),
      π.range ≠ ⊥ := by
  let E := componentOrbit L A
  let i : L →* E := inclusion (le_componentOrbit L A)
  let π : L →* (E ⧸ center E) :=
    (QuotientGroup.mk' (center E)).comp i
  let : IsQuasisimple L := hL.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial (L ⧸ center L) := IsSimpleGroup.toNontrivial
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  have hLbot : L ≠ ⊥ := (nontrivial_iff_ne_bot L).mp inferInstance
  have hEperfect : Group.IsPerfect E := hL.orbit_isPerfect A
  let : Group.IsPerfect E := hEperfect
  have hEnontrivial : Nontrivial E :=
    (Subgroup.inclusion_injective (le_componentOrbit L A)).nontrivial
  refine ⟨π, ?_⟩
  intro hπbot
  have hLcenterE : ∀ (x : G) (hx : x ∈ L),
      (i ⟨x, hx⟩ : E) ∈ center E := by
    intro x hx
    have hxrange : π ⟨x, hx⟩ ∈ π.range := ⟨⟨x, hx⟩, rfl⟩
    have hxbot : π ⟨x, hx⟩ ∈ (⊥ : Subgroup (E ⧸ center E)) := hπbot ▸ hxrange
    have hxone : π ⟨x, hx⟩ = 1 := Subgroup.mem_bot.mp hxbot
    change QuotientGroup.mk' (center E) (i ⟨x, hx⟩) = 1 at hxone
    exact (QuotientGroup.eq_one_iff _).mp hxone
  have hEZ : E ≤ (center E).map E.subtype := by
    unfold E componentOrbit
    apply iSup_le
    intro a z hz
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz
    have hnorm : (a : G) ∈ normalizer (E : Set G) :=
      le_normalizer_componentOrbit L A a.property
    let xE : E := ⟨x, le_componentOrbit L A hx⟩
    let zE : E := ⟨(a : G) * x * (a : G)⁻¹,
      (mem_normalizer_iff.mp hnorm x).mp xE.property⟩
    have hEconj : E.map (↑(MulAut.conj (a : G))) = E :=
      mem_normalizer_iff_map_conj_eq.mp hnorm
    let e0 := (MulAut.conj (a : G)).subgroupMap E
    let e : E ≃* E := e0.trans
      (MulEquiv.cast (M := fun H : Subgroup G => H) hEconj)
    have hxcenter : xE ∈ center E := by
      have hi : i ⟨x, hx⟩ = xE := by
        apply Subtype.ext
        rfl
      rw [← hi]
      exact hLcenterE x hx
    have hzcenter : zE ∈ center E := by
      have hecenter : e xE ∈ center E := by
        apply mem_center_iff.mpr
        intro y
        have hcomm := mem_center_iff.mp hxcenter (e.symm y)
        simpa only [map_mul, e.apply_symm_apply, e.symm_apply_apply] using congrArg e hcomm
      have heq : e xE = zE := by
        apply Subtype.ext
        change ((MulEquiv.cast (M := fun H : Subgroup G => H) hEconj) (e0 xE) : G) = _
        have hcast_val {H K : Subgroup G} (h : H = K) (x : H) :
            ((MulEquiv.cast (M := fun S : Subgroup G => S) h x : K) : G) = (x : G) := by
          subst K
          rfl
        rw [hcast_val]
        rfl
      simpa [heq] using hecenter
    change (E.subtype zE) ∈ (center E).map E.subtype
    exact mem_map_of_mem E.subtype hzcenter
  have hcenter_top : center E = ⊤ := by
    apply top_unique
    intro e he
    obtain ⟨z, hz, hze⟩ := Subgroup.mem_map.mp (hEZ e.property)
    have hze' : z = e := Subtype.ext hze
    simpa [hze'] using hz
  exact Group.IsPerfect.not_isMulCommutative E (center_eq_top_iff.mp hcenter_top)

/-- A nonzero projection of a quasisimple source is a perfect central
cover of its image; transfer retains the rank-two lower bound. -/
theorem projection_three_rank_ge_two {L Q : Type u} [Group L] [Finite L]
    [Group Q] [Finite Q] [IsQuasisimple L]
    (π : L →* Q) (hn : π.range ≠ ⊥) (hr : 2 ≤ primeRank 3 L) :
    IsQuasisimple π.range ∧ 2 ≤ primeRank 3 Q := by
  let : Nontrivial π.range := (nontrivial_iff_ne_bot _).mpr hn
  let : IsQuasisimple π.range := IsQuasisimple.of_surjective π.rangeRestrict
    π.rangeRestrict_surjective
  have hz := PerfectCentralCovering.two_le_primeRank_central_quotient (p := 3)
    (by decide) hr
  let e := IsQuasisimple.centralQuotientEquiv π.rangeRestrict π.rangeRestrict_surjective
  have hzR : 2 ≤ primeRank 3 (π.range ⧸ center π.range) := by
    rw [← primeRank_equiv 3 e]
    exact hz
  have hb : 2 ≤ primeRank 3 π.range := by
    by_contra h
    have hu := PrimeRank.le_of_surjective_of_source_le_one (by decide : 3 ≠ 2)
      (QuotientGroup.mk' (center π.range)) (QuotientGroup.mk'_surjective _)
      (by omega : primeRank 3 π.range ≤ 1)
    omega
  exact ⟨inferInstance, hb.trans
    (Theory.GroupTheory.primeRank_le_of_injective 3 π.range.subtype
      π.range.subtype_injective)⟩

/-- The exact rank-two source assertion I.3.1(3), conditional only on
the full genuine earlier source implications and their actual projection. -/
theorem lemma_I_3_1_three
    {H : Type u} [Group H] [Finite H] {κ : GroupClass.{u}}
    (hA36 : EarlierA36 κ) (hA38 : EarlierA38 κ)
    (hGLS : EarlierOrbitProjection κ) (hH : IsSQTK κ H)
    (P : Subgroup H) (hP : IsPGroup 2 P)
    (L : Subgroup (centralizer (P : Set H))) (hL : L.IsTwoComponent)
    (hr : primeRank 3 L = 2) :
    IsQuasisimple L ∧ ∃ J : Subgroup H, IsComponent H J ∧ J.Normal ∧
      L.map (centralizer (P : Set H)).subtype ≤ J := by
  have hLq := twoComponent_quasisimple_of_rank_two hA36
    (hH.subgroup (centralizer (P : Set H))) hL hr.ge
  let : IsQuasisimple L := hLq
  obtain ⟨J, hJ, horbit, π, hπ⟩ := hGLS H hH.isKGroup P hP L hL
  have hp := (projection_three_rank_ge_two π hπ hr.ge).2
  let Jbar := J.map (QuotientGroup.mk' (pPrimeCore 2 H))
  let qJ : J →* Jbar ⧸ center Jbar :=
    (QuotientGroup.mk' (center Jbar)).comp
      ((QuotientGroup.mk' (pPrimeCore 2 H)).subgroupMap J)
  have hqJ : Function.Surjective qJ :=
    (QuotientGroup.mk'_surjective (center Jbar)).comp
      ((QuotientGroup.mk' (pPrimeCore 2 H)).subgroupMap_surjective J)
  have hrJ : 2 ≤ primeRank 3 J := by
    by_contra hh
    have hl := PrimeRank.le_of_surjective_of_source_le_one (by decide : 3 ≠ 2)
      qJ hqJ
      (by omega : primeRank 3 J ≤ 1)
    change primeRank 3 (Jbar ⧸ center Jbar) ≤ primeRank 3 J at hl
    change 2 ≤ primeRank 3 (Jbar ⧸ center Jbar) at hp
    omega
  have hJq := twoComponent_quasisimple_of_rank_two hA36 hH hJ hrJ
  have hn := cComponent_normal_of_rank_two hA38 hH hJ.1 hrJ
  have hcollapse : componentOrbit J P ≤ J := by
    let := hn
    exact iSup_conjugates_le_of_le_normalizer J P J le_rfl
      (by rw [normalizer_eq_top]; exact le_top)
  refine ⟨hLq, J, ⟨hJ.1.subnormal, hJq⟩, hn, ?_⟩
  exact (le_componentOrbit (L.map (centralizer (P : Set H)).subtype) (oddELayer H)).trans
    (horbit.le.trans hcollapse)

end CFSG.Quasithin.ChapterI.RankTwoSource
