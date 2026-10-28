module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.Assembly.NormalizerSource
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.Assembly.RankTwoSource
public import CFSG.Quasithin.ChapterI.Section03.RankTwoSource.EarlierSources

/-!
# The ordinary representative component before proper-embedding analysis

The full source rank-two balance theorem constructs an ordinary normal
component of C_G(v) containing L. This construction uses the marked plane
normalizer and the original rank and odd-core hypotheses. It makes no
proper-embedding assertion; that independent step must retain this K.

Source: Aschbacher–Smith 15.3.38 p.1136 and I.3.1(3) pp.414–415.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.GlobalGeometry
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Rank-two balance alone constructs the actual ordinary normal envelope. -/
theorem representative_component_envelope_of_balance {κ : GroupClass.{u}}
    (balance : EarlierRankTwoBalance κ) (hG : IsSimpleQTKE κ G)
    (I L V : Subgroup G) [IsKleinFour V] [IsQuasisimple L]
    (hI : I = normalizer (V : Set G))
    (hIL : I ≤ normalizer (L : Set G))
    (hZ : (center L).map L.subtype = V)
    (hoL : pPrimeCore 2 L = ⊥) (hrank : primeRank 3 L = 2)
    (v : G) (hv : v ∈ V) (hv2 : orderOf v = 2) :
    let H := centralizer ({v} : Set G)
    ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧ L ≤ K.map H.subtype := by
  let H := centralizer ({v} : Set G)
  have hH := hG.involution_centralizer_sqtk hv2
  have hVH : V ≤ H := by
    intro w hw
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (IsKleinFour.isMulCommutative.is_comm.comm
        (⟨w, hw⟩ : V) ⟨v, hv⟩))
  have hLC : L ≤ centralizer (V : Set G) := by
    intro l hl w hw
    obtain ⟨z, hz, he⟩ := mem_map.mp (hZ.symm ▸ hw)
    have hc := congrArg Subtype.val (mem_center_iff.mp hz ⟨l, hl⟩)
    change (z : G) = w at he
    change l * (z : G) = (z : G) * l at hc
    rw [he] at hc
    exact hc.symm
  have hLH : L ≤ H := by
    intro l hl
    exact mem_centralizer_singleton_iff.mpr (hLC hl v hv).symm
  let A := L.subgroupOf H
  let Q := V.subgroupOf H
  let C := centralizer (Q : Set H)
  have hAC : A ≤ C := by
    intro a ha w hw
    exact Subtype.ext (hLC ha w hw)
  have hCI : C ≤ I.subgroupOf H := by
    intro a ha
    rw [hI]
    apply Subgroup.centralizer_le_normalizer
    intro w hw
    exact congrArg Subtype.val (ha ⟨w, hVH hw⟩ hw)
  have hCA : C ≤ normalizer (A : Set H) := by
    intro a ha
    apply mem_normalizer_iff.mpr
    intro l
    exact mem_normalizer_iff.mp (hIL (hCI ha)) l
  let B := A.subgroupOf C
  let e : B ≃* L := (subgroupOfEquivOfLe hAC).trans (subgroupOfEquivOfLe hLH)
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv e.symm
  let : B.Normal := normal_subgroupOf_of_le_normalizer hCA
  have hcomp : IsComponent C B := ⟨(inferInstance : B.Normal).isSubnormal, inferInstance⟩
  have hoB : pPrimeCore 2 B = ⊥ := by
    apply ((pPrimeCore 2 B).map_eq_bot_iff_of_injective (f := e.toMonoidHom) e.injective).mp
    rw [pPrimeCore_map_iso, hoL]
  have htwo : IsTwoComponent B := by
    refine ⟨component_isCComponent hcomp, ?_⟩
    exact IsQuasisimple.of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hoB).trans (QuotientGroup.quotientBot (G := B))).symm
  have hQ : IsPGroup 2 Q :=
    (IsPGroup.of_card (n := 2) (show Nat.card V = 2 ^ 2 by
      rw [IsKleinFour.card_four]; decide)).comap_subtype
  obtain ⟨K, hK, hn, hBK⟩ := balance H hH Q hQ B htwo
    ((primeRank_congr 3 e).trans hrank)
  have hAK : A ≤ K := by
    change (A.subgroupOf C).map C.subtype ≤ K at hBK
    rwa [map_subgroupOf_eq_of_le hAC] at hBK
  refine ⟨K, hK, hn, ?_⟩
  simpa only [A, map_subgroupOf_eq_of_le hLH] using map_mono (f := H.subtype) hAK

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.GlobalGeometry

namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
open LocalCover LocalCover.SourceBorel GlobalGeometry Chapter1 Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The actual source setup has its balanced representative envelope with
all earlier-source inputs discharged. -/
theorem LocalResult.representative_envelope_knownSimple
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) {d : CharacteristicTwo.LocalData G}
    (s : SourceInputs d) {I L : Subgroup G} (h : Setup d I L)
    (r : LocalResult d I L) (v : G) (hv : v ∈ r.cover.borel.W₁)
    (hv2 : orderOf v = 2) :
    let H := centralizer ({v} : Set G)
    ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧ L ≤ K.map H.subtype := by
  let V := r.cover.borel.W₁
  obtain ⟨i, hi⟩ := r.plane
  let : IsElementaryAbelian 2 V := d.action.elementary_of_le
    (by simpa only [V, hi] using d.action.plane_le i)
  let : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by
    change 1 < Nat.card r.cover.borel.W₁
    rw [hi, d.action.card_plane]; decide)
  let : IsKleinFour V := ⟨by simpa only [V, hi] using d.action.card_plane i,
    IsElementaryAbelian.exponent_eq_prime⟩
  let e := subgroupOfEquivOfLe h.component_le
  let : IsQuasisimple (L.subgroupOf I) := h.component.2
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv e
  have ho : pPrimeCore 2 L = ⊥ := by
    rw [← pPrimeCore_map_iso 2 e,
      component_oddCore_eq_bot h.component (s.earlier.odd I h.outside), Subgroup.map_bot]
  exact representative_component_envelope_of_balance
    (earlierRankTwoBalance_of_source ChapterI.RankTwoSource.earlierA36_knownSimple
      ChapterI.RankTwoSource.earlierA38_knownSimple
      (ChapterI.RankTwoSource.earlierOrbitProjection KnownSimple.IsKnownSimple))
    hG I L V (normalizer_eq_knownSimple hG s h r)
    (h.normalizes_component s.earlier) r.cover.center_plane ho h.component_rank v hv hv2

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
end
