module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.NormalizerChiefBound
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.LocalResidual
public import Theory.GroupTheory.PResidual.CubicSectionCentralizer

/-!
# The first centralizer conclusion of Goldschmidt (5.3)

The maximal local normalizer has two-residual C3 or A4. The literal inclusion
of the original local normalizer therefore bounds its residual order by a
divisor of twelve. If its quotient by the track fixer has a nonnormal Sylow
three-subgroup, the residual centralizer theorem forces every cubic subgroup
to centralize that fixer. Local transitivity supplies a cubic subgroup and
gives the source conclusion that the vertex centralizer has order divisible
by three.

The earlier graph argument owns nonnormality of the Sylow three-subgroup in
the displayed quotient. All normalizer containments, maximality choices,
local classification hypotheses and original ambient inclusions are supplied
here. The ambient completion need not be finite.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (5.3),
printed p.395, first conclusion, using (5.2) and (2.14).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

/-- Restricting a subgroup to any of its local normalizers gives a normal
subgroup, even when the ambient completion is infinite. -/
instance localNormalizer_subgroupOf_normal (Q : Subgroup G) (i : Bool) :
    (Q.subgroupOf (localNormalizer F Q i)).Normal := by
  refine ⟨?_⟩
  intro x hx g
  change (g : G) * (x : G) * (g : G)⁻¹ ∈ Q
  exact (Subgroup.mem_normalizer_iff.mp g.property.1 (x : G)).mp hx

/-- The residual order bound passes from the chosen maximal normalizer to
the actual candidate using its literal inclusion. -/
theorem NormalizerCandidate.local_residual_card_dvd_twelve
    (h : CubicTreeAction F) {Q : Subgroup G} (hQ : NormalizerCandidate F Q) :
    Nat.card (pResidual 2 (localNormalizer F Q false)) ∣ 12 := by
  obtain ⟨R, hR, hQR⟩ := h.exists_maximalNormalizerCandidate hQ
  let H := localNormalizer F Q false
  let M := localNormalizer F R false
  let : Finite H := h.finite_localNormalizer Q false
  let : Finite M := h.finite_localNormalizer R false
  let i : H →* M := Subgroup.inclusion hQR
  have hd : Nat.card (pResidual 2 H) ∣ Nat.card (pResidual 2 M) := by
    have hd := Subgroup.card_dvd_of_le (Subgroup.map_pResidual_le 2 i)
    rwa [Subgroup.card_map_of_injective (Subgroup.inclusion_injective hQR)] at hd
  obtain ⟨P, _, ⟨e⟩, hP⟩ := hR.local_pushingUp_input h
  rcases local_residual_cubic_or_alternatingFour e P hP with hC | hA
  · obtain ⟨ec⟩ := hC
    have hc : Nat.card (pResidual 2 M) = 3 := by
      rw [Nat.card_congr ec.toEquiv]
      simp
    exact hd.trans (by rw [hc]; decide)
  · obtain ⟨ea⟩ := hA
    have hc : Nat.card (pResidual 2 M) = 12 := by
      rw [Nat.card_congr ea.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      rfl
    exact hd.trans (by rw [hc])

/-- Every supplied cubic subgroup of the actual local normalizer centralizes
the original fixer, under the earlier nonnormal quotient-Sylow conclusion. -/
theorem NormalizerCandidate.cubic_centralizes_of_quotient_not_three_closed
    (h : CubicTreeAction F) {Q : Subgroup G} (hQ : NormalizerCandidate F Q)
    (P : Sylow 3 (localNormalizer F Q false ⧸
      Q.subgroupOf (localNormalizer F Q false)))
    (hP : ¬ (P : Subgroup (localNormalizer F Q false ⧸
      Q.subgroupOf (localNormalizer F Q false))).Normal)
    (X : Subgroup (localNormalizer F Q false)) (hX : Nat.card X = 3) :
    X.map (localNormalizer F Q false).subtype ≤ centralizer (Q : Set G) := by
  let H := localNormalizer F Q false
  let : Finite H := h.finite_localNormalizer Q false
  have hQH : Q ≤ H := hQ.le_edge.trans (edgeNormalizer_le_local Q false)
  have hQ2 : IsPGroup 2 Q := h.primitive.sylow.isPGroup.to_le hQ.le_overlap
  have hc := cubic_le_centralizer_of_nonNormal_three_quotient
    (Q.subgroupOf H) hQ2.comap_subtype
    (hQ.local_residual_card_dvd_twelve h) P hP X hX
  rintro _ ⟨x, hx, rfl⟩ y hy
  exact congrArg Subtype.val (hc hx ⟨y, hQH hy⟩ hy)

/-- Goldschmidt (5.3)'s first conclusion on the literal vertex centralizer.
The nonnormal Sylow premise is supplied by the preceding track-quotient
regularity argument; there is no additional local classification premise. -/
theorem NormalizerCandidate.three_dvd_card_centralizer
    (h : CubicTreeAction F) {Q : Subgroup G} (hQ : NormalizerCandidate F Q)
    (P : Sylow 3 (localNormalizer F Q false ⧸
      Q.subgroupOf (localNormalizer F Q false)))
    (hP : ¬ (P : Subgroup (localNormalizer F Q false ⧸
      Q.subgroupOf (localNormalizer F Q false))).Normal) :
    3 ∣ Nat.card ((centralizer (Q : Set G)).subgroupOf (F false)) := by
  let H := localNormalizer F Q false
  let : Finite H := h.finite_localNormalizer Q false
  let : Finite (F false) := h.finite false
  have hd : 3 ∣ Nat.card H := by
    rw [← hQ.left_index]
    exact ((F false ⊓ F true).subgroupOf H).index_dvd_card
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := H) 3 hd
  have hX : Nat.card (zpowers x) = 3 := by rw [Nat.card_zpowers, hx]
  have hc := hQ.cubic_centralizes_of_quotient_not_three_closed h P hP (zpowers x) hX
  let i : H →* F false := Subgroup.inclusion inf_le_right
  have hle : (zpowers x).map i ≤ (centralizer (Q : Set G)).subgroupOf (F false) := by
    rintro _ ⟨y, hy, rfl⟩
    exact hc (Subgroup.mem_map_of_mem H.subtype hy)
  have hcard : Nat.card ((zpowers x).map i) = 3 := by
    have hi : Function.Injective i := Subgroup.inclusion_injective
      (show H ≤ F false from inf_le_right)
    rw [Subgroup.card_map_of_injective hi, hX]
  exact hcard ▸ Subgroup.card_dvd_of_le hle

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
