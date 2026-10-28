module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.QuotientAction
public import Theory.GroupTheory.InvolutionCentralizerControl
import Mathlib.Tactic.Group

/-!
# Lifting a point stabilizer across the source central line

For the literal conjugation action of H/O₂(H) on U/Z, with |Z| = 2,
a point moved by O₂(H) has its entire two-element fiber in one O₂(H)-orbit.
Thus a representative fixing its quotient point can be corrected by an
element of O₂(H) to centralize the original point. For an involution line,
this identifies its normalizer image with the quotient point stabilizer.

The movement hypothesis is essential and remains explicit. No normality of
Z in the ambient group is required; only the quotient inside U is used.
The whole quotient module and its original central kernel are retained.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the final
paragraph of the proof of 13.8.1, printed pp.968–969 (PDF pp.985–986).
-/

public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.A6Endgame.PointNormalizer
variable {G : Type*} [Group G] {H U Z : Subgroup G} [(Z.subgroupOf U).Normal]

@[expose] def pointStabilizer (a : SolvableExclusion.Five.StarAction H U Z) (u : U) :
    Subgroup (Source.Hstar H) :=
  (MulAction.stabilizer (MulAut (U ⧸ Z.subgroupOf U))
    (QuotientGroup.mk' (Z.subgroupOf U) u)).comap a.action

/-- Correcting by an element of the actual two-core lifts a quotient fixer. -/
theorem centralizer_image_eq_stabilizer
    (a : SolvableExclusion.Five.StarAction H U Z) (u : U)
    (hZ : Nat.card Z = 2) (hcomm : ⁅U, Source.QH H⁆ ≤ Z)
    (hm : ∃ n ∈ Source.QH H, n * (u : G) ≠ (u : G) * n) :
    Source.starImage H (centralizer ({(u : G)} : Set G)) = pointStabilizer a u := by
  let π := QuotientGroup.mk' (pCore 2 H)
  let q := QuotientGroup.mk' (Z.subgroupOf U)
  have fixes (h : H) : a.action (π h) (q u) = q
      ⟨(h : G) * (u : G) * (h : G)⁻¹,
        (mem_normalizer_iff.mp (a.normalizes h.property) u).mp u.property⟩ := a.conjugation h u
  apply le_antisymm
  · rintro x ⟨h, hh, rfl⟩
    change a.action (π h) (q u) = q u
    rw [fixes]
    congr 1
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hh)
  · intro x hx
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) x
    change a.action (π h) (q u) = q u at hx
    let v : U := ⟨(h : G) * (u : G) * (h : G)⁻¹,
      (mem_normalizer_iff.mp (a.normalizes h.property) u).mp u.property⟩
    have hqu : q v = q u := (fixes h).symm.trans hx
    have hz : (v : G) * (u : G)⁻¹ ∈ Z := by
      have he : q (v * u⁻¹) = 1 := by rw [map_mul, map_inv, hqu, mul_inv_cancel]
      exact (QuotientGroup.eq_one_iff (v * u⁻¹)).mp he
    by_cases hv : v = u
    · refine ⟨h, ?_, rfl⟩
      apply mem_centralizer_singleton_iff.mpr
      exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hv)
    · obtain ⟨n, hn, hnu⟩ := hm
      obtain ⟨n', hn', rfl⟩ := hn
      have hw : (n' : G) * (u : G) * (n' : G)⁻¹ * (u : G)⁻¹ ∈ Z := by
        exact hcomm (commutator_comm (U) (Source.QH H) ▸
          commutator_mem_commutator (mem_map_of_mem H.subtype hn') u.property)
      obtain ⟨z, hz1, huniq⟩ := (Nat.card_eq_two_iff' (1 : Z)).mp hZ
      have hdiff : (⟨(v : G) * (u : G)⁻¹, hz⟩ : Z) ≠ 1 := by
        intro he
        exact hv (Subtype.ext (mul_inv_eq_one.mp (congrArg Subtype.val he)))
      have hwdiff : (⟨(n' : G) * (u : G) * (n' : G)⁻¹ * (u : G)⁻¹, hw⟩ : Z) ≠ 1 := by
        intro he
        exact hnu (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp (congrArg Subtype.val he)))
      have he := congrArg Subtype.val ((huniq _ hdiff).trans (huniq _ hwdiff).symm)
      have he' : (h : G) * (u : G) * (h : G)⁻¹ =
          (n' : G) * (u : G) * (n' : G)⁻¹ := mul_right_cancel he
      refine ⟨n'⁻¹ * h, ?_, ?_⟩
      · apply mem_centralizer_singleton_iff.mpr
        change ((n' : G)⁻¹ * (h : G)) * (u : G) = (u : G) * ((n' : G)⁻¹ * (h : G))
        have hc : ((n' : G)⁻¹ * (h : G)) * (u : G) * ((n' : G)⁻¹ * (h : G))⁻¹ = (u : G) := by
          calc
            _ = (n' : G)⁻¹ * ((h : G) * (u : G) * (h : G)⁻¹) * (n' : G) := by group
            _ = (u : G) := by rw [he']; group
        exact mul_inv_eq_iff_eq_mul.mp hc
      · change π (n'⁻¹ * h) = π h
        rw [map_mul, map_inv, show π n' = 1 from (QuotientGroup.eq_one_iff _).mpr hn', inv_one, one_mul]

/-- The order-two line has the same normalizer as its nonidentity point's
centralizer. This avoids an assumption of normality in the ambient group. -/
theorem normalizer_eq_point_centralizer (A : Subgroup G) (hA : Nat.card A = 2)
    (u : G) (hu : u ∈ A) (hu1 : u ≠ 1) :
    normalizer (A : Set G) = centralizer ({u} : Set G) := by
  obtain ⟨z, _, hz⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hA
  have hall (x : G) (hx : x ∈ A) : x = 1 ∨ x = u := by
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · exact Or.inr (congrArg Subtype.val
        ((hz ⟨x, hx⟩ (fun h => hx1 (congrArg Subtype.val h))).trans
          (hz ⟨u, hu⟩ (fun h => hu1 (congrArg Subtype.val h))).symm))
  apply le_antisymm
  · exact (normalizer_le_centralizer_of_card_two A hA).trans
      (centralizer_le (Set.singleton_subset_iff.mpr hu))
  · intro g hg
    apply centralizer_le_normalizer (A : Set G)
    intro x hx
    rcases hall x hx with rfl | rfl
    · simp only [one_mul, mul_one]
    · exact (mem_centralizer_singleton_iff.mp hg).symm

/-- The source point-normalizer equality uses the actual quotient map and
conjugation action, without replacing the full quotient by its duad orbit. -/
theorem normalizer_image_eq_stabilizer
    (a : SolvableExclusion.Five.StarAction H U Z) (A : Subgroup G)
    (hA : Nat.card A = 2) (u : U) (hu : (u : G) ∈ A) (hu1 : (u : G) ≠ 1)
    (hZ : Nat.card Z = 2) (hcomm : ⁅U, Source.QH H⁆ ≤ Z)
    (hm : ∃ n ∈ Source.QH H, n * (u : G) ≠ (u : G) * n) :
    Source.starImage H (normalizer (A : Set G)) = pointStabilizer a u := by
  rw [normalizer_eq_point_centralizer A hA u hu hu1]
  exact centralizer_image_eq_stabilizer a u hZ hcomm hm

end CFSG.Quasithin.Chapter13.Section08.A6Endgame.PointNormalizer
