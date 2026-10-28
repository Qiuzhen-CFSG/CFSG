module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Fusion
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.CenterTwoCoreSylowPromotion
public import Theory.GroupTheory.PGroup.ExtraspecialThirtyTwoElementaryAlternative

/-!
# Elementary fusion intersections and the ambient Sylow subgroup

The centers of the two conjugate extraspecial cores are distinct involution
lines. Every square in their intersection lies in both lines, so the literal
intersection is elementary abelian, and its order is at most eight. Separately,
self-centralization of the generalized Fitting subgroup and its center of
order two promote every Sylow two-subgroup of H to an ambient Sylow subgroup.
Consequently H has odd index in G. Neither assertion requires a choice of
representative for the fused involution or the nonnormal quaternion case.

These are parts of Aschbacher, “A 2-local characterization of M12”, Illinois
J. Math. 47 (2003), Lemma 2.4 and the Sylow argument opening Section 3,
pp.34 and 36. The order-eight lower bound and normality in H are separate
source steps; they are not asserted here.
-/

namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition

open Subgroup

variable {G : Type*} [Group G] [Finite G] {z : G}

private theorem mem_involution_line {x w : G} (hw : orderOf w = 2)
    (hx : x ∈ zpowers w) : x = 1 ∨ x = w := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, hw] at hx
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
  have hnlt : n < 2 := Finset.mem_range.mp hn
  interval_cases n <;> simp

/-- A square in the ambient core is either the identity or the marked involution. -/
public theorem core_square_eq_one_or_involution (h : Hypotheses z)
    {x : G} (hx : x ∈ coreInG z) : x ^ 2 = 1 ∨ x ^ 2 = z := by
  let : IsExtraspecial 2 (coreInG z) := h.coreInG_extraspecial
  apply mem_involution_line h.involution
  rw [← h.coreInG_center_image]
  exact ⟨(⟨x, hx⟩ : coreInG z) ^ 2, IsExtraspecial.square_mem_center _, rfl⟩

/-- Distinct center lines force exponent two in the actual intersection. -/
public theorem coreIntersection_square (h : Hypotheses z) (g : G)
    (hg : g * z * g⁻¹ ≠ z) {x : G} (hx : x ∈ coreIntersection z g) :
    x ^ 2 = 1 := by
  rcases core_square_eq_one_or_involution h hx.1 with hx1 | hxz
  · exact hx1
  obtain ⟨y, hy, hyx⟩ := hx.2
  change (MulAut.conj g) y = x at hyx
  rcases core_square_eq_one_or_involution h hy with hy1 | hyz
  · calc
      x ^ 2 = (MulAut.conj g) (y ^ 2) := by rw [← hyx, map_pow]
      _ = 1 := by rw [hy1, map_one]
  · exfalso
    apply hg
    calc
      g * z * g⁻¹ = (MulAut.conj g) (y ^ 2) := by rw [hyz]; rfl
      _ = x ^ 2 := by rw [map_pow, hyx]
      _ = z := hxz

/-- The elementary-abelian part of source 2.4, for the given conjugator. -/
public theorem coreIntersection_elementary (h : Hypotheses z) (g : G)
    (hg : g * z * g⁻¹ ≠ z) : IsElementaryAbelian 2 (coreIntersection z g) := by
  have hs (x : coreIntersection z g) : x ^ 2 = 1 :=
    Subtype.ext (coreIntersection_square h g hg x.property)
  have hi (x : coreIntersection z g) : x⁻¹ = x :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hs x)
  refine { toIsMulCommutative := ⟨⟨fun x y => ?_⟩⟩
           exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }
  calc
    x * y = (x * y)⁻¹ := (hi _).symm
    _ = y * x := by rw [mul_inv_rev, hi, hi]

/-- The extraspecial rank bound applies to this literal intersection. -/
public theorem coreIntersection_card_le_eight (h : Hypotheses z) (g : G)
    (hg : g * z * g⁻¹ ≠ z) : Nat.card (coreIntersection z g) ≤ 8 := by
  let E := coreIntersection z g
  let Q := coreInG z
  let : IsExtraspecial 2 Q := h.coreInG_extraspecial
  let : IsElementaryAbelian 2 E := coreIntersection_elementary h g hg
  let : IsElementaryAbelian 2 (E.subgroupOf Q) :=
    IsElementaryAbelian.subgroupOf (coreIntersection_le z g)
  have hc := IsExtraspecial.elementary_card_le_eight_of_card_thirty_two
    h.coreInG_card (E.subgroupOf Q)
  rwa [Nat.card_congr (subgroupOfEquivOfLe (coreIntersection_le z g)).toEquiv] at hc

/-- Every chosen Sylow two-subgroup of H has an exact ambient Sylow image. -/
public theorem centralizer_sylow_promotes (h : Hypotheses z)
    (T : Sylow 2 (Centralizer z)) :
    ∃ S : Sylow 2 G, (S : Subgroup G) =
      (T : Subgroup (Centralizer z)).map (Centralizer z).subtype := by
  have hc : Nat.card (center (pCore 2 (Centralizer z))) = 2 := by
    rw [← h.core_eq_pCore]
    let : IsExtraspecial 2 (Core z) := h.extraspecial
    exact IsExtraspecial.center_order_p 2 (Core z)
  have hs : centralizer (pCore 2 (Centralizer z) : Set (Centralizer z)) ≤
      pCore 2 (Centralizer z) := by
    rw [← h.core_eq_pCore]
    exact Theory.GroupTheory.centralizer_generalizedFitting_le (Centralizer z)
  exact (centralizer_structure_of_center_two_core z h.involution hc hs).2.2 T

/-- The ambient odd-index field of `IntersectionData` follows already from
the original local hypotheses, independently of quaternion normality. -/
public theorem centralizer_odd_index (h : Hypotheses z) : Odd (Centralizer z).index := by
  obtain ⟨S, hS⟩ := centralizer_sylow_promotes h (Sylow.nonempty.some : Sylow 2 (Centralizer z))
  have hSC : (S : Subgroup G) ≤ Centralizer z := hS ▸ map_subtype_le _
  have hn : ¬ 2 ∣ (Centralizer z).index := fun hd =>
    S.not_dvd_index (hd.trans (index_dvd_of_le hSC))
  rw [Nat.dvd_iff_mod_eq_zero] at hn
  exact Nat.odd_iff.mpr (by omega)

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition
