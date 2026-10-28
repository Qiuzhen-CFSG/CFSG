module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PointCoreSeedCoverage
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PointCoreCommutator
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.SeedIntersections

/-!
# Point-core intersections as original conjugate seeds

An involution in the original marked point core belongs to a conjugate
of the original seed under the original involution centralizer. Transport
of the distinct-seed-point core intersection identifies that same seed
with the intersection of the two literal point cores. For an involution
outside the original seed, the seed intersection theorem consequently
gives precisely the original marked involution line.

These are consequences of the exact HS1--HS2 data preceding
Aschbacher--Smith I.4.8, printed p.418.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

private theorem point_core_map (e : MulAut G) (x : G) :
    ((involutionCentralizer x).pCoreIn 2).map e.toMonoidHom =
      (involutionCentralizer (e x)).pCoreIn 2 := by
  have hc : (involutionCentralizer x).map e.toMonoidHom = involutionCentralizer (e x) := by
    ext y
    rw [mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    rw [← e.injective.eq_iff]
    simp only [map_mul, MulEquiv.apply_symm_apply]
  rw [map_pCoreIn_of_ker_isPGroup _ (by
    rw [e.toMonoidHom.ker_eq_bot e.injective]
    exact IsPGroup.of_subsingleton 2 (⊥ : Subgroup G)), hc]

/-- The two literal point cores at adjacent distinct involutions meet in
an actual original-centralizer conjugate of the original seed. -/
theorem TypeAt.point_core_intersection_seed (h : TypeAt z V)
    (q : G) (hq : q ∈ (involutionCentralizer z).pCoreIn 2)
    (hq2 : orderOf q = 2) (hqz : q ≠ z) :
    ∃ g : involutionCentralizer z,
      (involutionCentralizer z).pCoreIn 2 ⊓ (involutionCentralizer q).pCoreIn 2 =
        V.map (MulAut.conj (g : G)).toMonoidHom := by
  obtain ⟨g, w, hw, he⟩ := h.centralizer_core_involution_seed_conjugate q hq hq2
  let e := MulAut.conj (g : G)
  have hz1 : z ≠ 1 := by
    intro hh
    have hz := h.involution
    simp [hh] at hz
  have hw1 : w ≠ 1 := by
    intro hh
    have hq1 : q = 1 := by rw [← he, hh, map_one]
    simp [hq1] at hq2
  have hzfix : e z = z := by
    change (g : G) * z * (g : G)⁻¹ = z
    rw [mem_centralizer_singleton_iff.mp g.property, mul_inv_cancel_right]
  have hzw : z ≠ w := by
    intro hh
    exact hqz (he.symm.trans (hh ▸ hzfix))
  have hi := h.distinct_point_cores_intersection z w h.involution_mem_seed hw hz1 hw1 hzw
  have hm := congrArg (fun A : Subgroup G => A.map e.toMonoidHom) hi
  rw [map_inf _ _ _ e.injective, point_core_map, point_core_map, hzfix,
    show e w = q from he] at hm
  exact ⟨g, hm⟩

/-- For a point-core involution outside the original seed, the corresponding
intersection seed meets the original seed precisely in its marked line. -/
theorem TypeAt.point_core_intersection_seed_intersection (h : TypeAt z V)
    (q : G) (hq : q ∈ (involutionCentralizer z).pCoreIn 2)
    (hq2 : orderOf q = 2) (hqV : q ∉ V) :
    ((involutionCentralizer z).pCoreIn 2 ⊓ (involutionCentralizer q).pCoreIn 2) ⊓ V =
      zpowers z := by
  have hqz : q ≠ z := fun he => hqV (he ▸ h.involution_mem_seed)
  obtain ⟨g, hg⟩ := h.point_core_intersection_seed q hq hq2 hqz
  have hqq : q ∈ (involutionCentralizer q).pCoreIn 2 := by
    let H := involutionCentralizer q
    let qH : H := ⟨q, mem_centralizer_singleton_iff.mpr rfl⟩
    have hqcentral : zpowers qH ≤ center H := by
      apply zpowers_le.mpr
      exact mem_center_iff.mpr fun x => Subtype.ext
        (mem_centralizer_singleton_iff.mp x.property)
    have hp : IsPGroup 2 (zpowers qH) := IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, ← orderOf_coe, show (qH : G) = q from rfl, hq2, pow_one])
    have hn : (zpowers qH).Normal := ⟨fun x hx g => by
      rw [mem_center_iff.mp (hqcentral hx) g, mul_inv_cancel_right]
      exact hx⟩
    have hc : zpowers qH ≤ pCore 2 H := le_sSup ⟨hn, hp⟩
    exact ⟨qH, hc (mem_zpowers qH), rfl⟩
  have hqg : q ∈ V.map (MulAut.conj (g : G)).toMonoidHom := hg ▸ ⟨hq, hqq⟩
  have hgn : (g : G) ∉ normalizer (V : Set G) := by
    intro hn
    have heV : V.map (MulAut.conj (g : G)).toMonoidHom = V :=
      mem_normalizer_iff_map_conj_eq.mp hn
    exact hqV (heV ▸ hqg)
  rw [hg, inf_comm]
  exact h.seed_conjugate_intersection g g.property hgn

end CFSG.Quasithin.HigmanSims
