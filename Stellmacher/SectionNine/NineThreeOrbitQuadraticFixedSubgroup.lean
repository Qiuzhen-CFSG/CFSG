module
public import Stellmacher.SectionNine.NineThreeQuadraticFixedSubgroup

/-!
# Quadratic fixed subgroups at conjugate initial vertices

At any vertex in the initial vertex's orbit, a two-subgroup of the stabilizer
acting quadratically on its center admits a subgroup of index at most two
whose fixed space escapes any ambient subgroup not containing that center.

Conjugate the actor and prescribed ambient subgroup back to the initial
vertex. Stabilizer and center covariance preserve containment and the
quadratic commutator equality. Apply the initial-vertex fixed-subgroup
theorem, then conjugate its witness back. Injective automorphisms preserve
cardinalities and transport the ambient centralizer condition.

This is the second occurrence of the fixed-space argument in Stellmacher
(9.3), Journal of Algebra 190 (1997), p.49, using the same local context
without classification assumptions. Source: `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext
universe u

private theorem map_inverse_map
    {G : Type*} [Group G] (e : G ≃* G) (A : Subgroup G) :
    (A.map e.symm.toMonoidHom).map e.toMonoidHom = A := by
  ext x
  simp only [Subgroup.mem_map_equiv, e.symm_symm, e.apply_symm_apply]

/-- The fixed-subgroup conclusion at any supplied conjugate of the initial vertex. -/
public theorem nine_three_quadratic_fixed_subgroup_at_vertex
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (l : ctx.Γ.Vertex) (hl : IsConjugateVertex ctx.Γ ctx.criticalPath.a l)
    (Y : Subgroup G) (hYP : Y ≤ GAt ctx.Γ l)
    (hYp : IsPGroup 2 Y)
    (hquad : ⁅⁅ZAt ctx.Γ l, Y⁆, Y⁆ = ⊥)
    (R : Subgroup G) (hnot : ¬ ZAt ctx.Γ l ≤ R) :
    ∃ W : Subgroup G, W ≤ Y ∧ Nat.card Y ≤ 2 * Nat.card W ∧
      ¬ ZAt ctx.Γ l ⊓ Subgroup.centralizer (W : Set G) ≤ R := by
  obtain ⟨g, hg⟩ := hl
  let e : G ≃* G := MulAut.conj g⁻¹
  let Y0 := Y.map e.symm.toMonoidHom
  let R0 := R.map e.symm.toMonoidHom
  have hP : (GAt ctx.Γ ctx.criticalPath.a).map e.toMonoidHom = GAt ctx.Γ l := by
    change conjugateBy (stabilizer ctx.Γ ctx.criticalPath.a) g⁻¹ = _
    rw [← stabilizer_act, hg]
  have hZ : (ZAt ctx.Γ ctx.criticalPath.a).map e.toMonoidHom = ZAt ctx.Γ l := by
    change (z ctx.Γ ctx.criticalPath.a).map (MulAut.conj g⁻¹).toMonoidHom = _
    rw [← z_act, hg]
  have hYmap : Y0.map e.toMonoidHom = Y := map_inverse_map e Y
  have hY0P : Y0 ≤ GAt ctx.Γ ctx.criticalPath.a := by
    apply (Subgroup.map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
    rw [hYmap, hP]
    exact hYP
  have hY0p : IsPGroup 2 Y0 := hYp.map e.symm.toMonoidHom
  have hquad0 : ⁅⁅ZAt ctx.Γ ctx.criticalPath.a, Y0⁆, Y0⁆ = ⊥ := by
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [Subgroup.map_commutator, Subgroup.map_commutator, hZ, hYmap,
      hquad, Subgroup.map_bot]
  have hnot0 : ¬ ZAt ctx.Γ ctx.criticalPath.a ≤ R0 := by
    intro hc
    apply hnot
    have hh := Subgroup.map_mono (f := e.toMonoidHom) hc
    rwa [hZ, map_inverse_map e R] at hh
  obtain ⟨W0, hW0, hcard, hfixed⟩ :=
    nine_three_quadratic_fixed_subgroup ctx Y0 hY0P hY0p hquad0 R0 hnot0
  let W := W0.map e.toMonoidHom
  refine ⟨W, ?_, ?_, ?_⟩
  · exact (Subgroup.map_mono hW0).trans_eq hYmap
  · have hYcard : Nat.card Y0 = Nat.card Y := Subgroup.card_map_of_injective e.symm.injective
    have hWcard : Nat.card W = Nat.card W0 := Subgroup.card_map_of_injective e.injective
    rwa [hYcard, ← hWcard] at hcard
  · intro hc
    apply hfixed
    intro x hx
    apply Subgroup.mem_map_equiv.mpr
    change e x ∈ R
    apply hc
    refine ⟨?_, ?_⟩
    · rw [← hZ]
      exact Subgroup.mem_map_of_mem e.toMonoidHom hx.1
    · change e x ∈ Subgroup.centralizer (W : Set G)
      rw [Subgroup.mem_centralizer_iff]
      rintro y ⟨y0, hy0, rfl⟩
      change e y0 * e x = e x * e y0
      simpa only [map_mul] using
        congrArg e (Subgroup.mem_centralizer_iff.mp hx.2 y0 hy0)

end Stellmacher.SectionNine
