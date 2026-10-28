module
public import Theory.GroupAction.CubicTree.CentralTranslation
public import Theory.GroupAction.CubicTree.Reflections

/-!
# Reflection of central intervals

A track with reflections has an action reflecting its integer parameter
about each vertex. Conjugating a central involution by that action reverses
its fixed and central intervals. For a one-edge central block with equal
margins, a reflection or translation aligns both boundary pairs.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (6.5), pp.397–398.
-/

@[expose] public section
namespace Theory.GroupAction.CubicTree
open Subgroup
variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
namespace Track

theorem HasReflections.exists_center {t : Track Γ G} (h : t.HasReflections) (c : ℤ) :
    ∃ g : G, ∀ i, g • t.vertex i = t.vertex (2 * c - i) := by
  obtain ⟨x, y, hx, hy, hxr, hyr⟩ := h
  refine ⟨t.translation ^ c * x, ?_⟩
  intro i
  rw [mul_smul, hxr, t.zpow_translate]
  congr 1
  omega

 theorem edgeStabilizer_reflection (t : Track Γ G) (g : G) (c : ℤ)
    (hg : ∀ i, g • t.vertex i = t.vertex (2*c-i)) (i : ℤ) :
    (t.edgeStabilizer i).map (MulAut.conj g).toMonoidHom =
      t.edgeStabilizer (2*c-i-1) := by
  unfold edgeStabilizer
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
    ← MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    ← MulAction.stabilizer_smul_eq_stabilizer_map_conj, hg, hg]
  have h1 : 2*c-(i+1) = 2*c-i-1 := by omega
  have h2 : 2*c-i-1+1 = 2*c-i := by omega
  rw [h1, h2, inf_comm]

theorem centralEdge_reflection_iff (t : Track Γ G) (g : G) (c : ℤ)
    (hg : ∀ i, g • t.vertex i = t.vertex (2*c-i)) (z : G) (i : ℤ) :
    t.CentralEdge ((MulAut.conj g) z) (2*c-i-1) ↔ t.CentralEdge z i := by
  rw [CentralEdge, ← t.edgeStabilizer_reflection g c hg]
  constructor
  · rintro ⟨⟨z', hz', he⟩, hc⟩
    have hz'z : z' = z := (MulAut.conj g).injective he
    subst z'
    refine ⟨hz', ?_⟩
    intro x hx
    have hh := hc ((MulAut.conj g) x) ⟨x, hx, rfl⟩
    exact (Commute.conj_iff g).1 hh
  · rintro ⟨hz, hc⟩
    refine ⟨⟨z, hz, rfl⟩, ?_⟩
    rintro x ⟨x', hx', rfl⟩
    exact (hc x' hx').conj g

theorem fixed_reflection_iff (t : Track Γ G) (g : G) (c : ℤ)
    (hg : ∀ i, g • t.vertex i = t.vertex (2*c-i)) (z : G) (i : ℤ) :
    (MulAut.conj g) z • t.vertex (2*c-i) = t.vertex (2*c-i) ↔
      z • t.vertex i = t.vertex i := by
  rw [← hg i]
  change (g * z * g⁻¹) • (g • t.vertex i) = g • t.vertex i ↔ _
  simp only [mul_smul, inv_smul_smul]
  exact (MulAction.toPerm g).injective.eq_iff

theorem CentralInvolution.reflection {t : Track Γ G} {z : G}
    (hz : t.CentralInvolution z) (g : G) (c : ℤ)
    (hg : ∀ i, g • t.vertex i = t.vertex (2*c-i)) :
    t.CentralInvolution ((MulAut.conj g) z) := by
  refine ⟨(orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective z).trans hz.1, ?_⟩
  obtain ⟨i, hi⟩ := hz.2
  exact ⟨2*c-i-1, (t.centralEdge_reflection_iff g c hg z i).2 hi⟩

def CentralInterval.reflection {t : Track Γ G} {z : G} (d : t.CentralInterval z)
    (g : G) (c : ℤ) (hg : ∀ i, g • t.vertex i = t.vertex (2*c-i)) :
    t.CentralInterval ((MulAut.conj g) z) where
  fixedLeft := 2*c-d.fixedRight
  fixedRight := 2*c-d.fixedLeft
  centralLeft := 2*c-d.centralRight
  centralRight := 2*c-d.centralLeft
  fixed_iff i := by
    have he : i = 2*c-(2*c-i) := by omega
    rw [he, t.fixed_reflection_iff g c hg, d.fixed_iff]
    omega
  central_lt := by have hh := d.central_lt; omega
  central i hi hir := by
    have he : i = 2*c-(2*c-i-1)-1 := by omega
    rw [he]
    exact (t.centralEdge_reflection_iff g c hg z _).2
      (d.central (2*c-i-1) (by omega) (by omega))
  maximal a b hab hcentral := by
    have hh := d.maximal (2*c-b) (2*c-a) (by omega) (fun i hi hir =>
      (t.centralEdge_reflection_iff g c hg z i).1
        (hcentral (2*c-i-1) (by omega) (by omega)))
    omega

/-- For a one-edge central interval with equal margins, a translation or a
reflection followed by a translation aligns both boundary pairs. -/
theorem CentralInterval.exists_double_aligned {t : Track Γ G} {z : G}
    (d : t.CentralInterval z) (hz : t.CentralInvolution z) (href : t.HasReflections)
    (hwidth : d.centralRight = d.centralLeft + 1)
    (hmargins : d.leftMargin = d.rightMargin) :
    ∃ z' : G, ∃ _hz' : t.CentralInvolution z', ∃ d' : t.CentralInterval z',
      d.centralRight = d'.fixedLeft ∧ d.fixedRight = d'.centralLeft := by
  have hl := d.leftMargin_cast
  have hr := d.rightMargin_cast
  rcases Nat.even_or_odd d.rightMargin with heven | hodd
  · obtain ⟨k, hk⟩ := heven
    obtain ⟨g, hg⟩ := href.exists_center d.centralRight
    let e := (d.reflection g d.centralRight hg).shift (k : ℤ)
    refine ⟨_, (hz.reflection g d.centralRight hg).shift (k : ℤ), e, ?_, ?_⟩ <;>
      dsimp only [e, CentralInterval.shift, CentralInterval.reflection] <;> omega
  · obtain ⟨k, hk⟩ := hodd
    let e := d.shift ((k : ℤ)+1)
    refine ⟨_, hz.shift ((k : ℤ)+1), e, ?_, ?_⟩ <;>
      dsimp only [e, CentralInterval.shift] <;> omega

end Track
end Theory.GroupAction.CubicTree
