module

public import Theory.GroupAction.CubicTree.CentralIntervals
public import Theory.GroupAction.CubicTree.TrackTranslation

/-!
# Translation of fixed and central intervals

Conjugating an involution by a power of the chosen track translation shifts
both of its intervals by twice that power. All four endpoints and the maximal
central-block condition are transported, so the subsequent comparisons retain
the source involutions and the literal left-action conjugation convention.

Source: Goldschmidt (6.2)--(6.3), printed pp.396--397.
-/

@[expose] public section
namespace Theory.GroupAction.CubicTree
open SimpleGraph Subgroup
universe u v
variable {V : Type u} {G : Type v} {Γ : SimpleGraph V} [Group G] [MulAction G V]
namespace Track

theorem edgeStabilizer_shift (t : Track Γ G) (a : G) (m : ℤ)
    (ha : ∀ i, a • t.vertex i = t.vertex (i + m)) (i : ℤ) :
    t.edgeStabilizer (i + m) = (t.edgeStabilizer i).map (MulAut.conj a).toMonoidHom := by
  unfold edgeStabilizer
  have he : i + m + 1 = (i + 1) + m := by omega
  rw [he, ← ha i, ← ha (i + 1),
    MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    Subgroup.map_inf _ _ _ (MulAut.conj a).injective]

theorem centralEdge_shift_iff (t : Track Γ G) (a : G) (m : ℤ)
    (ha : ∀ i, a • t.vertex i = t.vertex (i + m)) (z : G) (i : ℤ) :
    t.CentralEdge ((MulAut.conj a) z) (i + m) ↔ t.CentralEdge z i := by
  rw [CentralEdge, t.edgeStabilizer_shift a m ha]
  constructor
  · rintro ⟨⟨z', hz', he⟩, hc⟩
    have hz'z : z' = z := (MulAut.conj a).injective he
    subst z'
    refine ⟨hz', ?_⟩
    intro x hx
    have hh := hc ((MulAut.conj a) x) ⟨x, hx, rfl⟩
    exact (Commute.conj_iff a).1 hh
  · rintro ⟨hz, hc⟩
    refine ⟨⟨z, hz, rfl⟩, ?_⟩
    rintro x ⟨x', hx', rfl⟩
    exact (hc x' hx').conj a

theorem fixed_shift_iff (t : Track Γ G) (a : G) (m : ℤ)
    (ha : ∀ i, a • t.vertex i = t.vertex (i + m)) (z : G) (i : ℤ) :
    (MulAut.conj a) z • t.vertex (i + m) = t.vertex (i + m) ↔
      z • t.vertex i = t.vertex i := by
  rw [← ha i]
  change (a * z * a⁻¹) • (a • t.vertex i) = a • t.vertex i ↔ _
  simp only [mul_smul, inv_smul_smul]
  exact (MulAction.toPerm a).injective.eq_iff

theorem CentralInvolution.shift {t : Track Γ G} {z : G}
    (hz : t.CentralInvolution z) (k : ℤ) :
    t.CentralInvolution ((MulAut.conj (t.translation ^ k)) z) := by
  refine ⟨(orderOf_injective (MulAut.conj _).toMonoidHom (MulAut.conj _).injective z).trans hz.1, ?_⟩
  obtain ⟨i, hi⟩ := hz.2
  exact ⟨i + 2 * k, (t.centralEdge_shift_iff _ _ (t.zpow_translate k) z i).2 hi⟩

/-- Transport the chosen maximal central block, without making any uniqueness
assumption about competing blocks. -/
def CentralInterval.shift {t : Track Γ G} {z : G} (d : t.CentralInterval z) (k : ℤ) :
    t.CentralInterval ((MulAut.conj (t.translation ^ k)) z) where
  fixedLeft := d.fixedLeft + 2 * k
  fixedRight := d.fixedRight + 2 * k
  centralLeft := d.centralLeft + 2 * k
  centralRight := d.centralRight + 2 * k
  fixed_iff i := by
    have he : i = (i - 2 * k) + 2 * k := by omega
    rw [he, t.fixed_shift_iff _ _ (t.zpow_translate k), d.fixed_iff]
    omega
  central_lt := by have hh := d.central_lt; omega
  central i hi hir := by
    have he : i = (i - 2 * k) + 2 * k := by omega
    rw [he]
    exact (t.centralEdge_shift_iff _ _ (t.zpow_translate k) z _).2
      (d.central (i - 2 * k) (by omega) (by omega))
  maximal a b hab hcentral := by
    have hh := d.maximal (a - 2 * k) (b - 2 * k) (by omega) (fun i hi hir =>
      (t.centralEdge_shift_iff _ _ (t.zpow_translate k) z i).1
        (hcentral (i + 2 * k) (by omega) (by omega)))
    omega

end Track
end Theory.GroupAction.CubicTree
