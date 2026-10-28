module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.OppositeOrbit
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.ReflectedMarking.Source

/-!
# Fusion of the two actual cubic axes

The second cubic axis is exactly the fixed subgroup of the first quaternion
support in the original Sylow nine. The earlier reflected marking supplies
an actor preserving that nine and interchanging its quaternion supports.
It therefore conjugates the first cubic axis to the second. Both axes are
actual source points on V; no orthogonal-module marking is required.

Source: Aschbacher, *Sporadic Groups* (1994), 45.3, 45.7 and the common
neighbor used in the proof of 45.10(6), pp.243–245,248.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsType z}
variable {P : Sylow 3 (centralizer z)}
namespace SourceConfiguration
variable (c : SourceConfiguration h P)

def otherAxis : Subgroup G := zpowers (c.actors.y : G)

omit [Finite G] in
theorem otherAxis_card : Nat.card c.otherAxis = 3 := by
  rw [otherAxis, Nat.card_zpowers, c.actors.y_order]

theorem otherAxis_fixed : c.actors.A ⊓ Subgroup.centralizer
    (h.toCentralizerHypothesis.factorData.leftCore : Set G) = c.otherAxis := by
  let B := h.toCentralizerHypothesis.factorData.leftCore
  let U := c.actors.A ⊓ Subgroup.centralizer (B : Set G)
  have hYU : c.otherAxis ≤ U := le_inf (zpowers_le.mpr c.actors.y.property)
    (zpowers_le.mpr c.actors.y_centralizes)
  have hd : Nat.card U ∣ 9 := c.actors.card ▸ card_dvd_of_le (show U ≤ c.actors.A from inf_le_left)
  have hlo : 3 ≤ Nat.card U := c.otherAxis_card ▸ card_le_of_le hYU
  have hne : Nat.card U ≠ 9 := by
    intro hu
    have he : U = c.actors.A := eq_of_le_of_card_ge inf_le_left (by rw [hu, c.actors.card])
    have hx : (c.actors.x : G) ∈ Subgroup.centralizer (B : Set G) :=
      (he.ge c.actors.x.property).2
    apply c.actors.x_actionB_ne_one
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    rw [c.actors.actionB_apply]
    change (c.actors.x : G) * (b : G) * (c.actors.x : G)⁻¹ = (b : G)
    rw [← hx b b.property, mul_inv_cancel_right]
  have hc : Nat.card U = 3 := by
    have hh := Nat.mem_divisors.mpr ⟨hd, (by decide : 9 ≠ 0)⟩
    have hdiv : Nat.divisors 9 = {1, 3, 9} := by decide
    simp only [hdiv, Finset.mem_insert, Finset.mem_singleton] at hh
    omega
  exact (eq_of_le_of_card_ge hYU (by rw [hc, c.otherAxis_card])).symm

theorem otherAxis_is_point : c.otherAxis ∈ c.points := by
  let d := h.toCentralizerHypothesis.factorData
  obtain ⟨R⟩ := h.exists_rootPair
  obtain ⟨m, E, hE, htE, ht, hs, hN, htB, htC⟩ :=
    R.exists_positioned_reflected_marking h c.X (h.cubic_sylow_image_card P) (map_subtype_le _)
  have hA : c.actors.A.map (MulAut.conj m.t).toMonoidHom = c.actors.A := by
    rw [c.actors_eq]
    exact mem_normalizer_iff_map_conj_eq.mp m.t_normalizes
  have hmap : c.W.map (MulAut.conj m.t).toMonoidHom ≤ c.actors.A ⊓
      Subgroup.centralizer (d.leftCore : Set G) := by
    refine le_inf ((map_mono (zpowers_le.mpr c.actors.x.property)).trans_eq hA) ?_
    have hWC : c.W ≤ Subgroup.centralizer (d.rightCore : Set G) :=
      zpowers_le.mpr c.actors.x_centralizes
    rintro a ⟨w, hw, rfl⟩ b hb
    have hb' : b ∈ d.rightCore.map (MulAut.conj m.t).toMonoidHom := htC.symm ▸ hb
    obtain ⟨v, hv, rfl⟩ := hb'
    simpa only [MulEquiv.coe_toMonoidHom, ← map_mul] using
      congrArg (MulAut.conj m.t) (hWC hw v hv)
  rw [c.otherAxis_fixed] at hmap
  have he : c.W.map (MulAut.conj m.t).toMonoidHom = c.otherAxis :=
    eq_of_le_of_card_ge hmap (by
      rw [card_map_of_injective (MulAut.conj m.t).injective, c.otherAxis_card, c.line_card])
  exact ⟨m.t, he.symm⟩

theorem otherAxis_le_kernel : c.otherAxis ≤ c.V := by
  have hAV : c.actors.A ≤ c.V := by
    rw [c.actors_eq]
    exact CubicNormalizer.le_oddKernel c.X (h.cubic_sylow_image_card P)
      (h.toCentralizerHypothesis.cubic_centralizer c.X (h.cubic_sylow_image_card P) (map_subtype_le _))
  exact (zpowers_le.mpr c.actors.y.property).trans hAV

theorem otherAxis_ne_point : c.otherAxis ≠ c.W := by
  have hYK : c.otherAxis ≤ c.K := le_sup_right.trans le_sup_left
  have hWD : c.W ≤ c.D := c.odd_fixed.ge.trans inf_le_left
  intro he
  have hb : c.otherAxis ≤ (⊥ : Subgroup G) := by
    rw [← c.complement_disjoint.eq_bot]
    exact le_inf (he ▸ hWD) hYK
  have hh := card_le_of_le hb
  rw [c.otherAxis_card, card_bot] at hh
  omega

theorem otherAxis_neighbor : c.otherAxis ∈ c.neighbors c.W :=
  ⟨c.otherAxis_is_point, c.otherAxis_ne_point, c.V, c.line_mem,
    c.line_le_kernel, c.otherAxis_le_kernel⟩

end SourceConfiguration
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry
