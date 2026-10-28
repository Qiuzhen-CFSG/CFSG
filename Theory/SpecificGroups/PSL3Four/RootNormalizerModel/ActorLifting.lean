module

public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel.CubicGeometry.Centralizer

/-!
# The normal diagonal three-subgroup of the root actor

The diagonal subgroup of the marked `UT₃(F₄)` actor is normal of order
nine and has no nonidentity common fixed point on the root center. These
facts supply the Sylow--Frattini lifting argument. The actor also intersects
the inner automorphism group trivially, as seen on the two root coordinates.

Source: Aschbacher, *Sporadic Groups* (1994), 46.3(3), p.251, and 46.14,
pp.257–258. We use the whole diagonal three-group to split over the center;
the source instead uses a diagonal cubic to split over the whole root.
-/

@[expose] public section

open Subgroup
namespace Matrix.PSL3Four.RootNormalizerModel
namespace ActorLifting

noncomputable section

def diagonalActor : Subgroup actor := diagonalHom.range.subgroupOf actor

theorem diagonalActor_card : Nat.card diagonalActor = 9 := by
  calc
    Nat.card diagonalActor = Nat.card diagonalHom.range :=
      Nat.card_congr (subgroupOfEquivOfLe
        (show diagonalHom.range ≤ actor from le_sup_left)).toEquiv
    _ = Nat.card (Fˣ × Fˣ) :=
      Nat.card_congr (MonoidHom.ofInjective Cubic.diagonalHom_injective).toEquiv.symm
    _ = 9 := by rw [Nat.card_prod, Nat.card_units, card_F]

theorem diagonalActor_isPGroup : IsPGroup 3 diagonalActor := by
  apply IsPGroup.of_card (n := 2)
  exact diagonalActor_card

theorem diagonalActor_normal : diagonalActor.Normal := by
  apply (normal_subgroupOf_iff_le_normalizer
    (show diagonalHom.range ≤ actor from le_sup_left)).mpr
  apply sup_le
  · intro g hg
    obtain ⟨a, rfl⟩ := hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨b, rfl⟩
      refine ⟨b, ?_⟩
      have hab : a * b * a⁻¹ = b := by simp
      simpa only [map_mul, map_inv] using (congrArg diagonalHom hab).symm
    · intro hh
      obtain ⟨b, hb⟩ := hh
      refine ⟨b, ?_⟩
      have h' : h = diagonalHom b := by
        calc
          h = (diagonalHom a)⁻¹ *
              (diagonalHom a * h * (diagonalHom a)⁻¹) * diagonalHom a := by
                simp [mul_assoc]
          _ = (diagonalHom a)⁻¹ * diagonalHom b * diagonalHom a := by rw [← hb]
          _ = diagonalHom b := by
            have hab : a⁻¹ * b * a = b := by simp
            simpa only [map_mul, map_inv] using congrArg diagonalHom hab
      exact h'.symm
  · apply zpowers_le.mpr
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨a, rfl⟩ := hh
      refine ⟨Cubic.twist a, ?_⟩
      rw [Cubic.graphField_inv, Cubic.graphField_diagonal]
      rw [mul_assoc, Cubic.graphField_sq, mul_one]
    · intro hh
      obtain ⟨a, ha⟩ := hh
      have h' : h = diagonalHom (Cubic.twist a) := by
        calc
          h = graphField * (graphField * h * graphField⁻¹) * graphField := by
            rw [Cubic.graphField_inv]
            rw [← mul_assoc]
            rw [← mul_assoc graphField graphField h]
            rw [Cubic.graphField_sq, one_mul]
            rw [mul_assoc, Cubic.graphField_sq, mul_one]
          _ = graphField * diagonalHom a * graphField := by rw [← ha]
          _ = diagonalHom (Cubic.twist a) := by
            rw [Cubic.graphField_diagonal]
            rw [mul_assoc, Cubic.graphField_sq, mul_one]
      exact ⟨Cubic.twist a, h'.symm⟩

theorem diagonalActor_center_fixed (q : Root)
    (hq : q ∈ center Root)
    (hfix : ∀ a : diagonalActor, (a : MulAut Root) q = q) : q = 1 := by
  have hxy := (SylowModel.mem_center_U q).mp hq
  have hx : q.c = 0 := by
    let _ : Fintype Fˣ := Fintype.ofFinite Fˣ
    have hc : Fintype.card Fˣ = 3 := by
      rw [← Nat.card_eq_fintype_card, Nat.card_units, card_F]
    obtain ⟨a, b, hab⟩ := (Fintype.one_lt_card_iff.mp (by rw [hc]; decide))
    obtain ⟨a, ha⟩ : ∃ a : Fˣ, a ≠ 1 := by
      by_cases ha : a = 1
      · exact ⟨b, fun hb => hab (ha.trans hb.symm)⟩
      · exact ⟨a, ha⟩
    have haF : (a : F) ≠ 1 := by
      intro h
      exact ha (Units.ext h)
    have hm : (⟨(diagonalHom (a, 1)), (le_sup_left : diagonalHom.range ≤ actor)
      ⟨(a, 1), rfl⟩⟩ : actor) ∈ diagonalActor :=
      ⟨(a, 1), rfl⟩
    have he := hfix ⟨_, hm⟩
    have hc := congrArg SylowModel.U.c he
    have hcm : (a : F) * q.c = q.c := by
      simpa [diagonalHom, diagonal, hxy.1, hxy.2] using hc
    exact (mul_eq_mul_right_iff.mp (by simpa using hcm)).resolve_left haF
  apply SylowModel.U.ext
  · simp [hxy.1]
  · simp [hxy.2]
  · simp [hx]

theorem actor_inner_eq_one (s : actor) (q : Root)
    (h : (s : MulAut Root) = MulAut.conj q) : s = 1 := by
  obtain ⟨a, ha | ha⟩ := Cubic.actor_normal_form s
  · have hx := congrArg (fun t : MulAut Root => (t ⟨1, 0, 0⟩).x) h
    have hy := congrArg (fun t : MulAut Root => (t ⟨0, 1, 0⟩).y) h
    rw [ha] at hx hy
    have ha₁ : a.1 = 1 := by
      apply Units.ext
      change (a.1 : F) * 1 = (q.x + 1) + -q.x at hx
      have hxa : (a.1 : F) = 1 := by
        simpa only [mul_one, add_right_comm, add_neg_cancel, zero_add] using hx
      exact hxa
    have ha₂ : a.2 = 1 := by
      apply Units.ext
      change (a.2 : F) * 1 = (q.y + 1) + -q.y at hy
      have hya : (a.2 : F) = 1 := by
        simpa only [mul_one, add_right_comm, add_neg_cancel, zero_add] using hy
      exact hya
    apply Subtype.ext
    calc
      (s : MulAut Root) = diagonalHom a := ha
      _ = diagonalHom (1, 1) := by rw [show a = (1, 1) from Prod.ext ha₁ ha₂]
      _ = 1 := by
        apply MulEquiv.ext
        intro z
        simp [diagonalHom, diagonal]
  · have hx := congrArg (fun t : MulAut Root => (t ⟨1, 0, 0⟩).x) h
    rw [ha] at hx
    change (a.1 : F) * fieldFrobenius 0 = (q.x + 1) + -q.x at hx
    have he : q.x + 1 + -q.x = 1 := by ring
    have hz : (0 : F) = 1 := by simpa only [map_zero, mul_zero, he] using hx
    exact (zero_ne_one hz).elim

end
end ActorLifting
end Matrix.PSL3Four.RootNormalizerModel
