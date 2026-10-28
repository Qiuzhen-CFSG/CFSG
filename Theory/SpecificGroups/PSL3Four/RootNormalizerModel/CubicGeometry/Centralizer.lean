module

public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel.CubicGeometry

/-!
# Centralizers in the full root normalizer

Graph–field conjugates a diagonal actor (a, b) to (b², a²), and has square
one. These identities prove that every actor is diagonal or diagonal times
graph–field. For a nonzero x-axis element, the latter case is impossible.
The commuting equation in the actual semidirect product then forces the
first diagonal scalar to be one and the root y-coordinate to vanish.

The resulting centralizer is in bijection with F₄ × F₄ × F₄ˣ, hence has
order 48. No enumeration of automorphisms or ambient subgroup subsets is
used. This is the normalizer calculation used at the start of Aschbacher,
*Sporadic Groups* (1994), 47.1, pp.259–260, with the coordinates of 46.14.
-/

@[expose] public section
open Subgroup
namespace Matrix.PSL3Four.RootNormalizerModel.Cubic
noncomputable section

def twist (a : Fˣ × Fˣ) : Fˣ × Fˣ := (a.2 ^ 2, a.1 ^ 2)

theorem graphField_sq : graphField * graphField = 1 := by
  apply MulEquiv.ext
  intro q
  apply SylowModel.U.ext
  · exact fieldFrobenius_involutive _
  · exact fieldFrobenius_involutive _
  · change fieldFrobenius (fieldFrobenius q.y * fieldFrobenius q.x -
      fieldFrobenius (q.x * q.y - q.c)) = q.c
    rw [map_sub, map_mul, fieldFrobenius_involutive, fieldFrobenius_involutive,
      fieldFrobenius_involutive]
    ring

theorem graphField_inv : graphField⁻¹ = graphField := by
  exact inv_eq_of_mul_eq_one_right graphField_sq

theorem graphField_diagonal (a : Fˣ × Fˣ) :
    graphField * diagonalHom a = diagonalHom (twist a) * graphField := by
  apply MulEquiv.ext
  intro q
  apply SylowModel.U.ext
  · change fieldFrobenius (a.2 * q.y) = (↑(a.2 ^ 2) : F) * fieldFrobenius q.y
    simp [mul_pow]
  · change fieldFrobenius (a.1 * q.x) = (↑(a.1 ^ 2) : F) * fieldFrobenius q.x
    simp [mul_pow]
  · change fieldFrobenius ((a.1 * q.x) * (a.2 * q.y) - (a.1 * a.2 : F) * q.c) =
      ((↑(a.2 ^ 2) : F) * (↑(a.1 ^ 2) : F)) * fieldFrobenius (q.x * q.y - q.c)
    simp only [map_sub, map_mul, fieldFrobenius_apply, Units.val_pow_eq_pow_val]
    ring

/-- Every actor is diagonal or diagonal times graph–field. -/
theorem actor_normal_form (s : actor) :
    ∃ a : Fˣ × Fˣ, (s : MulAut Root) = diagonalHom a ∨
      (s : MulAut Root) = diagonalHom a * graphField := by
  let H : Subgroup (MulAut Root) :=
    { carrier := {s | ∃ a : Fˣ × Fˣ, s = diagonalHom a ∨ s = diagonalHom a * graphField}
      one_mem' := ⟨1, Or.inl (map_one diagonalHom).symm⟩
      mul_mem' := by
        rintro s t ⟨a, ha | ha⟩ ⟨b, hb | hb⟩
        · exact ⟨a * b, Or.inl (by rw [ha, hb, map_mul])⟩
        · exact ⟨a * b, Or.inr (by rw [ha, hb, map_mul, mul_assoc])⟩
        · refine ⟨a * twist b, Or.inr ?_⟩
          rw [ha, hb, map_mul, mul_assoc, graphField_diagonal, mul_assoc]
        · refine ⟨a * twist b, Or.inl ?_⟩
          rw [ha, hb, map_mul, mul_assoc, ← mul_assoc graphField,
            graphField_diagonal, mul_assoc, graphField_sq, mul_one]
      inv_mem' := by
        rintro s ⟨a, ha | ha⟩
        · exact ⟨a⁻¹, Or.inl (by rw [ha, map_inv])⟩
        · exact ⟨twist a⁻¹, Or.inr (by
            rw [ha]
            rw [_root_.mul_inv_rev, graphField_inv, ← map_inv, graphField_diagonal])⟩ }
  have h : actor ≤ H := by
    apply sup_le
    · rintro s ⟨a, rfl⟩
      exact ⟨a, Or.inl rfl⟩
    · apply zpowers_le.mpr
      exact ⟨1, Or.inr (by rw [map_one, one_mul])⟩
  exact h s.property

theorem commute_inl_iff (g : Model) (q : Root) :
    g * SemidirectProduct.inl q = SemidirectProduct.inl q * g ↔
      g.left * (g.right : MulAut Root) q = q * g.left := by
  constructor
  · intro h
    simpa using congrArg SemidirectProduct.left h
  · intro h
    apply SemidirectProduct.ext
    · simpa using h
    · simp

/-- Root coordinates and the diagonal scalar are retained in this full centralizer. -/
theorem centralizes_axis_iff (x : F) (hx : x ≠ 0) (g : Model) :
    g ∈ centralizer ({uHom (Multiplicative.ofAdd x)} : Set Model) ↔
      g.left.y = 0 ∧ ∃ b : Fˣ, g.right = torus (1, b) := by
  rw [mem_centralizer_singleton_iff]
  change g * SemidirectProduct.inl (xAxis (Multiplicative.ofAdd x)) =
      SemidirectProduct.inl (xAxis (Multiplicative.ofAdd x)) * g ↔ _
  rw [commute_inl_iff]
  constructor
  · intro h
    obtain ⟨a, ha | ha⟩ := actor_normal_form g.right
    · rw [ha] at h
      have hfirst : (a.1 : F) * x = x := by
        have hh := congrArg SylowModel.U.x h
        have hh' : g.left.x + (a.1 : F) * x = x + g.left.x := by
          simpa [diagonalHom, diagonal, xAxis] using hh
        exact add_left_cancel (hh'.trans (add_comm x g.left.x))
      have ha1 : a.1 = 1 := Units.ext ((mul_eq_right₀ hx).mp hfirst)
      have hy : g.left.y = 0 := by
        have hh := congrArg SylowModel.U.c h
        have hz : x * g.left.y = 0 := by
          simpa [diagonalHom, diagonal, xAxis, eq_comm] using hh
        exact (mul_eq_zero.mp hz).resolve_left hx
      refine ⟨hy, a.2, Subtype.ext ?_⟩
      change (g.right : MulAut Root) = diagonalHom (1, a.2)
      rw [show a = (1, a.2) from Prod.ext ha1 rfl] at ha
      exact ha
    · rw [ha] at h
      have hh := congrArg SylowModel.U.x h
      have hz : x = 0 := by
        have hh' : g.left.x = x + g.left.x := by
          simpa [diagonalHom, diagonal, graphField, graph, SylowModel.frob, xAxis] using hh
        exact add_right_cancel (show x + g.left.x = 0 + g.left.x by simpa using hh'.symm)
      exact (hx hz).elim
  · rintro ⟨hy, b, hb⟩
    rw [hb]
    change g.left * diagonal (1, b) (xAxis (Multiplicative.ofAdd x)) =
      xAxis (Multiplicative.ofAdd x) * g.left
    apply SylowModel.U.ext <;> simp [diagonal, xAxis, hy, add_comm]

/-- The centralizer has two free field coordinates and one nonzero scalar. -/
def centralizerCoordinates (x : F) (hx : x ≠ 0) :
    centralizer ({uHom (Multiplicative.ofAdd x)} : Set Model) ≃ F × F × Fˣ where
  toFun g := (g.val.left.x, g.val.left.c,
    Classical.choose ((centralizes_axis_iff x hx g).mp g.property).2)
  invFun p := ⟨⟨⟨p.1, 0, p.2.1⟩, torus (1, p.2.2)⟩,
    (centralizes_axis_iff x hx _).mpr ⟨rfl, p.2.2, rfl⟩⟩
  left_inv g := by
    apply Subtype.ext
    apply SemidirectProduct.ext
    · exact SylowModel.U.ext rfl ((centralizes_axis_iff x hx g).mp g.property).1.symm rfl
    · exact (Classical.choose_spec ((centralizes_axis_iff x hx g).mp g.property).2).symm
  right_inv p := by
    change (p.1, p.2.1, Classical.choose _) = p
    refine Prod.ext rfl (Prod.ext rfl ?_)
    have h := Classical.choose_spec ((centralizes_axis_iff x hx
      (⟨⟨p.1, 0, p.2.1⟩, torus (1, p.2.2)⟩ : Model)).mp
      ((centralizes_axis_iff x hx _).mpr ⟨rfl, p.2.2, rfl⟩)).2
    exact (congrArg Prod.snd (diagonalHom_injective (congrArg Subtype.val h))).symm

theorem centralizer_card (t : Model) (ht : t ∈ U) (ht1 : t ≠ 1) :
    Nat.card (centralizer ({t} : Set Model)) = 48 := by
  rcases ht with ⟨x, rfl⟩
  have hx : x.toAdd ≠ 0 := fun h => ht1 (by
    simpa using congrArg (fun x : F => uHom (Multiplicative.ofAdd x)) h)
  change Nat.card (centralizer ({uHom (Multiplicative.ofAdd x.toAdd)} : Set Model)) = 48
  rw [Nat.card_congr (centralizerCoordinates x.toAdd hx), Nat.card_prod,
    Nat.card_prod, Nat.card_units, card_F]

end
end Matrix.PSL3Four.RootNormalizerModel.Cubic
