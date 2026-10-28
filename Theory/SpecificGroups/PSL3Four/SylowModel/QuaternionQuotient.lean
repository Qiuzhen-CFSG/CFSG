module

public import Theory.SpecificGroups.PSL3Four.SylowModel.QuaternionCoordinates
/-!
# The elementary central quotient of the exceptional quaternion core

Squaring an element of the trace kernel kills its two root coordinates and its
field-automorphism coordinate. The remaining coordinate is Frobenius-fixed,
so the square belongs to the marked central involution subgroup. Thus the
natural surjection onto Qbar has that subgroup as its kernel and Qbar is an
elementary abelian group of order sixteen.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, §5.3.7,
printed pp. 660–661 (PDF pp. 677–678).
-/

@[expose] public section
namespace Matrix.PSL3Four.SylowModel
noncomputable section

theorem mem_C_coordinates (g : T) : g ∈ C ↔
    g.right = 1 ∧ g.left.x = 0 ∧ g.left.y = 0 ∧ fieldFrobenius g.left.c = g.left.c := by
  rw [mem_C_iff]
  constructor
  · rintro (rfl | rfl) <;> simp [z, inclusion, central]
  · rintro ⟨hr, hx, hy, hc⟩
    rcases (frobenius_fixed_iff _).mp hc with hc | hc
    · exact Or.inl (SemidirectProduct.ext (U.ext hx hy hc) hr)
    · exact Or.inr (SemidirectProduct.ext (U.ext hx hy hc) hr)

theorem core_square_mem_C (g : Q) : g.val ^ 2 ∈ C := by
  have hx := ((mem_Q _).mp g.property).1
  have hy := ((mem_Q _).mp g.property).2
  apply (mem_C_coordinates _).mpr
  rcases c2_cases g.val.right with hr | hr
  · simp only [pow_two, SemidirectProduct.mul_right, SemidirectProduct.mul_left,
      hr, one_mul, map_one, MulAut.one_apply, mul_x, mul_y, mul_c,
      CharTwo.add_self_eq_zero, zero_add]
    exact ⟨trivial, trivial, trivial, by rw [map_mul, hx, hy]⟩
  · simp only [pow_two, SemidirectProduct.mul_right, SemidirectProduct.mul_left,
      hr, action_τ, mul_x, mul_y, mul_c, frob_x, frob_y, frob_c, hx, hy,
      CharTwo.add_self_eq_zero]
    refine ⟨?_, trivial, trivial, ?_⟩
    · decide
    · change fieldFrobenius (trace g.val.left.c + g.val.left.x * g.val.left.y) = _
      rw [map_add, trace_fixed, map_mul, hx, hy]
      rfl

/-- The restriction of the marked quotient to its trace-kernel image. -/
def coreQuotient : Q →* Qbar where
  toFun g := ⟨quotient g, ⟨g, g.property, rfl⟩⟩
  map_one' := Subtype.ext (map_one quotient)
  map_mul' g h := Subtype.ext (map_mul quotient g.val h.val)

@[simp] theorem coreQuotient_val (g : Q) : (coreQuotient g).val = quotient g := rfl

theorem coreQuotient_surjective : Function.Surjective coreQuotient := by
  rintro ⟨g, a, ha, rfl⟩
  exact ⟨⟨a,ha⟩, rfl⟩

theorem coreQuotient_ker : coreQuotient.ker = C.subgroupOf Q := by
  ext g
  change coreQuotient g = 1 ↔ g.val ∈ C
  rw [Subtype.ext_iff]
  exact QuotientGroup.eq_one_iff g.val

theorem coreQuotient_sq (g : Qbar) : g ^ 2 = 1 := by
  obtain ⟨g, rfl⟩ := coreQuotient_surjective g
  rw [← map_pow]
  exact MonoidHom.mem_ker.mp (by
    rw [coreQuotient_ker]
    exact core_square_mem_C g)

instance : IsElementaryAbelian 2 Qbar where
  toIsMulCommutative := by
    have hi (g : Qbar) : g⁻¹ = g := inv_eq_of_mul_eq_one_right
      (by simpa only [pow_two] using coreQuotient_sq g)
    exact ⟨⟨fun a b => by rw [← hi (a*b), _root_.mul_inv_rev, hi a, hi b]⟩⟩
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr coreQuotient_sq

theorem card_Qbar : Nat.card Qbar = 16 := by
  have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup coreQuotient.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective coreQuotient
    coreQuotient_surjective).toEquiv, coreQuotient_ker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe C_le_Q).toEquiv, card_C, card_Q] at hc
  omega
end
end Matrix.PSL3Four.SylowModel
