module

public import Theory.GroupTheory.SpecificGroups.QuaternionCyclicModel

/-!
# Restricting automorphisms of Q₈ ◦ C₄ to Q₈

The embedded quaternion factor is characteristic: it consists of the identity,
the unique nonidentity square, and the noncentral elements with nonidentity
square. Every automorphism fixes the common involution by applying it to `r²`.

Restriction to this characteristic subgroup, transported along its actual
embedding, gives a homomorphism to `Aut(Q₈)` splitting the extension homomorphism.
An automorphism is determined by this restriction and its value on the central
generator `r`, by the model's normal forms.

Source: the central-product calculation in the proof of Aschbacher–Smith,
*The Classification of Quasithin Groups*, Lemma 14.2.21, printed p.988.
This module supplies the restriction step, not the full residual calculation.
-/

public section

namespace QuaternionCyclic

/-- Every automorphism fixes the shared involution, the unique nonidentity square. -/
theorem aut_fixes_involution (e : MulAut Model) :
    e (quaternionEmbedding z) = quaternionEmbedding z := by
  have hr : r ^ 2 ≠ 1 := by
    intro h
    have hd := orderOf_dvd_of_pow_eq_one h
    rw [r_order] at hd
    norm_num at hd
  have he : (e r) ^ 2 ≠ 1 := by
    rw [← map_pow, ← map_one e]
    exact fun h => hr (e.injective h)
  rw [← r_sq, map_pow]
  exact square_eq_involution (e r) he

/-- The quaternion factor is intrinsic to the central product. -/
instance quaternionRange_characteristic : quaternionEmbedding.range.Characteristic := by
  apply Subgroup.characteristic_iff_le_comap.mpr
  intro e x hx
  change e x ∈ quaternionEmbedding.range
  rw [mem_quaternion_iff] at hx ⊢
  rcases hx with rfl | rfl | ⟨hs, hc⟩
  · exact Or.inl (map_one e)
  · exact Or.inr (Or.inl (aut_fixes_involution e))
  · refine Or.inr (Or.inr ⟨?_, ?_⟩)
    · rw [← map_pow, ← map_one e]
      exact fun h => hs (e.injective h)
    · intro h
      exact hc (Subgroup.characteristic_iff_comap_le.mp
        (inferInstance : (Subgroup.center Model).Characteristic) e h)

/-- Restrict an automorphism to the quaternion factor, identified with `Q₈`. -/
noncomputable def restrictionHom : MulAut Model →* MulAut (QuaternionGroup 2) :=
  (MulAut.congr (MonoidHom.ofInjective quaternionEmbedding_injective).symm).toMonoidHom.comp
    (MulAut.characteristic quaternionEmbedding.range)

/-- Restriction agrees with the original action on the embedded quaternion factor. -/
theorem restrictionHom_quaternion (e : MulAut Model) (q : QuaternionGroup 2) :
    quaternionEmbedding (restrictionHom e q) = e (quaternionEmbedding q) := by
  exact MonoidHom.apply_ofInjective_symm quaternionEmbedding_injective _

/-- Restriction is a left inverse to extension fixing the central generator. -/
@[simp] theorem restrictionHom_extendAutHom (e : MulAut (QuaternionGroup 2)) :
    restrictionHom (extendAutHom e) = e := by
  apply MulEquiv.ext
  intro q
  apply quaternionEmbedding_injective
  rw [restrictionHom_quaternion]
  exact extendAut_quaternion e q

@[simp] theorem restrictionHom_one : restrictionHom 1 = 1 := map_one restrictionHom

@[simp] theorem restrictionHom_mul (e f : MulAut Model) :
    restrictionHom (e * f) = restrictionHom e * restrictionHom f :=
  map_mul restrictionHom e f

@[simp] theorem restrictionHom_inv (e : MulAut Model) :
    restrictionHom e⁻¹ = (restrictionHom e)⁻¹ := map_inv restrictionHom e

@[simp] theorem restrictionHom_symm (e : MulAut Model) :
    restrictionHom e.symm = (restrictionHom e).symm := map_inv restrictionHom e

/-- Every quaternion automorphism occurs as a restriction. -/
theorem restrictionHom_surjective : Function.Surjective restrictionHom :=
  fun e => ⟨extendAutHom e, restrictionHom_extendAutHom e⟩

/-- The embedded quaternion factor and the central generator determine an automorphism. -/
theorem aut_ext_quaternion_r {e f : MulAut Model}
    (hq : ∀ q, e (quaternionEmbedding q) = f (quaternionEmbedding q))
    (hr : e r = f r) : e = f := by
  apply MulEquiv.ext
  intro x
  rw [normal_form x, map_mul, map_mul, hq]
  congr 1
  cases x.odd <;> simp [r] at hr ⊢
  exact hr

/-- Restriction together with the image of `r` determines an automorphism. -/
theorem aut_ext_restriction_r {e f : MulAut Model}
    (hq : restrictionHom e = restrictionHom f) (hr : e r = f r) : e = f := by
  apply aut_ext_quaternion_r (hr := hr)
  intro q
  rw [← restrictionHom_quaternion, ← restrictionHom_quaternion, hq]

end QuaternionCyclic

end
