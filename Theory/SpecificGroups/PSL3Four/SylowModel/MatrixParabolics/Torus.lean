module

public import Theory.SpecificGroups.PSL3Four.SylowModel.MatrixParabolics.Basic

/-!
# An odd torus in the standard flag stabilizer

The diagonal matrices `diag(u,1,u⁻¹)` give an injective copy of `F₄ˣ` in the
matrix field extension. They fix the standard point and plane, and conjugation
scales the unitriangular coordinates by `(u,u,u²)`. Hence this torus also lies
in both root-plane normalizers. Its nonidentity elements have order three and
lie outside the coordinate Sylow subgroup of order 128. In particular, neither
the geometric flag stabilizer nor the intersection of the two actual locals
can be identified with that Sylow subgroup.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, §5.3.2
and §5.3.7, printed pp. 659--661 (PDF pp. 676--678).
-/

@[expose] public section
noncomputable section
open Configuration Projectivization
namespace Matrix.PSL3Four.SylowModel.MatrixRealization

/-- The determinant-one diagonal torus with middle diagonal entry one. -/
def torusSL : Fˣ →* SL where
  toFun u := ⟨!![(u : F), 0, 0; 0, 1, 0; 0, 0, (↑u⁻¹ : F)], by
    simp [Matrix.det_fin_three]⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' u v := by
    apply Subtype.ext
    change !![_,0,0;0,1,0;0,0,_] = !![_,0,0;0,1,0;0,0,_] * !![_,0,0;0,1,0;0,0,_]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, mul_comm]

@[simp] theorem torusSL_val (u : Fˣ) : (torusSL u).val =
    !![(u : F), 0, 0; 0, 1, 0; 0, 0, (↑u⁻¹ : F)] := rfl

/-- The same torus in the actual projective field extension. -/
def torus : Fˣ →* FieldExtension :=
  linearInclusion.comp ((QuotientGroup.mk' (Subgroup.center SL)).comp torusSL)

theorem torusSL_inverseTranspose (u : Fˣ) :
    SpecialLinearGroup.inverseTranspose (torusSL u) = torusSL u⁻¹ := by
  change (torusSL u)⁻¹.transpose = _
  rw [← map_inv]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem torus_mem_parabolic₁ (u : Fˣ) : torus u ∈ parabolic₁ := by
  rw [mem_parabolic₁]
  change Collineation.pointHom PG PG
    (pairedAction (linearInclusion ((torusSL u : SL) : PSL))) standardPoint = _
  rw [pairedAction_linear_point]
  rw [standardPoint, Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]
  refine ⟨u, ?_⟩
  change (fun i => (u : F) * (![1,0,0] : Fin 3 → F) i) = (torusSL u).val *ᵥ ![1,0,0]
  ext i
  fin_cases i <;> simp [torusSL_val, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem torus_mem_parabolic₂ (u : Fˣ) : torus u ∈ parabolic₂ := by
  rw [mem_parabolic₂]
  change Collineation.lineHom PG PG
    (pairedAction (linearInclusion ((torusSL u : SL) : PSL))) standardPlane = _
  rw [pairedAction_linear_line, torusSL_inverseTranspose]
  rw [standardPlane, Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]
  refine ⟨u, ?_⟩
  change (fun i => (u : F) * (![0,0,1] : Fin 3 → F) i) = (torusSL u⁻¹).val *ᵥ ![0,0,1]
  ext i
  fin_cases i <;> simp [torusSL_val, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem torus_injective : Function.Injective torus := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro u hu
  have he : ((torusSL u : SL) : PSL) = 1 :=
    linearInclusion_injective (show torus u = linearInclusion 1 from hu.trans (map_one _).symm)
  obtain ⟨r, _, hr⟩ := SpecialLinearGroup.mem_center_iff.mp
    ((QuotientGroup.eq_one_iff _).mp he)
  have h1 := congrArg (fun A : Matrix (Fin 3) (Fin 3) F => A 1 1) hr
  have h0 := congrArg (fun A : Matrix (Fin 3) (Fin 3) F => A 0 0) hr
  change r = 1 at h1
  change r = (u : F) at h0
  exact Units.ext (h0.symm.trans h1)

theorem torus_cube (u : Fˣ) : torus u ^ 3 = 1 := by
  have hu : u ^ 3 = 1 := by
    have hc : Nat.card Fˣ = 3 := by rw [Nat.card_units, card_F]
    simpa only [hc] using (pow_card_eq_one' : u ^ Nat.card Fˣ = 1)
  rw [← map_pow, hu, map_one]

theorem torus_order (u : Fˣ) (hu : u ≠ 1) : orderOf (torus u) = 3 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact orderOf_eq_prime (torus_cube u) (fun h => hu (torus_injective (h.trans (map_one _).symm)))

theorem torus_not_mem_sylow (u : Fˣ) (hu : u ≠ 1) : torus u ∉ (sylow : Subgroup FieldExtension) := by
  intro h
  have hd := orderOf_dvd_natCard (⟨torus u, h⟩ : sylow)
  rw [Subgroup.orderOf_mk, torus_order u hu] at hd
  change 3 ∣ Nat.card embedding.range at hd
  rw [card_range] at hd
  norm_num at hd

theorem torus_conjugate (u : Fˣ) (a : U) :
    torus u * linearInclusion (projective a) * (torus u)⁻¹ =
      linearInclusion (projective ⟨(u : F) * a.x, (u : F) * a.y, (u : F)^2 * a.c⟩) := by
  have h : torusSL u * specialLinear a =
      specialLinear ⟨(u : F) * a.x, (u : F) * a.y, (u : F)^2 * a.c⟩ * torusSL u := by
    apply Subtype.ext
    change !![(u : F),0,0;0,1,0;0,0,↑u⁻¹] * matrix a =
      matrix ⟨(u : F) * a.x, (u : F) * a.y, (u : F)^2 * a.c⟩ *
        !![(u : F),0,0;0,1,0;0,0,↑u⁻¹]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matrix, Matrix.mul_apply, Fin.sum_univ_three, pow_two, mul_assoc, u.ne_zero] <;> field_simp
  have he := congrArg
    (fun A : SL => linearInclusion ((QuotientGroup.mk' (Subgroup.center SL)) A)) h
  simp only [map_mul] at he
  change torus u * linearInclusion (projective a) =
    linearInclusion (projective ⟨(u : F) * a.x, (u : F) * a.y, (u : F)^2 * a.c⟩) * torus u at he
  rw [he, mul_inv_cancel_right]

theorem torus_range_le_local₁ : torus.range ≤ local₁ := by
  apply Subgroup.le_normalizer_iff.mpr
  rintro _ ⟨u, rfl⟩ a ha
  obtain ⟨x, c, rfl⟩ := (mem_rootPlane₁ a).mp ha
  rw [torus_conjugate]
  apply (mem_rootPlane₁ _).mpr
  exact ⟨(u : F) * x, (u : F)^2 * c, by simp⟩

theorem torus_range_le_local₂ : torus.range ≤ local₂ := by
  apply Subgroup.le_normalizer_iff.mpr
  rintro _ ⟨u, rfl⟩ a ha
  obtain ⟨y, c, rfl⟩ := (mem_rootPlane₂ a).mp ha
  rw [torus_conjugate]
  apply (mem_rootPlane₂ _).mpr
  exact ⟨(u : F) * y, (u : F)^2 * c, by simp⟩

/-- A common torus element of order three witnesses the full overlap outside the Sylow. -/
theorem exists_odd_torus_in_flag : ∃ g : FieldExtension,
    g ∈ flagIntersection ∧ g ∈ local₁ ⊓ local₂ ∧ orderOf g = 3 ∧
      g ∉ (sylow : Subgroup FieldExtension) := by
  obtain ⟨x, hx⟩ := exists_fieldFrobenius_ne
  have hx0 : x ≠ 0 := by intro h; exact hx (by simp [h])
  have hx1 : x ≠ 1 := by intro h; exact hx (by simp [h])
  let u : Fˣ := Units.mk0 x hx0
  have hu : u ≠ 1 := fun h => hx1 (congrArg Units.val h)
  exact ⟨torus u, ⟨torus_mem_parabolic₁ u, torus_mem_parabolic₂ u⟩,
    ⟨torus_range_le_local₁ ⟨u, rfl⟩, torus_range_le_local₂ ⟨u, rfl⟩⟩,
    torus_order u hu, torus_not_mem_sylow u hu⟩

theorem localIntersection_ne_sylow : local₁ ⊓ local₂ ≠ (sylow : Subgroup FieldExtension) := by
  obtain ⟨g, _, hg, _, hn⟩ := exists_odd_torus_in_flag
  intro h
  exact hn (h ▸ hg)

theorem flagIntersection_ne_sylow : flagIntersection ≠ (sylow : Subgroup FieldExtension) := by
  obtain ⟨g, hg, _, _, hn⟩ := exists_odd_torus_in_flag
  intro h
  exact hn (h ▸ hg)

theorem sylow_lt_localIntersection :
    (sylow : Subgroup FieldExtension) < local₁ ⊓ local₂ :=
  lt_of_le_of_ne sylow_le_localIntersection (Ne.symm localIntersection_ne_sylow)

theorem sylow_lt_flagIntersection :
    (sylow : Subgroup FieldExtension) < flagIntersection :=
  lt_of_le_of_ne sylow_le_flagIntersection (Ne.symm flagIntersection_ne_sylow)

end Matrix.PSL3Four.SylowModel.MatrixRealization
