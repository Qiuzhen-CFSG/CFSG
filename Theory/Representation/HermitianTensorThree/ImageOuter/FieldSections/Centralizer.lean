module

public import Theory.Representation.HermitianTensorThree.ImageOuter.FieldSections.Basic

/-!
# The full field centralizer is SL₃ over the fixed field

A commuting image element lifts to a matrix whose Frobenius conjugate differs
by a norm-one cubic scalar. For even half-degree that scalar is one; for odd
half-degree a cubic scalar correction makes the lift fixed by Frobenius.
Thus the literal fixed-field embedding maps onto the entire centralizer.
Its action kernel is trivial, since a fixed norm-one scalar in characteristic
two is one. All identifications retain the original cover and image maps.

Source: Aschbacher–Smith, H.4.4(6), printed pp.380–381.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Representation.HermitianTensorThree.ImageOuter.FieldSections
variable (n : ℕ) [NeZero n]

/-- The literal inclusion SL₃(F) → SL₃(E). -/
def fixedCover : Matrix.SpecialLinearGroup (Fin 3) (F n) →* Cover n :=
  Matrix.SpecialLinearGroup.map (F n).subtype

omit [NeZero n] in
theorem fixedCover_sigma (a : Matrix.SpecialLinearGroup (Fin 3) (F n)) :
    Matrix.SpecialLinearGroup.map (sigma n).toRingHom (fixedCover n a) = fixedCover n a := by
  apply Subtype.ext
  ext i j
  exact (a.val i j).property

/-- The embedded fixed-field matrices commute with the literal marked swap. -/
def fixedToCentralizer : Matrix.SpecialLinearGroup (Fin 3) (F n) →* centralizer n :=
  ((binaryActionHom n).comp (fixedCover n)).codRestrict (centralizer n) (by
    intro a
    refine ⟨⟨fixedCover n a, rfl⟩, ?_⟩
    change binaryActionHom n (fixedCover n a) ∈ Subgroup.centralizer {fieldSwapBinary n}
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply LinearEquiv.ext
    intro X
    change action n (fixedCover n a) (fieldSwap n X) = fieldSwap n (action n (fixedCover n a) X)
    simpa only [fixedCover_sigma] using (fieldSwap_action n (fixedCover n a) X).symm)

theorem fixedToCentralizer_apply (a : Matrix.SpecialLinearGroup (Fin 3) (F n)) :
    (fixedToCentralizer n a).val = binaryActionHom n (fixedCover n a) := rfl

theorem fixedToCentralizer_toImage (a : Matrix.SpecialLinearGroup (Fin 3) (F n)) :
    centralizerToImage n (fixedToCentralizer n a) = toImage n (fixedCover n a) := by
  apply (binaryImageEquiv n).injective
  exact (binaryImageEquiv n).apply_symm_apply _

theorem fixedToCentralizer_injective : Function.Injective (fixedToCentralizer n) := by
  apply (injective_iff_map_eq_one (fixedToCentralizer n)).mpr
  intro a ha
  have hk : fixedCover n a ∈ (binaryActionHom n).ker := congrArg Subtype.val ha
  rw [binaryActionHom_ker_eq] at hk
  obtain ⟨c, he, _, hc⟩ := (mem_actionHom_ker_iff n _).mp hk
  have hcfix : sigma n c = c := by
    have h00 := congrArg (fun A : Mat n => A 0 0) he
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h00
    rw [← h00]
    exact (a.val 0 0).property
  have hc1 : c = 1 := by
    rw [hcfix] at hc
    have hh : c ^ 2 = (1 : E n) ^ 2 := by simpa [pow_two] using hc
    exact frobenius_inj (E n) 2 hh
  apply Subtype.ext
  ext i j
  have hij := congrArg (fun A : Mat n => A i j) he
  change (a.val i j).val = ((1 : Matrix (Fin 3) (Fin 3) (F n)) i j).val
  change (a.val i j).val = (Matrix.scalar (Fin 3) c) i j at hij
  simpa [hc1, Matrix.one_apply, apply_ite] using hij

/-- A fixed matrix descends along the actual subfield inclusion. -/
def descendFixed (a : Cover n)
    (ha : ∀ i j, sigma n (a.val i j) = a.val i j) :
    Matrix.SpecialLinearGroup (Fin 3) (F n) :=
  ⟨fun i j => ⟨a.val i j, ha i j⟩, by
    apply (F n).subtype.injective
    change (F n).subtype (Matrix.det (fun i j : Fin 3 => (⟨a.val i j, ha i j⟩ : F n))) = (F n).subtype 1
    rw [RingHom.map_det, map_one]
    exact a.property⟩

omit [NeZero n] in
theorem fixedCover_descendFixed (a : Cover n)
    (ha : ∀ i j, sigma n (a.val i j) = a.val i j) :
    fixedCover n (descendFixed n a ha) = a := by
  apply Subtype.ext
  rfl

/-- Every centralizing image element has a Frobenius-fixed cover lift. -/
theorem exists_fixed_lift (g : centralizer n) :
    ∃ a : Cover n, binaryActionHom n a = g.val ∧
      ∀ i j, sigma n (a.val i j) = a.val i j := by
  obtain ⟨a, ha⟩ := g.property.1
  let asig := Matrix.SpecialLinearGroup.map (sigma n).toRingHom a
  have him : binaryActionHom n asig = binaryActionHom n a := by
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp g.property.2
    rw [← ha] at hcomm
    rw [← fieldSwapBinary_conj, ← hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hk : asig * a⁻¹ ∈ (actionHom n).ker := by
    rw [← binaryActionHom_ker_eq]
    change binaryActionHom n (asig * a⁻¹) = 1
    rw [map_mul, map_inv, him, mul_inv_cancel]
  obtain ⟨c, he, hc, hn⟩ := (mem_actionHom_ker_iff n _).mp hk
  have hs : asig.val = Matrix.scalar (Fin 3) c * a.val := by
    calc
      asig.val = (asig * a⁻¹ * a).val := by rw [inv_mul_cancel_right]
      _ = Matrix.scalar (Fin 3) c * a.val := by rw [Matrix.SpecialLinearGroup.coe_mul, he]
  have hsij (i j : Fin 3) : sigma n (a.val i j) = c * a.val i j := by
    have hij := congrArg (fun A : Mat n => A i j) hs
    change sigma n (a.val i j) = (Matrix.scalar (Fin 3) c * a.val) i j at hij
    simpa only [Matrix.scalar_apply, Matrix.diagonal_mul] using hij
  rcases Nat.even_or_odd n with hnEven | hnOdd
  · have hc1 := (norm_cube_root_even_iff n hnEven c hc).mp hn
    exact ⟨a, ha, fun i j => by simpa [hc1] using hsij i j⟩
  · let s : Cover n := ⟨Matrix.scalar (Fin 3) (c ^ 2), by
      simp only [Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_three]
      calc
        c ^ 2 * c ^ 2 * c ^ 2 = (c ^ 3) ^ 2 := by ring
        _ = 1 := by rw [hc, one_pow]⟩
    have hsk : s ∈ (actionHom n).ker := by
      rw [mem_actionHom_ker_iff]
      refine ⟨c ^ 2, rfl, ?_, ?_⟩
      · rw [← pow_mul, show 2 * 3 = 3 * 2 by decide, pow_mul, hc, one_pow]
      · rw [map_pow, ← mul_pow, hn, one_pow]
    have hsk' : binaryActionHom n s = 1 := by
      rw [← binaryActionHom_ker_eq] at hsk
      exact hsk
    refine ⟨s * a, by rw [map_mul, hsk', one_mul, ha], ?_⟩
    intro i j
    change sigma n ((Matrix.scalar (Fin 3) (c ^ 2) * a.val) i j) =
      (Matrix.scalar (Fin 3) (c ^ 2) * a.val) i j
    rw [Matrix.scalar_apply, Matrix.diagonal_mul, map_mul, map_pow,
      sigma_cube_root_odd n hnOdd c hc, hsij]
    have hp : (c ^ 2) ^ 2 * c = c ^ 2 := by
      calc
        (c ^ 2) ^ 2 * c = c ^ 2 * c ^ 3 := by ring
        _ = c ^ 2 := by rw [hc, mul_one]
    rw [← mul_assoc, hp]

theorem fixedToCentralizer_surjective : Function.Surjective (fixedToCentralizer n) := by
  intro g
  obtain ⟨a, ha, hfix⟩ := exists_fixed_lift n g
  refine ⟨descendFixed n a hfix, ?_⟩
  apply Subtype.ext
  change binaryActionHom n (fixedCover n (descendFixed n a hfix)) = g.val
  rw [fixedCover_descendFixed, ha]

/-- The full centralizer, not just an embedded subgroup, is SL₃(F). -/
def centralizerEquiv : centralizer n ≃* Matrix.SpecialLinearGroup (Fin 3) (F n) :=
  (MulEquiv.ofBijective (fixedToCentralizer n)
    ⟨fixedToCentralizer_injective n, fixedToCentralizer_surjective n⟩).symm

theorem centralizerEquiv_fixedToCentralizer (a : Matrix.SpecialLinearGroup (Fin 3) (F n)) :
    centralizerEquiv n (fixedToCentralizer n a) = a :=
  (MulEquiv.ofBijective (fixedToCentralizer n)
    ⟨fixedToCentralizer_injective n, fixedToCentralizer_surjective n⟩).symm_apply_apply a

theorem centralizerEquiv_compatibility (g : centralizer n) :
    binaryImageEquiv n (toImage n (fixedCover n (centralizerEquiv n g))) =
      (⟨g.val, g.property.1⟩ : binaryImage n) := by
  apply Subtype.ext
  exact congrArg (fun a : centralizer n => a.val) ((centralizerEquiv n).symm_apply_apply g)

end Representation.HermitianTensorThree.ImageOuter.FieldSections
