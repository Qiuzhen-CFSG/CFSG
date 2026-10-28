module
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.End

/-!
# Automorphisms of the J3 parabolic pair

The pair group D₃ × D₅ has two outer automorphism classes. Coordinate
multiplication by two represents the nontrivial class; its square is inner.
An arbitrary automorphism is determined by the images of the four standard
generators. Odd orders and commuting relations force these images into the
original factors, and finite checks on the dihedral normal forms supply the
conjugating element. No automorphism group is enumerated.
-/

open DihedralGroup
namespace Sporadic.Janko3.SourceRecognition.PairAutomorphisms

/-- The standard S₃ × D₁₀ parabolic overlap. -/
public abbrev H := DihedralGroup 3 × DihedralGroup 5

/-- Double both rotation coordinates while fixing the two standard reflections. -/
@[expose] public def delta : MulAut H where
  toFun x :=
    (match x.1 with | r i => r (2 * i) | sr i => sr (2 * i),
     match x.2 with | r i => r (2 * i) | sr i => sr (2 * i))
  invFun x :=
    (match x.1 with | r i => r (2 * i) | sr i => sr (2 * i),
     match x.2 with | r i => r (3 * i) | sr i => sr (3 * i))
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_mul' := by
    rintro ⟨x₃, x₅⟩ ⟨y₃, y₅⟩
    apply Prod.ext
    · cases x₃ <;> cases y₃ <;> simp [mul_add, mul_sub]
    · cases x₅ <;> cases y₅ <;> simp [mul_add, mul_sub]

@[simp] public theorem delta_r_left (i : ZMod 3) : delta (r i, 1) = (r (2 * i), 1) := by
  change (r (2 * i), r (2 * 0)) = (r (2 * i), (1 : DihedralGroup 5))
  simp

@[simp] public theorem delta_sr_left (i : ZMod 3) : delta (sr i, 1) = (sr (2 * i), 1) := by
  change (sr (2 * i), r (2 * 0)) = (sr (2 * i), (1 : DihedralGroup 5))
  simp

@[simp] public theorem delta_r_right (i : ZMod 5) : delta (1, r i) = (1, r (2 * i)) := by
  change (r (2 * 0), r (2 * i)) = ((1 : DihedralGroup 3), r (2 * i))
  simp

@[simp] public theorem delta_sr_right (i : ZMod 5) : delta (1, sr i) = (1, sr (2 * i)) := by
  change (r (2 * 0), sr (2 * i)) = ((1 : DihedralGroup 3), sr (2 * i))
  simp

/-- The representative has an inner square, not order two. -/
public theorem delta_sq : delta ^ 2 = MulAut.conj (1, sr 0) := by
  apply MulEquiv.ext
  exact (by decide +kernel : ∀ x : H, (delta ^ 2) x = MulAut.conj (1, sr 0) x)

-- These checks concern at most sixty group elements, never automorphisms.
private theorem cube_support :
    ∀ x : H, x ^ 3 = 1 → x ≠ 1 →
      ∃ i : ZMod 3, i ≠ 0 ∧ x = (r i, 1) := by decide +kernel

private theorem fifth_support :
    ∀ x : H, x ^ 5 = 1 → x ≠ 1 →
      ∃ i : ZMod 5, i ≠ 0 ∧ x = (1, r i) := by decide +kernel

private theorem reflection_three :
    ∀ x : DihedralGroup 3, x ^ 2 = 1 → x ≠ 1 →
      ∃ i : ZMod 3, x = sr i := by decide +kernel

private theorem reflection_five :
    ∀ x : DihedralGroup 5, x ^ 2 = 1 → x ≠ 1 →
      ∃ i : ZMod 5, x = sr i := by decide +kernel

private theorem commuting_involution_three :
    ∀ (x : DihedralGroup 3) (i : ZMod 3), i ≠ 0 →
      x ^ 2 = 1 → x * r i = r i * x → x = 1 := by decide +kernel

private theorem commuting_involution_five :
    ∀ (x : DihedralGroup 5) (i : ZMod 5), i ≠ 0 →
      x ^ 2 = 1 → x * r i = r i * x → x = 1 := by decide +kernel

private theorem coordinates_three :
    ∀ (i j : ZMod 3), i ≠ 0 → ∀ ε : Bool,
      ∃ h : DihedralGroup 3,
        h * r (if ε then 2 else 1) * h⁻¹ = r i ∧
        h * sr 0 * h⁻¹ = sr j := by decide +kernel

private theorem coordinates_five :
    ∀ (i j : ZMod 5), i ≠ 0 →
      ∃ (h : DihedralGroup 5) (ε : Bool),
        h * r (if ε then 2 else 1) * h⁻¹ = r i ∧
        h * sr 0 * h⁻¹ = sr j := by decide +kernel

private theorem dihedral_hom_ext {n : ℕ} [NeZero n] {K : Type*} [Group K]
    (f g : DihedralGroup n →* K)
    (hr : f (r 1) = g (r 1)) (hs : f (sr 0) = g (sr 0)) : f = g := by
  have hrot (i : ZMod n) : f (r i) = g (r i) := by
    have hi : (r 1 : DihedralGroup n) ^ i.val = r i := by simp
    rw [← hi, map_pow, map_pow, hr]
  apply MonoidHom.ext
  rintro (i | i)
  · exact hrot i
  · have hi : sr i = sr 0 * r i := by simp
    rw [hi, map_mul, map_mul, hs, hrot]

private theorem pair_hom_ext {K : Type*} [Group K] (f g : H →* K)
    (hr3 : f (r 1, 1) = g (r 1, 1))
    (hs3 : f (sr 0, 1) = g (sr 0, 1))
    (hr5 : f (1, r 1) = g (1, r 1))
    (hs5 : f (1, sr 0) = g (1, sr 0)) : f = g := by
  have h3 := dihedral_hom_ext
    (f.comp (MonoidHom.inl _ _)) (g.comp (MonoidHom.inl _ _)) hr3 hs3
  have h5 := dihedral_hom_ext
    (f.comp (MonoidHom.inr _ _)) (g.comp (MonoidHom.inr _ _)) hr5 hs5
  apply MonoidHom.ext
  rintro ⟨x, y⟩
  have hx : f (x, 1) = g (x, 1) := DFunLike.congr_fun h3 x
  have hy : f (1, y) = g (1, y) := DFunLike.congr_fun h5 y
  have hxy : (x, y) = (x, 1) * (1, y) := by simp
  rw [hxy, map_mul, map_mul, hx, hy]

/-- Every automorphism is inner followed by one of the two coordinate representatives. -/
public theorem exists_inner_mul_delta (φ : MulAut H) :
    ∃ (h : H) (ε : Bool), φ = MulAut.conj h * (if ε then delta else 1) := by
  have hne (x : H) (hx : x ≠ 1) : φ x ≠ 1 := by
    simpa only [map_one] using φ.injective.ne hx
  have hp (x : H) (n : ℕ) (hx : x ^ n = 1) : φ x ^ n = 1 := by
    rw [← map_pow, hx, map_one]
  obtain ⟨i, hi, hri⟩ := cube_support (φ (r 1, 1))
    (hp _ 3 (by decide +kernel)) (hne _ (by decide +kernel))
  obtain ⟨k, hk, hrk⟩ := fifth_support (φ (1, r 1))
    (hp _ 5 (by decide +kernel)) (hne _ (by decide +kernel))
  have hs3 := hp (sr 0, 1) 2 (by decide +kernel)
  have hs5 := hp (1, sr 0) 2 (by decide +kernel)
  have hc3 : φ (sr 0, 1) * φ (1, r 1) = φ (1, r 1) * φ (sr 0, 1) := by
    rw [← map_mul, ← map_mul]
    congr 1
  have hc5 : φ (1, sr 0) * φ (r 1, 1) = φ (r 1, 1) * φ (1, sr 0) := by
    rw [← map_mul, ← map_mul]
    congr 1
  have hs3snd : (φ (sr 0, 1)).2 = 1 :=
    commuting_involution_five _ k hk (congrArg Prod.snd hs3)
      (by simpa only [hrk, Prod.snd_mul] using congrArg Prod.snd hc3)
  have hs5fst : (φ (1, sr 0)).1 = 1 :=
    commuting_involution_three _ i hi (congrArg Prod.fst hs5)
      (by simpa only [hri, Prod.fst_mul] using congrArg Prod.fst hc5)
  obtain ⟨j, hj⟩ := reflection_three (φ (sr 0, 1)).1 (congrArg Prod.fst hs3)
    (by intro he; exact hne _ (by decide +kernel) (Prod.ext he hs3snd))
  obtain ⟨l, hl⟩ := reflection_five (φ (1, sr 0)).2 (congrArg Prod.snd hs5)
    (by intro he; exact hne _ (by decide +kernel) (Prod.ext hs5fst he))
  have hsj : φ (sr 0, 1) = (sr j, 1) := Prod.ext hj hs3snd
  have hsl : φ (1, sr 0) = (1, sr l) := Prod.ext hs5fst hl
  obtain ⟨h5, ε, h5r, h5s⟩ := coordinates_five k l hk
  obtain ⟨h3, h3r, h3s⟩ := coordinates_three i j hi ε
  refine ⟨(h3, h5), ε, ?_⟩
  apply MulEquiv.toMonoidHom_injective
  apply pair_hom_ext
  all_goals simp only [MulEquiv.coe_toMonoidHom]
  · rw [hri]
    cases ε <;> simpa [MulAut.mul_apply, MulAut.conj_apply, delta_r_left] using
      (congrArg (fun z : DihedralGroup 3 => (z, (1 : DihedralGroup 5))) h3r).symm
  · rw [hsj]
    cases ε <;> simpa [MulAut.mul_apply, MulAut.conj_apply, delta_sr_left] using
      (congrArg (fun z : DihedralGroup 3 => (z, (1 : DihedralGroup 5))) h3s).symm
  · rw [hrk]
    cases ε <;> simpa [MulAut.mul_apply, MulAut.conj_apply, delta_r_right] using
      (congrArg (fun z : DihedralGroup 5 => ((1 : DihedralGroup 3), z)) h5r).symm
  · rw [hsl]
    cases ε <;> simpa [MulAut.mul_apply, MulAut.conj_apply, delta_sr_right] using
      (congrArg (fun z : DihedralGroup 5 => ((1 : DihedralGroup 3), z)) h5s).symm

end Sporadic.Janko3.SourceRecognition.PairAutomorphisms
