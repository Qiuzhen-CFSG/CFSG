module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.Algebra.Group.Conj
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Tactic.Ring

/-!
# Recognition with the two dihedral reflections marked

The usual rotation–reflection homomorphism sends `r 1` to `a * b` and `sr 0`
to `a`, hence `sr 1` to `b`. Generation proves surjectivity. Every nontrivial
normal subgroup of the dihedral group of order sixteen contains `r 4`: a
nonidentity rotation has a power equal to it, while commuting a reflection
with `r 1` and squaring produces it. Thus survival of `r 4` proves injectivity.

The homomorphism construction is adapted from this repository's
`Theory/GroupTheory/DihedralPresentation.lean`; the conclusion here retains
both generator images and uses the concrete fourth-power separation instead
of a cardinality premise. This is the presentation used for GLS3 2.3.2(d)
and 2.3.4, `refs/KGroup/GLS3/chapter2.tex`.
-/

public section
namespace ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry.MarkedWeyl
private def rotation {G : Type*} [Group G] {m : ℕ} [NeZero m]
    (c : G) (hc : c ^ m = 1) : Multiplicative (ZMod m) →* G where
  toFun i := c ^ i.toAdd.val
  map_one' := by simp
  map_mul' i j := by
    change c ^ (i.toAdd + j.toAdd).val = c ^ i.toAdd.val * c ^ j.toAdd.val
    rw [ZMod.val_add, ← pow_add]
    exact (pow_eq_pow_mod (i.toAdd.val + j.toAdd.val) hc).symm

private theorem rotation_one {G : Type*} [Group G] {m : ℕ} [NeZero m]
    (c : G) (hc : c ^ m = 1) : rotation c hc (.ofAdd 1) = c := by
  change c ^ (1 : ZMod m).val = c
  rw [← Nat.cast_one, ZMod.val_natCast, ← pow_eq_pow_mod 1 hc, pow_one]

private def presentationHom {G : Type*} [Group G] {m : ℕ} [NeZero m]
    (c d : G) (hc : c ^ m = 1) (hd : d ^ 2 = 1)
    (hconj : d * c * d⁻¹ = c⁻¹) : DihedralGroup m →* G := by
  let f := rotation c hc
  have hswap (i : Multiplicative (ZMod m)) : f i * d = d * (f i)⁻¹ := by
    have hh : d * f i * d⁻¹ = (f i)⁻¹ := by
      change d * c ^ i.toAdd.val * d⁻¹ = (c ^ i.toAdd.val)⁻¹
      rw [← conj_pow, hconj, inv_pow]
    have dd : d * d = 1 := by simpa [pow_two] using hd
    calc
      f i * d = (d * d) * f i * d := by rw [dd, one_mul]
      _ = d * (d * f i * d⁻¹) := by
        have hi : d⁻¹ = d := inv_eq_of_mul_eq_one_right dd
        rw [hi]
        simp only [mul_assoc]
      _ = d * (f i)⁻¹ := by rw [hh]
  refine {
    toFun := fun x => match x with
      | .r i => f (.ofAdd i)
      | .sr i => d * f (.ofAdd i)
    map_one' := by change f 1 = 1; exact f.map_one
    map_mul' := ?_ }
  intro x y
  cases x with
  | r i =>
    cases y with
    | r j => exact f.map_mul (.ofAdd i) (.ofAdd j)
    | sr j =>
      change d * f (.ofAdd (j - i)) = f (.ofAdd i) * (d * f (.ofAdd j))
      rw [← mul_assoc, hswap, mul_assoc]
      rw [sub_eq_add_neg]
      change d * f ((.ofAdd j) * (.ofAdd i)⁻¹) = d * ((f (.ofAdd i))⁻¹ * f (.ofAdd j))
      rw [map_mul, map_inv]
      congr 1
      simpa only [map_inv] using (Commute.map (Commute.all (.ofAdd j) ((.ofAdd i)⁻¹)) f).eq
  | sr i =>
    cases y with
    | r j =>
      change d * f ((.ofAdd i) * (.ofAdd j)) = d * f (.ofAdd i) * f (.ofAdd j)
      rw [map_mul, mul_assoc]
    | sr j =>
      change f (.ofAdd (j - i)) = (d * f (.ofAdd i)) * (d * f (.ofAdd j))
      rw [mul_assoc d, ← mul_assoc (f (.ofAdd i)), hswap, ← mul_assoc d, ← mul_assoc d d]
      have dd : d * d = 1 := by simpa [pow_two] using hd
      rw [dd, one_mul]
      rw [sub_eq_add_neg]
      change f ((.ofAdd j) * (.ofAdd i)⁻¹) = (f (.ofAdd i))⁻¹ * f (.ofAdd j)
      rw [map_mul, map_inv]
      simpa only [map_inv] using (Commute.map (Commute.all (.ofAdd j) ((.ofAdd i)⁻¹)) f).eq


variable {G : Type*} [Group G]

private lemma presentationHom_r_one (c d : G) (hc : c ^ 8 = 1) (hd : d ^ 2 = 1)
    (hconj : d * c * d⁻¹ = c⁻¹) :
    presentationHom c d hc hd hconj (.r 1) = c := by
  exact rotation_one c hc

private lemma presentationHom_sr_zero (c d : G) (hc : c ^ 8 = 1) (hd : d ^ 2 = 1)
    (hconj : d * c * d⁻¹ = c⁻¹) :
    presentationHom c d hc hd hconj (.sr 0) = d := by
  change d * c ^ (0 : ZMod 8).val = d
  simp

private lemma dihedralHom_injective (f : DihedralGroup 8 →* G) (hf : f (.r 4) ≠ 1) :
    Function.Injective f := by
  apply (injective_iff_map_eq_one f).mpr
  rintro (i | i) hi
  · by_cases h0 : i = 0
    · subst i; rfl
    · have hex : ∀ i : ZMod 8, i ≠ 0 →
          ∃ k : Fin 8, (DihedralGroup.r i) ^ k.val = DihedralGroup.r 4 := by decide +kernel
      obtain ⟨k, hk⟩ := hex i h0
      exact (hf (by rw [← hk, map_pow, hi, one_pow])).elim
  · have he : ((DihedralGroup.sr i * .r 1 * (DihedralGroup.sr i)⁻¹ *
          (DihedralGroup.r 1)⁻¹) ^ 2 : DihedralGroup 8) = .r 4 := by
      simp only [DihedralGroup.inv_sr, DihedralGroup.inv_r, DihedralGroup.sr_mul_r,
        DihedralGroup.sr_mul_sr, DihedralGroup.r_mul_r, DihedralGroup.r_pow]
      congr 1
      ring_nf
      rfl
    apply False.elim
    apply hf
    rw [← he, map_pow, map_mul, map_mul, map_mul, map_inv, map_inv, hi]
    simp

/-- Two generating involutions give the marked order-sixteen dihedral group
when their product has eighth power one and nonidentity fourth power. -/
theorem markedEquiv_of_involutions (a b : G) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (h8 : (a * b) ^ 8 = 1) (h4 : (a * b) ^ 4 ≠ 1)
    (hgen : Subgroup.closure ({a, b} : Set G) = ⊤) :
    ∃ e : G ≃* DihedralGroup 8, e a = .sr 0 ∧ e b = .sr 1 := by
  have haa : a * a = 1 := by simpa only [pow_two] using ha
  have hbb : b * b = 1 := by simpa only [pow_two] using hb
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have hconj : a * (a * b) * a⁻¹ = (a * b)⁻¹ := by
    simp only [mul_inv_rev, hai, hbi, ← mul_assoc, haa, one_mul]
  let f := presentationHom (a * b) a h8 ha hconj
  have hfa : f (.sr 0) = a := presentationHom_sr_zero _ _ _ _ _
  have hfc : f (.r 1) = a * b := presentationHom_r_one _ _ _ _ _
  have hfb : f (.sr 1) = b := by
    have h : (DihedralGroup.sr 1 : DihedralGroup 8) = .sr 0 * .r 1 := by decide
    rw [h, map_mul, hfa, hfc, ← mul_assoc, haa, one_mul]
  have hfi : Function.Injective f := by
    apply dihedralHom_injective
    have h : (DihedralGroup.r 4 : DihedralGroup 8) = .r 1 ^ 4 := by decide
    rwa [h, map_pow, hfc]
  have hfs : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    apply top_unique
    rw [← hgen]
    apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact ⟨.sr 0, hfa⟩
    · rw [Set.mem_singleton_iff] at hx
      subst x
      exact ⟨.sr 1, hfb⟩
  let e := MulEquiv.ofBijective f ⟨hfi, hfs⟩
  refine ⟨e.symm, ?_, ?_⟩
  · exact e.symm_apply_eq.mpr hfa.symm
  · exact e.symm_apply_eq.mpr hfb.symm

end ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry.MarkedWeyl
