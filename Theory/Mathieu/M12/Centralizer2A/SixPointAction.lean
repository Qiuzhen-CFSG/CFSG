module

public import Theory.Mathieu.M12.Centralizer2A.Data

/-!
# The faithful six-point action of S₅

Conjugation permutes the six cyclic subgroups of order five. The transposition
certificates extend to all permutations by swap induction. Faithfulness reduces
to the twenty-element normalizer of the first label: only its identity also
fixes the second and third labels. This action is the S₅ factor in the concrete
M₁₂ centralizer construction (Aschbacher–Smith 16.1.5(4), p.1171).
-/

@[expose] public section
namespace Sporadic.Mathieu.M12Centralizer2A
set_option maxRecDepth 10000

theorem swap_spec (a b : Fin 5) (i : Fin 6) :
    conjugate (Equiv.swap a b) (label i) = label (swapIndex a b i) := by
  have hsurj : Function.Surjective (powerIndex a b i) :=
    (by decide +kernel : ∀ a b i, Function.Surjective (powerIndex a b i)) a b i
  simp only [conjugate, label, Finset.image_image, Function.comp_def]
  simp_rw [swap_cycle]
  have himage := Finset.image_image (s := Finset.univ) (f := powerIndex a b i)
    (g := fun j : Fin 4 => cycle ⟨4*(swapIndex a b i).val+j.val, by omega⟩)
  rw [Finset.image_univ_of_surjective hsurj] at himage
  exact himage.symm

theorem swap_stable (a b : Fin 5) (i : Fin 6) :
    ∃ j : Fin 6, conjugate (Equiv.swap a b) (label i) = label j :=
  ⟨swapIndex a b i, swap_spec a b i⟩

theorem kernel_trivial (s : Equiv.Perm (Fin 5))
    (hs : ∀ i : Fin 6, conjugate s (label i) = label i) : s = 1 := by
  have hc : cycle 0 ∈ label 0 := by decide +kernel
  have hm : s * cycle 0 * s⁻¹ ∈ label 0 := by
    rw [← hs 0]
    exact Finset.mem_image.mpr ⟨cycle 0, hc, rfl⟩
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hm
  let d := cycle ⟨j.val, by omega⟩
  have he : SemiconjBy s (cycle 0) d := by
    change s * cycle 0 = d * s
    simp only [Fin.val_zero, Nat.mul_zero, zero_add] at hj
    change d = s * cycle 0 * s⁻¹ at hj
    rw [hj]
    simp [mul_assoc]
  let q := normalizerPerm (s 0) j
  have hq : SemiconjBy q (cycle 0) d :=
    normalizer_semiconj_eq (s 0) j
  have hq0 : q 0 = s 0 :=
    normalizer_zero (s 0) j
  have seq : s = q := by
    apply Equiv.ext
    intro x
    obtain ⟨n, hn⟩ := (by decide +kernel : ∀ x : Fin 5,
      ∃ n : Fin 5, (cycle 0 ^ n.val) 0 = x) x
    rw [← hn]
    exact (congrArg (fun p : Equiv.Perm (Fin 5) => p 0) (he.pow_right n.val).eq).trans
      (by simpa only [Equiv.Perm.mul_apply, hq0] using
        (congrArg (fun p : Equiv.Perm (Fin 5) => p 0) (hq.pow_right n.val).eq).symm)
  have hsmall : ∀ x j,
      conjugate (normalizerPerm x j) (label 1) = label 1 →
      conjugate (normalizerPerm x j) (label 2) = label 2 → normalizerPerm x j = 1 := by
    decide +kernel
  rw [seq]
  apply hsmall (s 0) j
  · change conjugate q (label 1) = label 1
    rw [← seq]
    exact hs 1
  · change conjugate q (label 2) = label 2
    rw [← seq]
    exact hs 2

theorem conjugate_one (L : Finset (Equiv.Perm (Fin 5))) : conjugate 1 L = L := by
  simp [conjugate]

theorem conjugate_mul (s t : Equiv.Perm (Fin 5)) (L : Finset (Equiv.Perm (Fin 5))) :
    conjugate (s*t) L = conjugate s (conjugate t L) := by
  simp [conjugate, Finset.image_image, Function.comp_def, mul_assoc]

theorem stable (s : Equiv.Perm (Fin 5)) : ∀ i : Fin 6,
    ∃ j : Fin 6, conjugate s (label i) = label j := by
  induction s using Equiv.Perm.swap_induction_on with
  | one => intro i; exact ⟨i, conjugate_one _⟩
  | swap_mul s a b _ ih =>
    intro i
    obtain ⟨j,hj⟩ := ih i
    obtain ⟨k,hk⟩ := swap_stable a b j
    exact ⟨k, by rw [conjugate_mul, hj, hk]⟩

noncomputable def act (s : Equiv.Perm (Fin 5)) (i : Fin 6) : Fin 6 :=
  Classical.choose (stable s i)

theorem act_spec (s : Equiv.Perm (Fin 5)) (i : Fin 6) :
    conjugate s (label i) = label (act s i) := Classical.choose_spec (stable s i)

theorem act_one (i : Fin 6) : act 1 i = i := by
  apply label_injective
  rw [← act_spec, conjugate_one]

theorem act_mul (s t : Equiv.Perm (Fin 5)) (i : Fin 6) :
    act (s*t) i = act s (act t i) := by
  apply label_injective
  rw [← act_spec, conjugate_mul, act_spec, act_spec]

noncomputable def sixAction : Equiv.Perm (Fin 5) →* Equiv.Perm (Fin 6) where
  toFun s := {
    toFun := act s
    invFun := act s⁻¹
    left_inv := fun i => by rw [← act_mul, inv_mul_cancel, act_one]
    right_inv := fun i => by rw [← act_mul, mul_inv_cancel, act_one] }
  map_one' := Equiv.ext act_one
  map_mul' s t := Equiv.ext (act_mul s t)

theorem sixAction_injective : Function.Injective sixAction := by
  apply (injective_iff_map_eq_one sixAction).mpr
  intro s hs
  apply kernel_trivial s
  intro i
  rw [act_spec]
  exact congrArg label (congrArg (fun p : Equiv.Perm (Fin 6) => p i) hs)

theorem sixAction_swap (a b : Fin 5) (i : Fin 6) :
    sixAction (Equiv.swap a b) i = swapIndex a b i := by
  apply label_injective
  exact (act_spec _ _).symm.trans (swap_spec a b i)

end Sporadic.Mathieu.M12Centralizer2A
