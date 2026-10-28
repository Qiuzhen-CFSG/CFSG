module

public import Theory.Alternating.Aut
public import Theory.Representation.BinaryPermutationAlternatingActions
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.Tactic

/-!
# Faithful normal extensions of the seven-point binary core action

Conjugation on the marked A₇ defines a homomorphism to Aut(A₇) = S₇.
The linear centralizer of A₇ on its augmentation core is trivial: its
seven weight-six vectors span, and a letter stabilizer fixes only the
corresponding line. This makes the homomorphism equivariant for the
original linear action; faithfulness then makes it injective.

Adapted from the proved Chapter 13 `SevenExtension.faithful_extension`,
without importing that later chapter. Both A₇ and S₇ extensions are allowed.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), §B.3,
G.11.2(4), and the final argument of 12.8.13, printed pp.856–857.
-/

public section
open BinaryPermutation Equiv
namespace BinaryPermutation.SevenParabolic
private def point (i : Fin 7) : core (Fin 7) :=
  ⟨fun j => if j = i then 0 else 1, by rw [mem_core]; fin_cases i <;> decide⟩

private lemma point_ne_zero (i : Fin 7) : point i ≠ 0 := by
  fin_cases i <;> decide

private lemma action_point (g : Perm (Fin 7)) (i : Fin 7) :
    coreRepresentation (Fin 7) g (point i) = point (g i) := by
  apply Subtype.ext
  ext j
  simp [point, ← Equiv.eq_symm_apply]

private def restCycle (i : Fin 7) (_hi : i ≠ 1) (hi2 : i ≠ 2) :
    alternatingGroup (Fin 7) :=
  ⟨swap 1 2 * swap 2 i, by
    simp [Perm.mem_alternatingGroup, Perm.sign_swap (by decide : (1 : Fin 7) ≠ 2),
      Perm.sign_swap hi2.symm]⟩

private lemma fixes_point_zero (f : core (Fin 7) ≃ₗ[ZMod 2] core (Fin 7))
    (hf : ∀ g : alternatingGroup (Fin 7), ∀ v,
      f (alternatingCoreRepresentation (Fin 7) g v) =
        alternatingCoreRepresentation (Fin 7) g (f v)) : f (point 0) = point 0 := by
  let w := f (point 0)
  have hfix (g : alternatingGroup (Fin 7)) (hg : g.val 0 = 0) :
      coreRepresentation (Fin 7) g.val w = w := by
    change alternatingCoreRepresentation (Fin 7) g (f (point 0)) = _
    rw [← hf]
    change f (coreRepresentation (Fin 7) g.val (point 0)) = _
    rw [action_point, hg]
  have hcy (i : Fin 7) (hi0 : i ≠ 0) (hi1 : i ≠ 1) (hi2 : i ≠ 2) :
      w.val i = w.val 1 := by
    have h := congrArg (fun v : core (Fin 7) => v.val 1)
      (hfix (restCycle i hi1 hi2) (by
        simp [restCycle, Perm.mul_def, swap_apply_of_ne_of_ne, hi0.symm]))
    simpa [restCycle, Perm.mul_def] using h
  have heq (i : Fin 7) (hi : i ≠ 0) : w.val i = w.val 1 := by
    by_cases hi1 : i = 1
    · rw [hi1]
    by_cases hi2 : i = 2
    · subst i
      have h := congrArg (fun v : core (Fin 7) => v.val 2)
        (hfix (restCycle 3 (by decide) (by decide)) (by decide))
      symm
      simpa [restCycle, Perm.mul_def, swap_apply_of_ne_of_ne] using h
    · exact hcy i hi hi1 hi2
  have hw0 : w.val 0 = 0 := by
    have h := w.property
    rw [mem_core] at h
    simpa [Fin.sum_univ_succ, heq 2 (by decide), heq 3 (by decide),
      heq 4 (by decide), heq 5 (by decide), heq 6 (by decide),
      CharTwo.add_self_eq_zero, add_assoc] using h
  have hw1 : w.val 1 = 1 := by
    have hb : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases hb (w.val 1) with h | h
    · have hz : w = 0 := by
        apply Subtype.ext
        ext i
        by_cases hi : i = 0
        · subst i; exact hw0
        · simpa [h] using heq i hi
      exact (point_ne_zero 0 (f.injective (hz.trans f.map_zero.symm))).elim
    · exact h
  change w = point 0
  apply Subtype.ext
  ext i
  by_cases hi : i = 0
  · subst i; exact hw0
  · simpa [point, hi, hw1] using heq i hi

theorem linearCentralizer_eq_one (f : core (Fin 7) ≃ₗ[ZMod 2] core (Fin 7))
    (hf : ∀ g : alternatingGroup (Fin 7), ∀ v,
      f (alternatingCoreRepresentation (Fin 7) g v) =
        alternatingCoreRepresentation (Fin 7) g (f v)) : f = 1 := by
  have hp0 := fixes_point_zero f hf
  have := alternatingGroup.isMultiplyPretransitive (Fin 7)
  have ht : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin 7)) (Fin 7) 2 :=
    MulAction.isMultiplyPretransitive_of_le (n := Nat.card (Fin 7) - 2)
      (by simp) (Nat.sub_le _ _)
  have hp (i : Fin 7) : f (point i) = point i := by
    obtain ⟨j, hj⟩ := exists_ne i
    obtain ⟨g, hg, _⟩ := (MulAction.is_two_pretransitive_iff.mp ht)
      (by decide : (0 : Fin 7) ≠ 1) hj.symm
    have hg' : g.val 0 = i := hg
    have h := hf g (point 0)
    change f (coreRepresentation _ g.val (point 0)) = coreRepresentation _ g.val (f (point 0)) at h
    rwa [hp0, action_point, hg'] at h
  have hspan (v : core (Fin 7)) : ∑ i, v.val i • point i = v := by
    apply Subtype.ext
    ext j
    simp only [Submodule.coe_sum, Finset.sum_apply, SetLike.val_smul, Pi.smul_apply,
      smul_eq_mul, point]
    have hz : ∑ i, v.val i = 0 := v.property
    have hs : (∑ i, v.val i * (if j = i then 0 else 1)) = ∑ i ∈ Finset.univ.erase j, v.val i := by
      simp only [mul_ite, mul_zero, mul_one, Finset.sum_ite, Finset.sum_const_zero, zero_add]
      apply Finset.sum_congr
      · ext i; simp [ne_comm]
      · intro i _; rfl
    rw [hs, Finset.sum_erase_eq_sub (Finset.mem_univ j), hz]
    exact CharTwo.neg_eq _
  apply LinearEquiv.ext
  intro v
  calc
    f v = f (∑ i, v.val i • point i) := congrArg f (hspan v).symm
    _ = ∑ i, v.val i • point i := by simp only [map_sum, map_smul, hp]
    _ = v := hspan v

private theorem action_of_conjugation
    (c : core (Fin 7) ≃ₗ[ZMod 2] core (Fin 7)) (s : Perm (Fin 7))
    (hc : ∀ g : alternatingGroup (Fin 7), ∀ v,
      c (coreRepresentation (Fin 7) g.val v) =
        coreRepresentation (Fin 7) (s * g.val * s⁻¹) (c v)) :
    ∀ v, c v = coreRepresentation (Fin 7) s v := by
  let R := coreRepresentation (Fin 7)
  let d := c.trans (LinearMap.GeneralLinearGroup.toLinearEquiv (R.asGroupHom s⁻¹))
  have hd : d = 1 := by
    apply linearCentralizer_eq_one
    intro g v
    change R s⁻¹ (c (R g.val v)) = R g.val (R s⁻¹ (c v))
    rw [hc]
    change (R s⁻¹ * R (s * g.val * s⁻¹)) (c v) =
      (R g.val * R s⁻¹) (c v)
    rw [← map_mul, ← map_mul]
    congr 2
    group
  intro v
  have hv := congrArg (fun e : core (Fin 7) ≃ₗ[ZMod 2] core (Fin 7) => e v) hd
  change R s⁻¹ (c v) = v at hv
  have hh := congrArg (R s) hv
  simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply] using hh

/-- Every faithful normal extension of the prescribed A₇ core action has a faithful
seven-letter permutation embedding. Both the component marking and all module
coordinates are retained; the linear centralizer is proved trivial internally. -/
theorem faithful_extension
    {A E : Type*} [Group A] [AddCommGroup E] [Module (ZMod 2) E]
    (K : Subgroup A) [K.Normal]
    (ρ : Representation (ZMod 2) A E) (hρ : Function.Injective ρ)
    (eK : K ≃* alternatingGroup (Fin 7))
    (eV : E ≃ₗ[ZMod 2] core (Fin 7))
    (he : ∀ k : K, ∀ v, eV (ρ k v) =
      alternatingCoreRepresentation (Fin 7) (eK k) (eV v)) :
    ∃ f : A →* Perm (Fin 7), Function.Injective f ∧
      (∀ k : K, f k = (eK k).val) ∧
      ∀ a v, eV (ρ a v) = coreRepresentation (Fin 7) (f a) (eV v) := by
  let eS : Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) :=
    MulEquiv.ofBijective MulAut.conjNormal
      (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by decide) (by decide))
  let α : A →* MulAut (alternatingGroup (Fin 7)) :=
    (MulAut.congr eK).toMonoidHom.comp (MulAut.conjNormal (H := K))
  let f : A →* Perm (Fin 7) := eS.symm.toMonoidHom.comp α
  have hconj (a : A) : MulAut.conjNormal (f a) = MulAut.congr eK (MulAut.conjNormal a) :=
    eS.apply_symm_apply (α a)
  have hfK (k : K) : f k = (eK k).val := by
    apply eS.injective
    change MulAut.conjNormal (f k) = MulAut.conjNormal (eK k).val
    rw [hconj, MulAut.conjNormal_val, MulAut.conjNormal_val]
    ext x
    simp [MulAut.congr_apply, MulAut.conj_apply]
  have hconjK (a : A) (k : K) :
      f a * (eK k).val * (f a)⁻¹ = (eK (MulAut.conjNormal a k)).val := by
    have h := congrArg (fun β : MulAut (alternatingGroup (Fin 7)) => (β (eK k)).val) (hconj a)
    simpa [MulAut.congr_apply] using h
  have hact (a : A) (v : E) : eV (ρ a v) = coreRepresentation (Fin 7) (f a) (eV v) := by
    let c := eV.symm.trans ((LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom a)).trans eV)
    have hc : ∀ g : alternatingGroup (Fin 7), ∀ w,
        c (coreRepresentation (Fin 7) g.val w) =
          coreRepresentation (Fin 7) (f a * g.val * (f a)⁻¹) (c w) := by
      intro g w
      obtain ⟨k, rfl⟩ := eK.surjective g
      have hinv : eV.symm (coreRepresentation (Fin 7) (eK k).val w) = ρ k (eV.symm w) := by
        apply eV.injective
        simpa using (he k (eV.symm w)).symm
      change eV (ρ a (eV.symm (coreRepresentation (Fin 7) (eK k).val w))) =
        coreRepresentation (Fin 7) (f a * (eK k).val * (f a)⁻¹) (eV (ρ a (eV.symm w)))
      rw [hinv, hconjK]
      change eV (ρ a (ρ k (eV.symm w))) =
        alternatingCoreRepresentation (Fin 7) (eK (MulAut.conjNormal a k))
          (eV (ρ a (eV.symm w)))
      rw [← he]
      congr 1
      change (ρ a * ρ k) (eV.symm w) = (ρ (MulAut.conjNormal a k) * ρ a) (eV.symm w)
      rw [← map_mul, ← map_mul, MulAut.conjNormal_apply, inv_mul_cancel_right]
    have h := action_of_conjugation c (f a) hc (eV v)
    simpa [c, Representation.asGroupHom_apply] using h
  refine ⟨f, ?_, hfK, hact⟩
  intro a b hab
  apply hρ
  ext v
  apply eV.injective
  rw [hact, hact, hab]

end BinaryPermutation.SevenParabolic
