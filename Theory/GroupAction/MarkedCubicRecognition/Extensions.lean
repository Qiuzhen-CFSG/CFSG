module
public import Theory.GroupAction.MarkedCubicRecognition.Models
public import Theory.GroupAction.ElementaryNineFourSemidirect

/-!
# Marked complements and ambient reconstruction

Two distinct commuting involutions identify an actual four-group with
E₄, including both generator values. Equivariance on these generators
extends to the full actor. Applying the internal semidirect-product
isomorphism then retains the normal subgroup and complement inclusions.
The elementary model gives S₃ × S₃ through its independent inversions.

Source: Aschbacher–Smith, The Classification of Quasithin Groups,
F.6.16, printed p.308 (1 March 2004 manuscript).
-/

@[expose] public section
namespace MarkedCubicRecognition
open Subgroup

/-- Exhaust the fixed four-group by its marked generators. -/
theorem four_cases (t : Four) : t = 1 ∨ t = first ∨ t = second ∨ t = first * second := by
  revert t
  decide

/-- Two distinct nontrivial commuting involutions embed the fixed four-group. -/
theorem fourHom_injective {P : Type*} [Group P] (x y : P)
    (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (hxy : Commute x y)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hne : x ≠ y) :
    Function.Injective (fourHom x y hx hy hxy) := by
  apply (injective_iff_map_eq_one _).mpr
  intro t ht
  rcases four_cases t with rfl | rfl | rfl | rfl
  · rfl
  · exact (hx1 (by simpa using ht)).elim
  · exact (hy1 (by simpa using ht)).elim
  · have hh : x * y = 1 := by simpa using ht
    exact (hne (calc
      x = x * (y * y) := by rw [← pow_two, hy, mul_one]
      _ = (x * y) * y := (mul_assoc ..).symm
      _ = y := by rw [hh, one_mul])).elim

/-- On a group of order four the embedding is an isomorphism with the specified values. -/
theorem exists_four_equiv {T : Type*} [Group T] [Finite T]
    (hcard : Nat.card T = 4) (x y : T)
    (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (hxy : Commute x y)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hne : x ≠ y) :
    ∃ e : Four ≃* T, e first = x ∧ e second = y ∧ zpowers x ⊔ zpowers y = ⊤ := by
  have hf := fourHom_injective x y hx hy hxy hx1 hy1 hne
  have hs := hf.bijective_of_nat_card_le (by simp [Four, C2, hcard])
  let e := MulEquiv.ofBijective (fourHom x y hx hy hxy) hs
  refine ⟨e, fourHom_first x y hx hy hxy, fourHom_second x y hx hy hxy, ?_⟩
  have hh := MonoidHom.range_eq_top.mpr hs.surjective
  have hr := MonoidHom.noncommCoprod_range (cyclicHom x hx) (cyclicHom y hy)
    (fun _ _ => hxy.pow_pow _ _)
  rw [cyclicHom_range (by decide), cyclicHom_range (by decide)] at hr
  exact hr.symm.trans hh

/-- Equivariance on the two distinguished involutions is equivariance on E₄. -/
theorem four_equivariant {M P T : Type*} [Group M] [Group P] [Group T]
    (ρ : Four →* MulAut M) (σ : T →* MulAut P)
    (e : M ≃* P) (d : Four →* T)
    (hfirst : ∀ z, e (ρ first z) = σ (d first) (e z))
    (hsecond : ∀ z, e (ρ second z) = σ (d second) (e z)) :
    ∀ t z, e (ρ t z) = σ (d t) (e z) := by
  intro t z
  rcases four_cases t with rfl | rfl | rfl | rfl
  · simp
  · exact hfirst z
  · exact hsecond z
  · simp only [map_mul, MulAut.mul_apply, hfirst, hsecond]

/-- Independent coordinate inversions give S₃ × S₃. -/
theorem nineExtension_equiv_symmetric_product :
    Nonempty (NineExtension ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  let : IsElementaryAbelian 3 Nine := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by decide) }
  let : IsElementaryAbelian 2 Four := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by decide) }
  apply ElementaryNineFourSemidirect.nonempty_mulEquiv nineAction
    (by simp [Nine, C3]) (by simp [Four, C2])
    (fourHom_injective nineLeftFlip nineRightFlip nineLeftFlip_sq nineRightFlip_sq
      nineFlips_commute ?_ ?_ ?_) ((MonoidHom.inl C3 C3).range) ?_ ?_
  · intro he
    have hh := DFunLike.congr_fun he (Multiplicative.ofAdd 1, 1)
    have hf := congrArg (fun z : Nine => z.1.toAdd) hh
    change (-1 : ZMod 3) = 1 at hf
    contradiction
  · intro he
    have hh := DFunLike.congr_fun he (1, Multiplicative.ofAdd 1)
    have hf := congrArg (fun z : Nine => z.2.toAdd) hh
    change (-1 : ZMod 3) = 1 at hf
    contradiction
  · intro he
    have hh := DFunLike.congr_fun he (Multiplicative.ofAdd 1, 1)
    have hf := congrArg (fun z : Nine => z.1.toAdd) hh
    change (-1 : ZMod 3) = 1 at hf
    contradiction
  · rw [Nat.card_congr (MonoidHom.ofInjective
      (show Function.Injective (MonoidHom.inl C3 C3) from fun _ _ he =>
        congrArg Prod.fst he)).toEquiv.symm]
    simp [C3]
  · intro t z hz
    obtain ⟨w, rfl⟩ := hz
    rcases four_cases t with rfl | rfl | rfl | rfl
    · simp
    · exact ⟨w⁻¹, rfl⟩
    · refine ⟨w, ?_⟩
      change (w, 1) = (w, (1 : C3)⁻¹)
      simp
    · exact ⟨w⁻¹, rfl⟩

/-- Reconstruct an internal semidirect product while retaining the literal
normal-subgroup inclusion and every element of the chosen complement. -/
theorem exists_internal_extension {G M : Type*} [Group G] [Group M]
    (L T : Subgroup G) [L.Normal] (hcomp : L.IsComplement' T)
    (ρ : Four →* MulAut M) (eM : M ≃* L) (eT : Four ≃* T)
    (hfirst : ∀ z, eM (ρ first z) = MulAut.conjNormal (eT first : G) (eM z))
    (hsecond : ∀ z, eM (ρ second z) = MulAut.conjNormal (eT second : G) (eM z)) :
    ∃ e : (M ⋊[ρ] Four) ≃* G,
      (∀ z, e (SemidirectProduct.inl z) = (eM z : G)) ∧
      (∀ t, e (SemidirectProduct.inr t) = (eT t : G)) := by
  let σ : T →* MulAut L :=
    L.normalizerMonoidHom.comp (inclusion (L.normalizer_eq_top ▸ le_top))
  have hh : ∀ t : Four, (ρ t).trans eM = eM.trans (σ (eT t)) := by
    intro t
    apply MulEquiv.ext
    intro z
    exact four_equivariant ρ σ eM eT.toMonoidHom hfirst hsecond t z
  let e := (SemidirectProduct.congr eM eT hh).trans (SemidirectProduct.mulEquivSubgroup hcomp)
  refine ⟨e, ?_, ?_⟩
  · intro z
    change (eM z : G) * (eT 1 : G) = (eM z : G)
    simp
  · intro t
    change (eM 1 : G) * (eT t : G) = (eT t : G)
    simp

end MarkedCubicRecognition
