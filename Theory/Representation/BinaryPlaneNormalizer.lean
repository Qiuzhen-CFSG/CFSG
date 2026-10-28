module

public import Theory.GroupTheory.SymmetricThreeTwoCore
public import Theory.GroupTheory.PPerfectHom
public import Mathlib.RepresentationTheory.Coinvariants
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# Two-perfect normalizers of binary rank-two S₃ actions

For a faithful binary representation of S₃, the kernel on the moved space
fixes both that space and its quotient. Its elements therefore square to one,
so the kernel lies in the trivial two-core of S₃. If the moved space has
rank two, averaging over the cubic subgroup splits it off from the fixed
space: a nonidentity cubic operator on the binary plane satisfies t²+t+1=0.

A two-perfect group fixing a nonzero vector of a binary plane acts trivially
there, since the invertible operators fixing that vector square to one.
Consequently a two-perfect normalizer either centralizes the S₃ subgroup
or has its fixed space contained in the S₃ fixed space. Every action used
here is the restriction of the specified ambient representation.

Source: the elementary representation argument used in Aschbacher–Smith,
combined manuscript (1 March 2004), proof of 15.3.49(i), printed pp.1143–1144,
with the rank-two factors of B.5.6, printed pp.105–110.
-/

public section

open Subgroup Representation
open scoped commutatorElement

namespace Representation.BinaryPlaneNormalizer
variable {K V : Type*} [Group K] [AddCommGroup V] [Module (ZMod 2) V]

private lemma add_self (v : V) : v + v = 0 := by
  have h := @two_smul (ZMod 2) V _ _ _ v
  simpa only [show (2 : ZMod 2) = 0 from by decide, zero_smul] using h.symm

private lemma neg_self (v : V) : -v = v :=
  (eq_neg_iff_add_eq_zero.mpr (add_self v)).symm

private lemma moved_stable (ρ : Representation (ZMod 2) K V) (g : K) :
    ∀ v ∈ Coinvariants.ker ρ, ρ g v ∈ Coinvariants.ker ρ := by
  intro v hv
  have hle : Coinvariants.ker ρ ≤ (Coinvariants.ker ρ).comap (ρ g) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨k, w⟩, rfl⟩
    change ρ g (ρ k w - w) ∈ Coinvariants.ker ρ
    convert Coinvariants.sub_mem_ker (ρ := ρ) (g * k * g⁻¹) (ρ g w) using 1
    ·
      simp [map_sub, ← Module.End.mul_apply, ← map_mul, mul_assoc]
  exact hle hv

/-- The actual action on the space spanned by all action differences. -/
noncomputable def movedRepresentation (ρ : Representation (ZMod 2) K V) :
    Representation (ZMod 2) K (Coinvariants.ker ρ) :=
  ρ.subrepresentation _ (moved_stable ρ)

private lemma movedRepresentation_ker_twoGroup (ρ : Representation (ZMod 2) K V)
    (hf : Function.Injective ρ) : IsPGroup 2 (movedRepresentation ρ).ker := by
  intro x
  refine ⟨1, ?_⟩
  apply Subtype.ext
  apply hf
  ext v
  have hd := LinearMap.congr_fun (MonoidHom.mem_ker.mp x.property)
    (⟨ρ x v - v, Coinvariants.sub_mem_ker (ρ := ρ) x v⟩ : Coinvariants.ker ρ)
  have hd' := congrArg Subtype.val hd
  change ρ x (ρ x v - v) = ρ x v - v at hd'
  rw [map_sub] at hd'
  have hv : ρ x (ρ x v) = v := by
    apply add_right_cancel (b := v)
    exact (sub_eq_sub_iff_add_eq_add.mp hd').trans ((add_self _).trans (add_self v).symm)
  change ρ ((x : K) ^ (2 ^ 1)) v = ρ (1 : K) v
  simpa only [pow_one, pow_two, map_mul, Module.End.mul_apply,
    map_one, Module.End.one_apply] using hv

/-- A faithful binary S₃ action remains faithful on its moved space. -/
theorem movedRepresentation_faithful [Finite K] (ρ : Representation (ZMod 2) K V)
    (hf : Function.Injective ρ) (e : K ≃* Equiv.Perm (Fin 3)) :
    Function.Injective (movedRepresentation ρ) := by
  have hcore : pCore 2 K = ⊥ := by
    rw [← ker_eq_twoCore_of_surjective_perm_three e.toMonoidHom e.surjective
      (by rw [e.toMonoidHom.ker_eq_bot e.injective]; exact IsPGroup.of_card (n := 0) (by simp))]
    exact e.toMonoidHom.ker_eq_bot e.injective
  apply (MonoidHom.ker_eq_bot_iff _).mp
  exact le_bot_iff.mp ((show (movedRepresentation ρ).ker ≤ pCore 2 K from
    le_sSup ⟨inferInstance, movedRepresentation_ker_twoGroup ρ hf⟩).trans_eq hcore)

private lemma matrix_cubic_norm : ∀ t : Matrix (Fin 2) (Fin 2) (ZMod 2),
    t ^ 3 = 1 → t ≠ 1 → t ^ 2 + t + 1 = 0 := by decide +kernel

private lemma plane_cubic_norm {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (hd : Module.finrank (ZMod 2) W = 2) (t : Module.End (ZMod 2) W)
    (ht : t ^ 3 = 1) (hne : t ≠ 1) : t ^ 2 + t + 1 = 0 := by
  let := Module.finite_of_finrank_pos (R := ZMod 2) (M := W) (by omega)
  let b := Module.finBasisOfFinrankEq (ZMod 2) W hd
  let m := LinearMap.toMatrixAlgEquiv b
  apply m.injective
  simpa only [map_add, map_pow, map_one, map_zero] using
    matrix_cubic_norm (m t) (by simp only [← map_pow, ht, map_one])
      (fun h => hne (m.injective (by simpa only [map_one] using h)))

private lemma exists_cubic (e : K ≃* Equiv.Perm (Fin 3)) :
    ∃ t : K, t ^ 3 = 1 ∧ t ≠ 1 ∧
      ∀ g : K, g⁻¹ * t * g = t ∨ g⁻¹ * t * g = t ^ 2 := by
  let c : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2
  have hc : c ^ 3 = 1 ∧ c ≠ 1 ∧
      ∀ g : Equiv.Perm (Fin 3), g⁻¹ * c * g = c ∨ g⁻¹ * c * g = c ^ 2 := by
    decide +kernel
  refine ⟨e.symm c, ?_, ?_, ?_⟩
  · apply e.injective
    simpa only [map_pow, e.apply_symm_apply, map_one] using hc.1
  · intro h
    exact hc.2.1 (by simpa using congrArg e h)
  · intro g
    rcases hc.2.2 (e g) with h | h
    · left
      apply e.injective
      simpa only [map_mul, map_inv, e.apply_symm_apply] using h
    · right
      apply e.injective
      simpa only [map_mul, map_inv, map_pow, e.apply_symm_apply] using h

/-- A faithful S₃ action with a two-dimensional moved space splits as
that plane and the fixed space. The cubic averaging operator gives the split. -/
theorem symmetric_three_split [Finite K] (ρ : Representation (ZMod 2) K V)
    (hf : Function.Injective ρ) (e : K ≃* Equiv.Perm (Fin 3))
    (hd : Module.finrank (ZMod 2) (Coinvariants.ker ρ) = 2) :
    IsCompl (Coinvariants.ker ρ) ρ.invariants := by
  obtain ⟨t, ht, htne, hconj⟩ := exists_cubic e
  have hmf := movedRepresentation_faithful ρ hf e
  have hmne : movedRepresentation ρ t ≠ 1 := fun he => htne (hmf (he.trans (map_one _).symm))
  have hnorm := plane_cubic_norm hd (movedRepresentation ρ t)
    (by rw [← map_pow, ht, map_one]) hmne
  have hnormv (w : Coinvariants.ker ρ) :
      ρ t (ρ t w) + ρ t w + (w : V) = 0 :=
    congrArg Subtype.val (LinearMap.congr_fun hnorm w)
  have hzero (v : V) (hv : v ∈ Coinvariants.ker ρ) (htv : ρ t v = v) : v = 0 := by
    have h := hnormv ⟨v, hv⟩
    change ρ t (ρ t v) + ρ t v + v = 0 at h
    simpa only [htv, add_self, zero_add] using h
  have hcubic (v : V) : ρ t (ρ t (ρ t v)) = v := by
    calc
      _ = ρ (t ^ 3) v := by simp [pow_succ, map_mul, Module.End.mul_apply]
      _ = v := by rw [ht, map_one]; rfl
  have hinv (v : V) (hv : ρ t v = v) : v ∈ ρ.invariants := by
    intro g
    have hconjv : ρ (g⁻¹ * t * g) v = v := by
      rcases hconj g with h | h
      · rw [h, hv]
      · rw [h, pow_two, map_mul, Module.End.mul_apply, hv, hv]
    have htg : ρ t (ρ g v) = ρ g v := by
      have h := congrArg (ρ g) hconjv
      simpa only [← Module.End.mul_apply, ← map_mul, mul_assoc, mul_inv_cancel_left] using h
    exact sub_eq_zero.mp (hzero (ρ g v - v) (Coinvariants.sub_mem_ker g v)
      (by rw [map_sub, htg, hv]))
  constructor
  · apply Submodule.disjoint_def.mpr
    intro v hv hi
    exact hzero v hv (hi t)
  · apply codisjoint_iff.mpr
    apply top_unique
    intro v _
    let c := ρ t (ρ t v) + ρ t v + v
    have hc : c ∈ ρ.invariants := by
      apply hinv
      dsimp [c]
      rw [map_add, map_add, hcubic]
      abel
    have hw : v - c ∈ Coinvariants.ker ρ := by
      have h2 := Coinvariants.sub_mem_ker (ρ := ρ) t (ρ t v)
      have he : v - c = -(ρ t (ρ t v) - ρ t v) := by
        dsimp [c]
        rw [sub_eq_add_neg (ρ t (ρ t v)), neg_self (ρ t v)]
        abel
      rw [he]
      exact (Coinvariants.ker ρ).neg_mem h2
    exact Submodule.mem_sup.mpr ⟨v - c, hw, c, hc, sub_add_cancel v c⟩

private lemma matrix_nonzero_fixed_square :
    ∀ a b : Matrix (Fin 2) (Fin 2) (ZMod 2), a * b = 1 →
      ∀ w : Fin 2 → ZMod 2, w ≠ 0 → a.mulVec w = w → a * a = 1 := by
  decide +kernel

/-- A two-perfect group fixing a nonzero vector of a binary plane acts
trivially on that plane. -/
theorem twoPerfect_plane_fixed {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) K W) (hK : IsPPerfect 2 K)
    (hd : Module.finrank (ZMod 2) W = 2)
    (w : W) (hw : w ≠ 0) (hfix : ∀ g, σ g w = w) : ∀ g, σ g = 1 := by
  let := Module.finite_of_finrank_pos (R := ZMod 2) (M := W) (by omega)
  let b := Module.finBasisOfFinrankEq (ZMod 2) W hd
  let m := LinearMap.toMatrixAlgEquiv b
  have hsquare (g : K) : σ g * σ g = 1 := by
    apply m.injective
    have hinv : m (σ g) * m (σ g⁻¹) = 1 := by
      rw [← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one]
    have hcoord : (m (σ g)).mulVec (b.equivFun w) = b.equivFun w := by
      exact (LinearMap.toMatrix_mulVec_repr b b (σ g) w).trans
        (congrArg b.equivFun (hfix g))
    have hne : b.equivFun w ≠ 0 := fun h => hw (b.equivFun.injective (by simpa using h))
    simpa only [map_mul, map_one] using
      matrix_nonzero_fixed_square _ _ hinv (b.equivFun w) hne hcoord
  have hp : IsPGroup 2 σ.asGroupHom.range := by
    intro x
    refine ⟨1, ?_⟩
    apply Subtype.ext
    apply Units.ext
    obtain ⟨g, hg⟩ := x.property
    change ((x : (Module.End (ZMod 2) W)ˣ) ^ (2 ^ 1) : Module.End (ZMod 2) W) = 1
    rw [← hg]
    simpa only [pow_one, pow_two, Units.val_mul, Representation.asGroupHom_apply] using hsquare g
  have he := hK.hom_eq_one_of_isPGroup hp σ.asGroupHom.rangeRestrict
  intro g
  have hx := DFunLike.congr_fun he g
  exact congrArg (fun x : σ.asGroupHom.range => (x.val : Module.End (ZMod 2) W)) hx

private lemma normalizer_moved_stable (ρ : Representation (ZMod 2) K V) (X : Subgroup K)
    {g : K} (hg : g ∈ normalizer (X : Set K)) :
    ∀ v ∈ Coinvariants.ker (ρ.comp X.subtype),
      ρ g v ∈ Coinvariants.ker (ρ.comp X.subtype) := by
  intro v hv
  have hle : Coinvariants.ker (ρ.comp X.subtype) ≤
      (Coinvariants.ker (ρ.comp X.subtype)).comap (ρ g) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨x, w⟩, rfl⟩
    have hx : g * (x : K) * g⁻¹ ∈ X := (mem_normalizer_iff.mp hg x).mp x.property
    change ρ g (ρ x w - w) ∈ Coinvariants.ker (ρ.comp X.subtype)
    convert Coinvariants.sub_mem_ker (ρ := ρ.comp X.subtype)
      ⟨g * (x : K) * g⁻¹, hx⟩ (ρ g w) using 1
    · simp [map_sub, ← Module.End.mul_apply, ← map_mul, mul_assoc]
  exact hle hv

private lemma normalizer_fixed_stable (ρ : Representation (ZMod 2) K V) (X : Subgroup K)
    {g : K} (hg : g ∈ normalizer (X : Set K)) :
    ∀ v ∈ (Representation.invariants (ρ.comp X.subtype)), ρ g v ∈ (Representation.invariants (ρ.comp X.subtype)) := by
  intro v hv x
  have hx : g⁻¹ * (x : K) * g ∈ X := by
    simpa using (mem_normalizer_iff.mp ((normalizer (X : Set K)).inv_mem hg) x).mp x.property
  have he := congrArg (ρ g) (hv ⟨g⁻¹ * (x : K) * g, hx⟩)
  change ρ g (ρ (g⁻¹ * (x : K) * g) v) = ρ g v at he
  change ρ x (ρ g v) = ρ g v
  simpa only [← Module.End.mul_apply, ← map_mul, mul_assoc, mul_inv_cancel_left] using he

/-- A two-perfect normalizer of a rank-two S₃ action either centralizes
S₃ or has all its fixed vectors fixed by S₃. -/
theorem symmetric_three_twoPerfect_dichotomy [Finite K]
    (ρ : Representation (ZMod 2) K V) (hf : Function.Injective ρ)
    (X Y : Subgroup K) (e : X ≃* Equiv.Perm (Fin 3))
    (hd : Module.finrank (ZMod 2) (Coinvariants.ker (ρ.comp X.subtype)) = 2)
    (hY : IsPPerfect 2 Y) (hN : Y ≤ normalizer (X : Set K)) :
    ⁅X, Y⁆ = ⊥ ∨ (Representation.invariants (ρ.comp Y.subtype)) ≤ (Representation.invariants (ρ.comp X.subtype)) := by
  classical
  let D := Coinvariants.ker (ρ.comp X.subtype)
  let C := (Representation.invariants (ρ.comp X.subtype))
  let τ : Representation (ZMod 2) Y D :=
    Representation.subrepresentation (ρ.comp Y.subtype) D
      (fun y => normalizer_moved_stable ρ X (hN y.property))
  have hfX := hf.comp X.subtype_injective
  have hm := movedRepresentation_faithful (ρ.comp X.subtype) hfX e
  have hsplit := symmetric_three_split (ρ.comp X.subtype) hfX e hd
  by_cases htriv : ∀ y, τ y = 1
  · left
    have hfix (y : Y) (w : D) : ρ y (w : V) = w :=
      congrArg Subtype.val (LinearMap.congr_fun (htriv y) w)
    apply le_bot_iff.mp
    apply commutator_le.mpr
    intro x hx y hy
    have hk : ⁅x, y⁆ ∈ X :=
      (le_normalizer_iff_commutator_le_left.mp hN) (commutator_mem_commutator hx hy)
    change ⁅x, y⁆ = 1
    have he : movedRepresentation (ρ.comp X.subtype) ⟨⁅x, y⁆, hk⟩ = 1 := by
      ext w
      change ρ ⁅x, y⁆ (w : V) = w
      have hiy := hfix ⟨y⁻¹, Y.inv_mem hy⟩ w
      have hxw := moved_stable (ρ.comp X.subtype) (⟨x⁻¹, X.inv_mem hx⟩ : X) w w.property
      have hyx := hfix ⟨y, hy⟩ ⟨ρ x⁻¹ w, hxw⟩
      simp only [commutatorElement_def, map_mul, Module.End.mul_apply, hiy, hyx]
      simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel,
        map_one, Module.End.one_apply]
    have hh := hm (he.trans (map_one _).symm)
    exact congrArg Subtype.val hh
  · right
    intro v hv
    obtain ⟨d, hdD, c, hcC, hdc⟩ := Submodule.mem_sup.mp
      (show v ∈ D ⊔ C from hsplit.sup_eq_top ▸ Submodule.mem_top)
    have hdY : ∀ y : Y, ρ y d = d := by
      intro y
      have hsum : (ρ y d - d) + (ρ y c - c) = 0 := by
        have h := hv y
        change ρ y v = v at h
        rw [← hdc, map_add] at h
        rw [← sub_eq_zero] at h
        calc
          _ = (ρ y d + ρ y c) - (d + c) := by abel
          _ = 0 := h
      have hdiffD : ρ y d - d ∈ D :=
        D.sub_mem (normalizer_moved_stable ρ X (hN y.property) d hdD) hdD
      have hdiffC : ρ y d - d ∈ C := by
        have he : ρ y d - d = -(ρ y c - c) := eq_neg_iff_add_eq_zero.mpr hsum
        rw [he]
        exact C.neg_mem (C.sub_mem (normalizer_fixed_stable ρ X (hN y.property) c hcC) hcC)
      exact sub_eq_zero.mp (Submodule.disjoint_def.mp hsplit.disjoint _ hdiffD hdiffC)
    have hd0 : d = 0 := by
      by_contra hn
      have hwn : (⟨d, hdD⟩ : D) ≠ 0 := fun h => hn (congrArg Subtype.val h)
      apply htriv
      exact twoPerfect_plane_fixed τ hY hd ⟨d, hdD⟩ hwn
        (fun y => Subtype.ext (hdY y))
    rw [hd0, zero_add] at hdc
    exact hdc ▸ hcC

end Representation.BinaryPlaneNormalizer
