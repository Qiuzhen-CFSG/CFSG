module

public import Theory.Representation.BinaryOffender.QuadraticFourSpace
public import Mathlib.Algebra.Module.ZMod

/-!
# Common-axis four-groups in quadratic five-dimensional actions

Faithful quadratic displacement embeds the actor into Hom(W/C,C), where C
is its common fixed space. Rank at least five forces the dimensions to be
2 by 3 or 3 by 2, and the displacement image has codimension at most one.
In the first case every fixed-functional column meets the image in a plane.
In the second case the quotient pairing has a nonzero functional in its
left kernel, so a whole two-dimensional column belongs to the image.
Pulling back a plane gives a literal four-group whose nonidentity elements
all have the same fixed hyperplane.

Source: Aschbacher–Smith, B.4.9(2)(i), printed p.95, combined manuscript
of 1 March 2004. This intrinsic argument covers both actor ranks five and six.
-/

public section
open Module Representation Representation.BinaryOffender
namespace Representation.BinaryOffender.QuadraticFiveAxis
variable {Q C : Type*} [AddCommGroup Q] [Module (ZMod 2) Q]
  [AddCommGroup C] [Module (ZMod 2) C]
  [FiniteDimensional (ZMod 2) Q] [FiniteDimensional (ZMod 2) C]

private theorem column_kernel (S : Submodule (ZMod 2) (Q →ₗ[ZMod 2] C))
    (hS : 5 ≤ finrank (ZMod 2) S)
    (hd : (finrank (ZMod 2) Q = 2 ∧ finrank (ZMod 2) C = 3) ∨
      (finrank (ZMod 2) Q = 3 ∧ finrank (ZMod 2) C = 2)) :
    ∃ φ : Module.Dual (ZMod 2) Q, φ ≠ 0 ∧
      2 ≤ finrank (ZMod 2) (LinearMap.ker
        (S.mkQ.comp (LinearMap.smulRightₗ φ))) := by
  have hdHom : finrank (ZMod 2) (Q →ₗ[ZMod 2] C) = 6 := by
    rw [Module.finrank_linearMap]
    rcases hd with ⟨hq, hc⟩ | ⟨hq, hc⟩ <;> rw [hq, hc]
  have hcodim : finrank (ZMod 2) ((Q →ₗ[ZMod 2] C) ⧸ S) ≤ 1 := by
    have := S.finrank_quotient_add_finrank
    omega
  rcases hd with ⟨hq, hc⟩ | ⟨hq, hc⟩
  · have : Nontrivial (Module.Dual (ZMod 2) Q) :=
      Module.nontrivial_of_finrank_pos (R := ZMod 2)
        (by rw [Subspace.dual_finrank_eq, hq]; decide)
    obtain ⟨φ, hφ⟩ := exists_ne (0 : Module.Dual (ZMod 2) Q)
    refine ⟨φ, hφ, ?_⟩
    have h := LinearMap.finrank_range_add_finrank_ker (S.mkQ.comp (LinearMap.smulRightₗ φ))
    have hb := (LinearMap.range (S.mkQ.comp (LinearMap.smulRightₗ φ))).finrank_le
    omega
  · let T : Module.Dual (ZMod 2) Q →ₗ[ZMod 2]
        (C →ₗ[ZMod 2] ((Q →ₗ[ZMod 2] C) ⧸ S)) :=
      { toFun := fun φ => S.mkQ.comp (LinearMap.smulRightₗ φ)
        map_add' := by intro φ ψ; ext c; simp
        map_smul' := by intro r φ; ext c; simp }
    have hT : 0 < finrank (ZMod 2) T.ker := by
      have h := T.finrank_range_add_finrank_ker
      have hb := T.range.finrank_le
      rw [Subspace.dual_finrank_eq, hq] at h
      rw [Module.finrank_linearMap, hc] at hb
      omega
    have : Nontrivial T.ker := Module.nontrivial_of_finrank_pos (R := ZMod 2) hT
    obtain ⟨φ, hφ⟩ := exists_ne (0 : T.ker)
    refine ⟨φ, fun h => hφ (Subtype.ext h), ?_⟩
    have hz : S.mkQ.comp (LinearMap.smulRightₗ φ.val) = 0 := φ.property
    rw [hz, LinearMap.ker_zero, finrank_top, hc]


variable {H W : Type*} [Group H] [Finite H] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

/-- A faithful quadratic elementary actor of rank at least five in dimension
five contains a four-group with a literal common fixed hyperplane. -/
theorem high_rank_axis (σ : Representation (ZMod 2) H W) (hσ : Function.Injective σ)
    (hdim : Module.finrank (ZMod 2) W = 5) (A : Subgroup H)
    (hA : IsElementaryTwo A) (hr : 5 ≤ rank A) (hq : IsQuadratic σ A) :
    ∃ E : Subgroup H, E ≤ A ∧ IsElementaryAbelian 2 E ∧ Nat.card E = 4 ∧
      ∃ I : Submodule (ZMod 2) W, Module.finrank (ZMod 2) (W ⧸ I) = 1 ∧
        ∀ a ∈ E, a ≠ 1 → fixedSpace σ (Subgroup.zpowers a) = I := by
  let C := fixedSpace σ A
  let D (a : A) : (W ⧸ C) →ₗ[ZMod 2] C :=
    C.liftQ ((σ a - LinearMap.id).codRestrict C (fun w b => hq b b.property a a.property w))
      (by intro w hw; exact Subtype.ext (sub_eq_zero.mpr (hw a)))
  let f : A →* Multiplicative ((W ⧸ C) →ₗ[ZMod 2] C) :=
    { toFun := fun a => Multiplicative.ofAdd (D a)
      map_one' := by
        apply Multiplicative.ext
        apply LinearMap.ext
        intro q
        induction q using Submodule.Quotient.induction_on with
        | _ w =>
          apply Subtype.ext
          change σ 1 w - w = 0
          simp
      map_mul' := by
        intro a b
        apply Multiplicative.ext
        apply LinearMap.ext
        intro q
        induction q using Submodule.Quotient.induction_on with
        | _ w =>
          apply Subtype.ext
          change σ (a.val * b.val) w - w = (σ a w - w) + (σ b w - w)
          have he := hq a a.property b b.property w
          rw [map_sub] at he
          rw [map_mul, Module.End.mul_apply]
          rw [sub_eq_iff_eq_add.mp he]
          abel }
  have hf : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    apply hσ
    apply LinearMap.ext
    intro w
    have hh := congrArg (fun z : Multiplicative ((W ⧸ C) →ₗ[ZMod 2] C) =>
      ((Multiplicative.toAdd z) (C.mkQ w) : W)) he
    exact sub_left_injective hh
  let S : Submodule (ZMod 2) ((W ⧸ C) →ₗ[ZMod 2] C) :=
    AddSubgroup.toZModSubmodule 2 f.range.toAddSubgroup'
  let fS : A →* Multiplicative S :=
    { toFun := fun a => Multiplicative.ofAdd ⟨D a, by exact ⟨a, rfl⟩⟩
      map_one' := by
        apply Multiplicative.ext
        apply Subtype.ext
        exact congrArg Multiplicative.toAdd f.map_one
      map_mul' := by
        intro a b
        apply Multiplicative.ext
        apply Subtype.ext
        exact congrArg Multiplicative.toAdd (f.map_mul a b) }
  have hfS : Function.Bijective fS := by
    constructor
    · intro a b h
      apply hf
      exact congrArg (fun s : Multiplicative S => Multiplicative.ofAdd s.toAdd.val) h
    · intro s
      obtain ⟨a, ha⟩ := s.toAdd.property
      refine ⟨a, ?_⟩
      apply Multiplicative.ext
      apply Subtype.ext
      exact congrArg Multiplicative.toAdd ha
  let e := MulEquiv.ofBijective fS hfS
  have hScard : Nat.card S = Nat.card A := (Nat.card_congr e.toEquiv).symm
  have hSrank : Module.finrank (ZMod 2) S = rank A := by
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    change 2 ^ Module.finrank (ZMod 2) S = 2 ^ rank A
    rw [← hA.card_eq_two_pow_rank, ← hScard]
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hS : 5 ≤ Module.finrank (ZMod 2) S := by omega
  have hprod : 5 ≤ Module.finrank (ZMod 2) (W ⧸ C) * Module.finrank (ZMod 2) C := by
    have := S.finrank_le
    rw [Module.finrank_linearMap] at this
    omega
  have hd : (Module.finrank (ZMod 2) (W ⧸ C) = 2 ∧ Module.finrank (ZMod 2) C = 3) ∨
      (Module.finrank (ZMod 2) (W ⧸ C) = 3 ∧ Module.finrank (ZMod 2) C = 2) := by
    have hs := C.finrank_quotient_add_finrank
    have hl := C.finrank_le
    rw [hdim] at hs hl
    interval_cases hc : Module.finrank (ZMod 2) C <;> omega
  obtain ⟨φ, hφ, hK⟩ := column_kernel S hS hd
  let K := LinearMap.ker (S.mkQ.comp (LinearMap.smulRightₗ φ))
  have hmem (c : K) : φ.smulRight c.val ∈ S := by
    have h := c.property
    change S.mkQ (φ.smulRight c.val) = 0 at h
    exact (Submodule.Quotient.mk_eq_zero S).mp h
  let j : Multiplicative K →* Multiplicative S :=
    { toFun := fun c => Multiplicative.ofAdd ⟨φ.smulRight c.toAdd.val, hmem c.toAdd⟩
      map_one' := by apply Multiplicative.ext; apply Subtype.ext; ext q; simp
      map_mul' := by
        intro a b
        apply Multiplicative.ext
        apply Subtype.ext
        ext q
        simp [smul_add] }
  obtain ⟨x, hx⟩ : ∃ x, φ x ≠ 0 := by
    by_contra h
    apply hφ
    apply LinearMap.ext
    intro x
    exact not_ne_iff.mp (not_exists.mp h x)
  have hx1 : φ x = 1 := (by decide : ∀ z : ZMod 2, z ≠ 0 → z = 1) _ hx
  have hj : Function.Injective j := by
    intro a b he
    have hh := congrArg (fun s : Multiplicative S => s.toAdd.val x) he
    change φ x • a.toAdd.val = φ x • b.toAdd.val at hh
    apply Multiplicative.ext
    apply Subtype.ext
    simpa only [hx1, one_smul] using hh
  let k : Multiplicative K →* H := A.subtype.comp (e.symm.toMonoidHom.comp j)
  have hk : Function.Injective k := Subtype.coe_injective.comp (e.symm.injective.comp hj)
  have hcardK : 2 ^ 2 ≤ Nat.card (Multiplicative K) := by
    change 2 ^ 2 ≤ Nat.card K
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    exact Nat.pow_le_pow_right (by decide) hK
  obtain ⟨B, hB⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card Nat.prime_two
    (ZModModule.isPGroup_multiplicative (n := 2) (G := K)) hcardK
  let E := B.map k
  have hEA : E ≤ A := by rintro a ⟨c, hc, rfl⟩; exact (e.symm (j c)).property
  have hEC : Nat.card E = 4 := by
    rw [Subgroup.card_map_of_injective hk]
    exact hB
  have hE0 : E ≠ ⊥ := by intro he; rw [he, Subgroup.card_bot] at hEC; omega
  let ψ : W →ₗ[ZMod 2] ZMod 2 := φ.comp C.mkQ
  have hψ : ψ ≠ 0 := by
    intro hz
    obtain ⟨w, hw⟩ := C.mkQ_surjective x
    have hh := LinearMap.congr_fun hz w
    change φ (C.mkQ w) = 0 at hh
    rw [hw] at hh
    exact hx hh
  have hker : Module.finrank (ZMod 2) (W ⧸ ψ.ker) = 1 := by
    have h1 := Module.Dual.finrank_ker_add_one_of_ne_zero hψ
    have h2 := ψ.ker.finrank_quotient_add_finrank
    omega
  refine ⟨E, hEA, (hA.of_le hEA hE0).2, hEC, ψ.ker, hker, ?_⟩
  intro a ha ha1
  obtain ⟨c, hc, rfl⟩ := ha
  have hc0 : (c.toAdd.val : C).val ≠ 0 := by
    intro hz
    have hc1 : c = 1 := Multiplicative.ext (Subtype.ext (Subtype.ext hz))
    exact ha1 (by rw [hc1, map_one])
  have hact (w : W) : σ (k c) w - w = ψ w • (c.toAdd.val : C).val := by
    have he := e.apply_symm_apply (j c)
    have hh := congrArg (fun s : Multiplicative S => (s.toAdd.val (C.mkQ w) : W)) he
    exact hh
  ext w
  rw [mem_fixedSpace_zpowers_iff, LinearMap.mem_ker]
  change σ (k c) w = w ↔ ψ w = 0
  rw [← sub_eq_zero, hact]
  simp only [smul_eq_zero, hc0, or_false]

end Representation.BinaryOffender.QuadraticFiveAxis
