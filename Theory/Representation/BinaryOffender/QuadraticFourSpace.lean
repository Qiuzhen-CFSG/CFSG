module
public import Theory.Representation.BinaryOffender.FaithfulRankOne
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.GroupTheory.Sylow
public import Theory.Representation.BinaryOffender.UniformFixedSpace

/-!
# Common-axis four-groups in quadratic four-dimensional actions

For a faithful quadratic elementary actor of rank four, displacement embeds
it into Hom(W/C,C), where C is its fixed space. In dimension four the order
bound forces dim(C) = dim(W/C) = 2 and makes this embedding surjective.
Fixing a nonzero functional on W/C then produces a subgroup of order four;
all three of its nonidentity elements fix precisely the same hyperplane.
A separate extraction handles any elementary actor already fixing a hyperplane.

These intrinsic lemmas construct the literal quotient witnesses used in
Aschbacher–Smith B.4.9(2), combined manuscript of 1 March 2004, printed p.94.
-/

public section
open Representation Representation.BinaryOffender
namespace Representation.BinaryOffender.QuadraticFourSpace

variable {H W : Type*} [Group H] [Finite H] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

/-- A faithful quadratic elementary actor of rank four in dimension four contains
an actual four-group with one common hyperplane as its fixed space. -/
theorem rank_four_axis (σ : Representation (ZMod 2) H W) (hσ : Function.Injective σ)
    (hdim : Module.finrank (ZMod 2) W = 4) (A : Subgroup H)
    (hA : IsElementaryTwo A) (hr : rank A = 4) (hq : IsQuadratic σ A) :
    ∃ E : Subgroup H, E ≤ A ∧ IsElementaryAbelian 2 E ∧ Nat.card E = 4 ∧
      ∃ I : Submodule (ZMod 2) W, Module.finrank (ZMod 2) (W ⧸ I) = 1 ∧
        ∀ a ∈ E, a ≠ 1 → fixedSpace σ (Subgroup.zpowers a) = I := by
  let C := fixedSpace σ A
  let D (a : A) : (W ⧸ C) →ₗ[ZMod 2] C :=
    C.liftQ ((σ a - LinearMap.id).codRestrict C (fun w b => hq b b.property a a.property w))
      (by intro w hw; exact Subtype.ext (sub_eq_zero.mpr (hw a)))
  have hD (a : A) (w : W) : (D a (C.mkQ w) : W) = σ a w - w := rfl
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
  let : Finite ((W ⧸ C) →ₗ[ZMod 2] C) := Module.finite_of_finite (ZMod 2)
  have hc : Nat.card ((W ⧸ C) →ₗ[ZMod 2] C) =
      2 ^ (Module.finrank (ZMod 2) (W ⧸ C) * Module.finrank (ZMod 2) C) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, Module.finrank_linearMap]
  have hcA : Nat.card A = 16 := by rw [hA.card_eq_two_pow_rank, hr]; rfl
  have hb := Nat.card_le_card_of_injective f hf
  change Nat.card A ≤ Nat.card ((W ⧸ C) →ₗ[ZMod 2] C) at hb
  rw [hcA, hc] at hb
  have hb' : 4 ≤ Module.finrank (ZMod 2) (W ⧸ C) * Module.finrank (ZMod 2) C :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hb
  have hdC : Module.finrank (ZMod 2) C = 2 := by
    have hs := C.finrank_quotient_add_finrank
    have hl := C.finrank_le
    rw [hdim] at hs hl
    interval_cases h : Module.finrank (ZMod 2) C <;> omega
  have hdQ : Module.finrank (ZMod 2) (W ⧸ C) = 2 := by
    have hs := C.finrank_quotient_add_finrank
    omega
  have hbij : Function.Bijective f := (Nat.bijective_iff_injective_and_card f).mpr
    ⟨hf, by change Nat.card A = Nat.card ((W ⧸ C) →ₗ[ZMod 2] C); rw [hcA, hc, hdC, hdQ]; rfl⟩
  let e := MulEquiv.ofBijective f hbij
  obtain ⟨x, hx⟩ : ∃ x : W ⧸ C, x ≠ 0 := by
    have : Nontrivial (W ⧸ C) := Module.nontrivial_of_finrank_pos (R := ZMod 2)
      (M := W ⧸ C) (by rw [hdQ]; decide)
    exact exists_ne 0
  obtain ⟨φ, hφx, _⟩ := (⊥ : Submodule (ZMod 2) (W ⧸ C)).exists_le_ker_of_notMem hx
  have hφx1 : φ x = 1 := (by decide : ∀ z : ZMod 2, z ≠ 0 → z = 1) _ hφx
  let j : Multiplicative C →* Multiplicative ((W ⧸ C) →ₗ[ZMod 2] C) :=
    { toFun := fun c => Multiplicative.ofAdd (φ.smulRight (Multiplicative.toAdd c))
      map_one' := by apply Multiplicative.ext; ext q; simp
      map_mul' := by intro a b; apply Multiplicative.ext; ext q; simp [smul_add] }
  have hj : Function.Injective j := by
    intro a b he
    have hh := congrArg (fun z : Multiplicative ((W ⧸ C) →ₗ[ZMod 2] C) =>
      Multiplicative.toAdd z x) he
    change φ x • Multiplicative.toAdd a = φ x • Multiplicative.toAdd b at hh
    apply Multiplicative.ext
    simpa only [hφx1, one_smul] using hh
  let k : Multiplicative C →* H := A.subtype.comp (e.symm.toMonoidHom.comp j)
  have hk : Function.Injective k := Subtype.coe_injective.comp (e.symm.injective.comp hj)
  let E := k.range
  have hEA : E ≤ A := by rintro a ⟨c, rfl⟩; exact (e.symm (j c)).property
  have hEC : Nat.card E = 4 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hk).toEquiv]
    change Nat.card C = 4
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hdC]
    rfl
  have hE0 : E ≠ ⊥ := by intro he; rw [he, Subgroup.card_bot] at hEC; omega
  have haE := hA.of_le hEA hE0
  let ψ : W →ₗ[ZMod 2] ZMod 2 := φ.comp C.mkQ
  have hψ : ψ ≠ 0 := by
    intro hz
    obtain ⟨w, hw⟩ := C.mkQ_surjective x
    have hh := LinearMap.congr_fun hz w
    change φ (C.mkQ w) = 0 at hh
    rw [hw, hφx1] at hh
    exact one_ne_zero hh
  have hker : Module.finrank (ZMod 2) (W ⧸ ψ.ker) = 1 := by
    have h1 := Module.Dual.finrank_ker_add_one_of_ne_zero hψ
    have h2 := ψ.ker.finrank_quotient_add_finrank
    omega
  refine ⟨E, hEA, haE.2, hEC, ψ.ker, hker, ?_⟩
  intro a ha ha1
  obtain ⟨c, rfl⟩ := ha
  have hc0 : (Multiplicative.toAdd c : C) ≠ 0 := by
    intro hz
    have hc1 : c = 1 := hz
    exact ha1 (by rw [hc1, map_one])
  have hact (w : W) : σ (k c) w - w = ψ w • (Multiplicative.toAdd c : C).val := by
    have he := e.apply_symm_apply (j c)
    have hh := congrArg (fun z : Multiplicative ((W ⧸ C) →ₗ[ZMod 2] C) =>
      ((Multiplicative.toAdd z) (C.mkQ w) : W)) he
    exact hh
  ext w
  rw [mem_fixedSpace_zpowers_iff, LinearMap.mem_ker]
  change σ (k c) w = w ↔ ψ w = 0
  rw [← sub_eq_zero, hact]
  have hcval : (Multiplicative.toAdd c : C).val ≠ 0 := fun hz => hc0 (Subtype.ext hz)
  simp only [smul_eq_zero, hcval, or_false]
/-- A faithful elementary actor fixing a hyperplane supplies a common-axis
four-group as soon as its rank is at least two. -/
theorem fixed_hyperplane_axis (σ : Representation (ZMod 2) H W)
    (hσ : Function.Injective σ) (A : Subgroup H) (hA : IsElementaryTwo A)
    (hr : 2 ≤ rank A) (hc : fixedCodim σ A = 1) :
    ∃ E : Subgroup H, E ≤ A ∧ IsElementaryAbelian 2 E ∧ Nat.card E = 4 ∧
      ∃ I : Submodule (ZMod 2) W, Module.finrank (ZMod 2) (W ⧸ I) = 1 ∧
        ∀ a ∈ E, a ≠ 1 → fixedSpace σ (Subgroup.zpowers a) = I := by
  let : IsElementaryAbelian 2 A := hA.2
  have hcard : 2 ^ 2 ≤ Nat.card A := by
    rw [hA.card_eq_two_pow_rank]
    exact Nat.pow_le_pow_right (by decide) hr
  obtain ⟨B, hB⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card Nat.prime_two
    (IsElementaryAbelian.isPGroup 2 A) hcard
  let E := B.map A.subtype
  have hEA : E ≤ A := Subgroup.map_subtype_le B
  have hEC : Nat.card E = 4 := by
    rw [Subgroup.card_map_of_injective Subtype.coe_injective]
    exact hB
  have hE0 : E ≠ ⊥ := by intro he; rw [he, Subgroup.card_bot] at hEC; omega
  refine ⟨E, hEA, (hA.of_le hEA hE0).2, hEC, fixedSpace σ A, hc, ?_⟩
  intro a ha ha1
  have hle : Subgroup.zpowers a ≤ A := Subgroup.zpowers_le.mpr (hEA ha)
  have hne : Subgroup.zpowers a ≠ ⊥ := by
    intro he
    exact ha1 (Subgroup.mem_bot.mp (he ▸ Subgroup.mem_zpowers a))
  have hp := fixedCodim_pos_of_faithful σ hσ hne
  have hl := Submodule.finrank_mono (fixedSpace_antitone σ hle)
  have hsum := fixedCodim_add_finrank σ A
  have hsum' := fixedCodim_add_finrank σ (Subgroup.zpowers a)
  exact (fixedSpace_eq_of_fixedCodim_eq σ hle (by omega)).symm
end Representation.BinaryOffender.QuadraticFourSpace
