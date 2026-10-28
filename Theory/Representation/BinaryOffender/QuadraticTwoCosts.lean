module

public import Theory.Representation.BinaryOffender.QuadraticFourSpace
public import Theory.Representation.BinaryOffender.DualDisplacement

/-!
# Four-groups from two displacement costs

A faithful quadratic actor of rank four whose natural and dual fixed
codimensions are both two fills Hom(W/C_W(A), [W,A]). A fixed nonzero
functional on the quotient gives an actual subgroup of order four with a
common fixed hyperplane. The ambient space need not have dimension four.
This is the rank-four construction in Aschbacher–Smith B.4.9(2), printed
pp.94–95, combined manuscript of 1 March 2004.
-/

public section
open Representation Representation.BinaryOffender
namespace Representation.BinaryOffender.QuadraticTwoCosts
variable {H W : Type*} [Group H] [Finite H] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

/-- Surjective displacement coordinates produce a literal common-axis four-group. -/
theorem axis_of_two_costs (σ : Representation (ZMod 2) H W) (hσ : Function.Injective σ)
    (A : Subgroup H) (hA : IsElementaryTwo A) (hr : rank A = 4)
    (hq : IsQuadratic σ A) (hcost : fixedCodim σ A = 2)
    (hd : fixedCodim σ.dual A = 2) :
    ∃ E : Subgroup H, E ≤ A ∧ IsElementaryAbelian 2 E ∧ Nat.card E = 4 ∧
      ∃ I : Submodule (ZMod 2) W, Module.finrank (ZMod 2) (W ⧸ I) = 1 ∧
        ∀ a ∈ E, a ≠ 1 → fixedSpace σ (Subgroup.zpowers a) = I := by
  let U := fixedSpace σ A
  let C := Coinvariants.ker (σ.comp A.subtype)
  let D (a : A) : (W ⧸ U) →ₗ[ZMod 2] C :=
    U.liftQ ((σ a - LinearMap.id).codRestrict C
      (fun w => Coinvariants.sub_mem_ker (ρ := σ.comp A.subtype) a w))
      (by intro w hw; exact Subtype.ext (sub_eq_zero.mpr (hw a)))
  have hD (a : A) (w : W) : (D a (U.mkQ w) : W) = σ a w - w := rfl
  let f : A →* Multiplicative ((W ⧸ U) →ₗ[ZMod 2] C) :=
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
    have hh := congrArg (fun z : Multiplicative ((W ⧸ U) →ₗ[ZMod 2] C) =>
      ((Multiplicative.toAdd z) (U.mkQ w) : W)) he
    exact sub_left_injective hh
  let : Finite ((W ⧸ U) →ₗ[ZMod 2] C) := Module.finite_of_finite (ZMod 2)
  have hc : Nat.card ((W ⧸ U) →ₗ[ZMod 2] C) =
      2 ^ (Module.finrank (ZMod 2) (W ⧸ U) * Module.finrank (ZMod 2) C) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, Module.finrank_linearMap]
  have hcA : Nat.card A = 16 := by rw [hA.card_eq_two_pow_rank, hr]; rfl
  have hdC : Module.finrank (ZMod 2) C = 2 :=
    (finrank_dual_quotient_invariants (σ.comp A.subtype)).symm.trans hd
  have hdQ : Module.finrank (ZMod 2) (W ⧸ U) = 2 := hcost
  have hbij : Function.Bijective f := (Nat.bijective_iff_injective_and_card f).mpr
    ⟨hf, by change Nat.card A = Nat.card ((W ⧸ U) →ₗ[ZMod 2] C); rw [hcA, hc, hdC, hdQ]; rfl⟩
  let e := MulEquiv.ofBijective f hbij
  obtain ⟨x, hx⟩ : ∃ x : W ⧸ U, x ≠ 0 := by
    have : Nontrivial (W ⧸ U) := Module.nontrivial_of_finrank_pos (R := ZMod 2)
      (M := W ⧸ U) (by rw [hdQ]; decide)
    exact exists_ne 0
  obtain ⟨φ, hφx, _⟩ := (⊥ : Submodule (ZMod 2) (W ⧸ U)).exists_le_ker_of_notMem hx
  have hφx1 : φ x = 1 := (by decide : ∀ z : ZMod 2, z ≠ 0 → z = 1) _ hφx
  let j : Multiplicative C →* Multiplicative ((W ⧸ U) →ₗ[ZMod 2] C) :=
    { toFun := fun c => Multiplicative.ofAdd (φ.smulRight (Multiplicative.toAdd c))
      map_one' := by apply Multiplicative.ext; ext q; simp
      map_mul' := by intro a b; apply Multiplicative.ext; ext q; simp [smul_add] }
  have hj : Function.Injective j := by
    intro a b he
    have hh := congrArg (fun z : Multiplicative ((W ⧸ U) →ₗ[ZMod 2] C) =>
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
  let ψ : W →ₗ[ZMod 2] ZMod 2 := φ.comp U.mkQ
  have hψ : ψ ≠ 0 := by
    intro hz
    obtain ⟨w, hw⟩ := U.mkQ_surjective x
    have hh := LinearMap.congr_fun hz w
    change φ (U.mkQ w) = 0 at hh
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
    have hh := congrArg (fun z : Multiplicative ((W ⧸ U) →ₗ[ZMod 2] C) =>
      ((Multiplicative.toAdd z) (U.mkQ w) : W)) he
    exact hh
  ext w
  rw [mem_fixedSpace_zpowers_iff, LinearMap.mem_ker]
  change σ (k c) w = w ↔ ψ w = 0
  rw [← sub_eq_zero, hact]
  have hcval : (Multiplicative.toAdd c : C).val ≠ 0 := fun hz => hc0 (Subtype.ext hz)
  simp only [smul_eq_zero, hcval, or_false]

end Representation.BinaryOffender.QuadraticTwoCosts
