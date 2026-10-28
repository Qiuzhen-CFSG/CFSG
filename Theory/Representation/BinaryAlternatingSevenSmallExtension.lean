module
public import Theory.Representation.BinaryAlternatingSevenCohomology
public import Theory.Representation.FirstCohomology
public import Theory.Representation.BinaryAlternatingSevenSmallOrbit
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# A four-space fills the small binary A₇ extension

Let an order-360 subgroup of A₇ act irreducibly on a four-dimensional
submodule of a binary space of dimension at most five, with no fixed vector
in the ambient space. If the ambient dimension were five, the submodule's
annihilator would be a binary line fixed by that subgroup. The established
small-orbit theorem makes this line fixed by A₇, so the submodule is globally
invariant and its quotient is trivial. The proved vanishing of first
cohomology for irreducible four-dimensional A₇ modules then makes the
submodule equal to the ambient space.

The actual consumer is the elementary upper core in the original normal A₆
configuration of Aschbacher–Smith 13.3.2 and 13.5.15, printed pp.884–885,920.
This is a specialized consequence of the existing I.1.6(8) cohomology theorem;
it does not classify arbitrary five-dimensional representations.
-/

public section
open Module
namespace Representation.BinaryAlternatingSevenSmallExtension
private abbrev A7 := alternatingGroup (Fin 7)
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]

private theorem hyperplane_trivial_quotient
    (ρ : Representation (ZMod 2) A7 W) (B : Subgroup A7)
    (U : Subrepresentation (ρ.comp B.subtype))
    (hdU : finrank (ZMod 2) U.toSubmodule = 4)
    (hdW : finrank (ZMod 2) W = 5)
    (hsmall : ∀ f : Module.Dual (ZMod 2) W,
      (∀ b : B, ρ.dual b.val f = f) → ∀ g, ρ.dual g f = f) :
    ∀ g w, ρ g w - w ∈ U := by
  let A := U.toSubmodule.dualAnnihilator
  have hdA : finrank (ZMod 2) A = 1 := by
    have hd := Subspace.finrank_add_finrank_dualAnnihilator_eq U.toSubmodule
    rw [hdU, hdW] at hd
    change finrank (ZMod 2) U.toSubmodule.dualAnnihilator = 1
    omega
  have hcA : Nat.card A = 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hdA]
    norm_num
  obtain ⟨f, hf0, huniq⟩ := (Nat.card_eq_two_iff' (0 : A)).mp hcA
  have hfixB (b : B) : ρ.dual b.val f.val = f.val := by
    have hm : ρ.dual b.val f.val ∈ A := by
      change _ ∈ U.toSubmodule.dualAnnihilator
      rw [Submodule.mem_dualAnnihilator]
      intro w hw
      exact (Submodule.mem_dualAnnihilator f.val).mp f.property _
        (U.apply_mem_toSubmodule b⁻¹ hw)
    have hne : (⟨ρ.dual b.val f.val, hm⟩ : A) ≠ 0 := by
      intro he
      apply hf0
      apply Subtype.ext
      change f.val = 0
      have he' : ρ.dual b.val f.val = 0 := congrArg Subtype.val he
      have hh := congrArg (fun t => ρ.dual b.val⁻¹ t) he'
      simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply, map_zero] using hh
    exact congrArg Subtype.val (huniq _ hne)
  have hfix := hsmall f.val hfixB
  have hmem {w : W} (hw : f.val w = 0) : w ∈ U := by
    change w ∈ U.toSubmodule
    rw [← Subspace.dualAnnihilator_dualCoannihilator_eq (W := U.toSubmodule)]
    rw [Submodule.mem_dualCoannihilator]
    intro l hl
    by_cases hz : (⟨l, hl⟩ : A) = 0
    · have hl0 : l = 0 := congrArg Subtype.val hz
      simp [hl0]
    · have hlf : l = f.val := congrArg Subtype.val (huniq _ hz)
      simpa [hlf] using hw
  intro g w
  apply hmem
  rw [map_sub, sub_eq_zero]
  have hh := congrArg (fun l : Module.Dual (ZMod 2) W => l w) (hfix g⁻¹)
  simpa only [dual, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.coe_mk,
    AddHom.coe_mk, LinearMap.coe_comp, Function.comp_apply, inv_inv] using hh

private theorem dimension_four_of_trivial_quotient
    (ρ : Representation (ZMod 2) A7 W) (B : Subgroup A7)
    (U : Subrepresentation (ρ.comp B.subtype)) [U.toRepresentation.IsIrreducible]
    (hdU : finrank (ZMod 2) U.toSubmodule = 4)
    (hfixed : OneCohomology.fixed (ρ.comp B.subtype) = ⊥)
    (htriv : ∀ g w, ρ g w - w ∈ U) : finrank (ZMod 2) W = 4 := by
  let V : Subrepresentation ρ := {
    toSubmodule := U.toSubmodule
    apply_mem_toSubmodule g w hw := by
      have hh := U.toSubmodule.add_mem (htriv g w) hw
      simpa using hh }
  let : V.toRepresentation.IsIrreducible := by
    refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
    · intro he
      have hh := congrArg (fun X : Subrepresentation V.toRepresentation =>
        finrank (ZMod 2) X.toSubmodule) he
      change finrank (ZMod 2) (⊥ : Submodule (ZMod 2) V.toSubmodule) =
        finrank (ZMod 2) (⊤ : Submodule (ZMod 2) V.toSubmodule) at hh
      have hz : finrank (ZMod 2) V.toSubmodule = 0 := by
        simpa only [finrank_bot, finrank_top] using hh.symm
      change finrank (ZMod 2) U.toSubmodule = 0 at hz
      omega
    · intro X
      let Y : Subrepresentation U.toRepresentation := {
        toSubmodule := X.toSubmodule
        apply_mem_toSubmodule b x hx := X.apply_mem_toSubmodule b.val hx }
      rcases eq_bot_or_eq_top Y with he | he
      · have he' := congrArg Subrepresentation.toSubmodule he
        change X.toSubmodule = ⊥ at he'
        exact Or.inl (Subrepresentation.toSubmodule_injective he')
      · have he' := congrArg Subrepresentation.toSubmodule he
        change X.toSubmodule = ⊤ at he'
        exact Or.inr (Subrepresentation.toSubmodule_injective he')
  have hH := binaryAlternatingSeven_finrank_H1_eq_zero_of_irreducible_four
    V.toRepresentation hdU
  let : Subsingleton (OneCohomology.H1 V.toRepresentation) :=
    (Module.finrank_zero_iff (R := ZMod 2)).mp hH
  have hfixedA : OneCohomology.fixed ρ = ⊥ := by
    apply bot_unique
    intro w hw
    have hb : w ∈ OneCohomology.fixed (ρ.comp B.subtype) := fun b => hw b.val
    rwa [hfixed] at hb
  have heq : V.toSubmodule = ⊤ :=
    OneCohomology.dualCover_eq_top_of_H1_subsingleton V htriv hfixedA
  change U.toSubmodule = ⊤ at heq
  rw [heq, finrank_top] at hdU
  exact hdU

private theorem finrank_eq_four_of_small_orbit
    (ρ : Representation (ZMod 2) A7 W) (B : Subgroup A7)
    (U : Subrepresentation (ρ.comp B.subtype)) [U.toRepresentation.IsIrreducible]
    (hdU : finrank (ZMod 2) U.toSubmodule = 4)
    (hdW : finrank (ZMod 2) W ≤ 5)
    (hfixed : OneCohomology.fixed (ρ.comp B.subtype) = ⊥)
    (hsmall : ∀ f : Module.Dual (ZMod 2) W,
      (∀ b : B, ρ.dual b.val f = f) → ∀ g, ρ.dual g f = f) :
    finrank (ZMod 2) W = 4 := by
  have hle : 4 ≤ finrank (ZMod 2) W := by
    rw [← hdU]
    exact Submodule.finrank_le _
  by_cases heq : finrank (ZMod 2) W = 4
  · exact heq
  have hd5 : finrank (ZMod 2) W = 5 := by omega
  exact dimension_four_of_trivial_quotient ρ B U hdU hfixed
    (hyperplane_trivial_quotient ρ B U hdU hd5 hsmall)

/-- An irreducible four-space for an order-360 subgroup exhausts a binary
A₇-module of dimension at most five when that subgroup has no fixed vector. -/
theorem finrank_eq_four
    (ρ : Representation (ZMod 2) (alternatingGroup (Fin 7)) W)
    (B : Subgroup (alternatingGroup (Fin 7))) (hB : Nat.card B = 360)
    (U : Subrepresentation (ρ.comp B.subtype)) [U.toRepresentation.IsIrreducible]
    (hdU : finrank (ZMod 2) U.toSubmodule = 4)
    (hdW : finrank (ZMod 2) W ≤ 5)
    (hfixed : OneCohomology.fixed (ρ.comp B.subtype) = ⊥) :
    finrank (ZMod 2) W = 4 := by
  apply finrank_eq_four_of_small_orbit ρ B U hdU hdW hfixed
  intro f hf
  exact BinaryAlternatingSevenSmallOrbit.fixed_of_card_subgroup ρ.dual
    (by simpa only [Subspace.dual_finrank_eq] using hdW) B hB f hf

end Representation.BinaryAlternatingSevenSmallExtension
