module

public import Theory.Representation.CubicFixedSpace
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Cubic stabilizers of binary Sylow fixed spaces

A nonidentity element of order three lies outside every two-subgroup.
Its pointwise fixation of a Sylow fixed space survives an extension with
trivial kernel. It also survives an extension with trivial quotient:
summing a Sylow-fixed vector over the odd number of Sylow cosets supplies
a globally fixed vector with the same quotient image.

These elementary extension and transport lemmas support the concrete module
comparison in Aschbacher–Smith, Lemma 15.4.18, printed p.1163, using the
extensions in B.4.8 and B.5.1. No extension classification is assumed.
-/

@[expose] public section

open Representation Representation.BinaryOffender
namespace Representation.BinarySylowFixedSpace
variable {G V W : Type*} [Group G]
  [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- Odd coset averaging lifts a Sylow-fixed vector to a globally fixed vector
with the same image in a trivial quotient. -/
theorem fixed_lift_mod_trivial_quotient [Finite G]
    (ρ : Representation (ZMod 2) G V) (S : Sylow 2 G)
    (U : Submodule (ZMod 2) V)
    (hU : ∀ g v, ρ g v - v ∈ U) (v : V) (hv : v ∈ fixedSpace ρ S) :
    ∃ w : V, (∀ g, ρ g w = w) ∧ v - w ∈ U := by
  classical
  let _ := Fintype.ofFinite (G ⧸ (S : Subgroup G))
  let f : G ⧸ (S : Subgroup G) → V := Quotient.lift (fun g => ρ g v) (by
    intro a b hab
    have hs : a⁻¹ * b ∈ S := QuotientGroup.leftRel_apply.mp hab
    have hf : ρ (a⁻¹ * b) v = v := hv ⟨_, hs⟩
    calc
      ρ a v = ρ a (ρ (a⁻¹ * b) v) := congrArg (ρ a) hf.symm
      _ = ρ b v := by simp [← Module.End.mul_apply, ← map_mul])
  have hf (g : G) (q : G ⧸ (S : Subgroup G)) : ρ g (f q) = f (g • q) := by
    induction q using Quotient.inductionOn with
    | h a => exact (congrArg (fun t : Module.End (ZMod 2) V => t v) (ρ.map_mul g a)).symm
  let w : V := ∑ q, f q
  refine ⟨w, ?_, ?_⟩
  · intro g
    simp only [w, map_sum, hf]
    exact Equiv.sum_comp (MulAction.toPerm g) f
  · have hq (q : G ⧸ (S : Subgroup G)) : U.mkQ (f q) = U.mkQ v := by
      induction q using Quotient.inductionOn with
      | h a => exact (Submodule.Quotient.eq U).mpr (hU a v)
    have hn : (Fintype.card (G ⧸ (S : Subgroup G)) : ZMod 2) = 1 := by
      have ho := S.not_dvd_index
      rw [Subgroup.index, Nat.card_eq_fintype_card] at ho
      have hm : Fintype.card (G ⧸ (S : Subgroup G)) % 2 = 1 := by omega
      exact (ZMod.natCast_eq_natCast_iff' _ 1 2).mpr hm
    have hw : U.mkQ w = U.mkQ v := by
      simp only [w, map_sum, hq, Finset.sum_const, Finset.card_univ]
      rw [← Nat.cast_smul_eq_nsmul (ZMod 2), hn, one_smul]
    exact (Submodule.Quotient.eq U).mp hw.symm

/-- An equivariant injection with trivial cokernel preserves the fixed-space
calculation. No splitting of the extension is required. -/
theorem fixes_of_trivial_quotient [Finite G]
    (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) G W)
    (i : σ.IntertwiningMap ρ) (hi : Function.Injective i)
    (hq : ∀ g v, ρ g v - v ∈ i.toLinearMap.range)
    (S : Sylow 2 G) {d : G}
    (hd : ∀ w ∈ fixedSpace σ S, σ d w = w) :
    ∀ v ∈ fixedSpace ρ S, ρ d v = v := by
  intro v hv
  obtain ⟨w, hw, u, hu⟩ := fixed_lift_mod_trivial_quotient ρ S _ hq v hv
  change i u = v - w at hu
  have huf : u ∈ fixedSpace σ S := by
    intro s
    apply hi
    change i (σ (s : G) u) = i u
    rw [i.isIntertwining, hu, map_sub, hw s]
    exact congrArg (fun x => x - w) (hv s)
  have hdu : ρ d (v - w) = v - w := by
    rw [← hu, ← i.isIntertwining, hd u huf]
  rw [map_sub, hw d] at hdu
  exact sub_left_inj.mp hdu

/-- Transport uses genuine group and linear coordinates. -/
theorem sylow_fixedSpace_enlargement_equivariant
    {D : Type*} [Group D]
    (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) D W)
    (A : Subgroup G) (e : G ≃* D) (E : V ≃ₗ[ZMod 2] W)
    (hE : ∀ g v, E (ρ g v) = σ (e g) (E v))
    (h : ∃ d : D, d ∉ A.map e.toMonoidHom ∧ d ^ 3 = 1 ∧
      ∀ w ∈ fixedSpace σ (A.map e.toMonoidHom), σ d w = w) :
    ∃ d : G, d ∉ A ∧ d ^ 3 = 1 ∧ ∀ v ∈ fixedSpace ρ A, ρ d v = v := by
  obtain ⟨d, hd, hc, hf⟩ := h
  refine ⟨e.symm d, ?_, ?_, ?_⟩
  · intro he
    exact hd ⟨e.symm d, he, e.apply_symm_apply d⟩
  · rw [← map_pow, hc, map_one]
  · intro v hv
    apply E.injective
    rw [hE, e.apply_symm_apply]
    apply hf
    rintro ⟨x, hx⟩
    obtain ⟨a, ha, rfl⟩ := hx
    change σ (e a) (E v) = E v
    rw [← hE]
    exact congrArg E (hv ⟨a, ha⟩)

/-- A common fixed-space witness works on the product of two representations. -/
theorem fixes_prod
    (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) G W)
    (A : Subgroup G) {d : G}
    (hρ : ∀ v ∈ fixedSpace ρ A, ρ d v = v)
    (hσ : ∀ w ∈ fixedSpace σ A, σ d w = w) :
    ∀ x ∈ fixedSpace (ρ.prod σ) A, (ρ.prod σ) d x = x := by
  intro x hx
  exact Prod.ext (hρ x.1 (fun a => congrArg Prod.fst (hx a)))
    (hσ x.2 (fun a => congrArg Prod.snd (hx a)))

/-- Central kernels and trivial quotients preserve a cubic witness on a Sylow
fixed space, without a normalizer or splitting hypothesis. The map need not
be onto; in an exact extension it is the usual surjective section map. -/
theorem sylow_fixedSpace_enlargement_of_central_section [Finite G]
    (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) G W)
    (U : Subrepresentation ρ) (q : U.toSubmodule →ₗ[ZMod 2] W)
    (hq : ∀ g u, q (U.toRepresentation g u) = σ g (q u))
    (hker : ∀ g u, q u = 0 → U.toRepresentation g u = u)
    (hquot : ∀ g v, ρ g v - v ∈ U) (S : Sylow 2 G)
    (hmodel : ∃ d : G, d ∉ S ∧ d ^ 3 = 1 ∧
      ∀ w ∈ fixedSpace σ (S : Subgroup G), σ d w = w) :
    ∃ d : G, d ∉ S ∧ d ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace ρ (S : Subgroup G), ρ d v = v := by
  obtain ⟨d, hd, h3, hf⟩ := hmodel
  have hU := cubic_fixedSpace_of_map U.toRepresentation σ (S : Subgroup G)
    d h3 q hq (fun u hu => hker d u hu) hf
  let i : U.toRepresentation.IntertwiningMap ρ :=
    { toLinearMap := U.toSubmodule.subtype
      isIntertwining' _ := by ext; rfl }
  exact ⟨d, hd, h3, fixes_of_trivial_quotient ρ U.toRepresentation i
    Subtype.val_injective (fun g v => ⟨⟨_, hquot g v⟩, rfl⟩) S hU⟩

end Representation.BinarySylowFixedSpace
