module

public import Theory.Representation.BinaryOffender.CodimensionSieve
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# Displacement bounds for small binary actors

An actor fixing `F` pointwise and displacing every vector into `S` embeds
into the linear maps from `U/F` to `S`. Counting those maps bounds its
binary rank by `dim(U/F) * dim(S)`. In particular a rank-three actor fixing
a codimension-two subspace cannot have a common one-dimensional center.

The remaining lemmas give exact codimension decomposition and descend a
commutator bound from a supplement to the literal quotient representation.
These are intrinsic linear arguments used at the end of Aschbacher–Smith,
*The Classification of Quasithin Groups*, 13.8.25, printed pp.961–962
(combined manuscript, 1 March 2004).
-/

public section

namespace Representation.BinaryOffender
variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U] (ρ : Representation (ZMod 2) H U)

/-- Faithfulness embeds the actor, by displacement, into Hom(U/F,S). No
elementary-abelian hypothesis is needed for this logarithmic cardinality
bound. -/
theorem rank_le_fixed_codim_mul_displacement_dim
    (hρ : Function.Injective ρ) (A : Subgroup H)
    (F S : Submodule (ZMod 2) U) (hF : F ≤ fixedSpace ρ A)
    (hS : ∀ a ∈ A, ∀ u : U, ρ a u - u ∈ S) :
    rank A ≤ Module.finrank (ZMod 2) (U ⧸ F) * Module.finrank (ZMod 2) S := by
  classical
  let d (a : A) : U →ₗ[ZMod 2] S :=
    (ρ a - LinearMap.id).codRestrict S (hS a a.property)
  have hd (a : A) : F ≤ (d a).ker := by
    intro u hu
    apply Subtype.ext
    change ρ a u - u = 0
    exact sub_eq_zero.mpr (hF hu a)
  let f (a : A) : (U ⧸ F) →ₗ[ZMod 2] S := F.liftQ (d a) (hd a)
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply hρ
    ext u
    have hu := congrArg (fun l : (U ⧸ F) →ₗ[ZMod 2] S => (l (F.mkQ u) : U)) hab
    change ρ a u - u = ρ b u - u at hu
    exact sub_left_injective hu
  let : Finite ((U ⧸ F) →ₗ[ZMod 2] S) := Module.finite_of_finite (ZMod 2)
  have hc := Nat.card_le_card_of_injective f hf
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := (U ⧸ F) →ₗ[ZMod 2] S),
    Nat.card_zmod, Module.finrank_linearMap] at hc
  have hl := Nat.log_monotone (b := 2) hc
  simpa only [rank, Nat.log_pow (by decide : 1 < 2)] using hl

/-- An actor of binary rank three fixing a subspace of codimension at most two
cannot have all its displacements in a line. -/
theorem rank_three_commutator_dim_gt_one
    (hρ : Function.Injective ρ) (A : Subgroup H)
    (F : Submodule (ZMod 2) U) (hF : F ≤ fixedSpace ρ A)
    (hdim : Module.finrank (ZMod 2) (U ⧸ F) ≤ 2) (hrank : rank A = 3) :
    1 < Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ A) := by
  have hr := rank_le_fixed_codim_mul_displacement_dim ρ hρ A F
    (subspaceCommutator ρ ⊤ A) hF (fun a ha u =>
      Submodule.subset_span ⟨a, ha, u, Submodule.mem_top, rfl⟩)
  by_contra hn
  have hle : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ A) ≤ 1 := by omega
  have hmul := Nat.mul_le_mul hdim hle
  omega

/-- The exact contribution of an intersected subspace and its quotient to
codimension. -/
theorem codim_decomposition (W D : Submodule (ZMod 2) U) :
    Module.finrank (ZMod 2) (U ⧸ (W ⊔ D)) +
      Module.finrank (ZMod 2) (W ⧸ D.comap W.subtype) =
        Module.finrank (ZMod 2) (U ⧸ D) := by
  let e : D.comap W.subtype ≃ₗ[ZMod 2] (W ⊓ D : Submodule (ZMod 2) U) :=
    { toFun := fun w => ⟨w.val, w.val.property, w.property⟩
      invFun := fun w => ⟨⟨w, w.property.1⟩, w.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have he := e.finrank_eq
  have := (D.comap W.subtype).finrank_quotient_add_finrank
  have := D.finrank_quotient_add_finrank
  have := (W ⊔ D).finrank_quotient_add_finrank
  have := W.finrank_sup_add_finrank_inf_eq D
  omega

omit [FiniteDimensional (ZMod 2) U] in
/-- A commutator bound on a supplement descends to the whole quotient
representation. -/
theorem quotient_commutator_le_of_supplement
    (W : Subrepresentation ρ) (D S : Submodule (ZMod 2) U) (A : Subgroup H)
    (hsup : W.toSubmodule ⊔ D = ⊤)
    (hcomm : ∀ a ∈ A, ∀ d ∈ D, ρ a d - d ∈ S) :
    subspaceCommutator W.quotientRepresentation ⊤ A ≤ S.map W.toSubmodule.mkQ := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a, ha, q, _, rfl⟩
  induction q using Submodule.Quotient.induction_on with
  | _ u =>
    have hu : u ∈ W.toSubmodule ⊔ D := by rw [hsup]; trivial
    obtain ⟨w, hw, d, hd, rfl⟩ := Submodule.mem_sup.mp hu
    refine ⟨ρ a d - d, hcomm a ha d hd, ?_⟩
    have hw0 : W.toSubmodule.mkQ w = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hw
    have haw0 : W.toSubmodule.mkQ (ρ a w) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr (W.apply_mem_toSubmodule a hw)
    change W.toSubmodule.mkQ (ρ a d - d) =
      W.toSubmodule.mkQ (ρ a (w + d)) - W.toSubmodule.mkQ (w + d)
    simp only [map_add, map_sub, hw0, haw0, zero_add]

end Representation.BinaryOffender
