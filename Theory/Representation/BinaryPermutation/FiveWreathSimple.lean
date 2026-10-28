module
public import Theory.Representation.BinaryPermutation.FiveTensorSquare.Constituent
public import Theory.Representation.BinaryPermutation.FivePairWreath
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Simplicity of the deleted wreath modules

Density for the absolutely irreducible five-letter core gives simplicity
of the tensor under the alternating base, hence under the full wreath group.
On the pair, the class sum of the twenty three-cycles projects onto an axis;
core simplicity and factor exchange then generate the whole pair.

Source: Aschbacher--Smith 10.3.1, printed pp.755--756.
-/

public section
open scoped TensorProduct
open Representation Representation.QuadraticFourGroup.TensorClassification
namespace BinaryPermutation.FiveTensorSquare

theorem deletedAction_irreducible : deletedAction.IsIrreducible := by
  let : δ.IsIrreducible := core_irreducible
  let : Nontrivial C := Subrepresentation.irreducible_module_nontrivial δ
  have hd := jacobson_density_surjective_rep δ
    ((isAbsolutelyIrreducible_iff_surjective δ).mp core_absolute)
  apply irreducible_of_jacobson_density_surjective
  let A := Algebra.adjoin (ZMod 2) (Set.range (deletedAction))
  have hleft (f : Module.End (ZMod 2) C) : LinearMap.rTensor C f ∈ A := by
    have h : Algebra.adjoin (ZMod 2) (Set.range δ) ≤
        A.comap (Module.End.rTensorAlgHom (ZMod 2) C C) := by
      apply Algebra.adjoin_le
      rintro _ ⟨g, rfl⟩
      change TensorProduct.map (δ g) LinearMap.id ∈ A
      have := Algebra.subset_adjoin (R := (ZMod 2)) (s := Set.range (deletedAction))
        (Set.mem_range_self (g, 1))
      simpa [deletedAction, externalTensor_apply, Module.End.one_eq_id, A] using this
    rw [hd] at h
    exact h (by trivial)
  have hright (f : Module.End (ZMod 2) C) : LinearMap.lTensor C f ∈ A := by
    have h : Algebra.adjoin (ZMod 2) (Set.range δ) ≤
        A.comap (Module.End.lTensorAlgHom (ZMod 2) C C) := by
      apply Algebra.adjoin_le
      rintro _ ⟨g, rfl⟩
      change TensorProduct.map LinearMap.id (δ g) ∈ A
      have := Algebra.subset_adjoin (R := (ZMod 2)) (s := Set.range (deletedAction))
        (Set.mem_range_self (1, g))
      simpa [deletedAction, externalTensor_apply, Module.End.one_eq_id, A] using this
    rw [hd] at h
    exact h (by trivial)
  apply top_unique
  intro f hf
  clear hf
  change f ∈ A
  obtain ⟨x, rfl⟩ := (homTensorHomEquiv (ZMod 2) C C C C).surjective f
  induction x using TensorProduct.induction_on with
  | zero => simpa only [map_zero] using A.zero_mem
  | tmul f g =>
    rw [homTensorHomEquiv_apply, TensorProduct.homTensorHomMap_apply]
    have hm := A.mul_mem (hleft f) (hright g)
    convert hm using 1
    ext u v
    simp [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
  | add x y hx hy => simpa only [map_add] using A.add_mem hx hy

theorem tensorWreathAction_irreducible : tensorWreathAction.IsIrreducible := by
  let : deletedAction.IsIrreducible := deletedAction_irreducible
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial deletedAction
  rw [Representation.IsIrreducible, isSimpleOrder_iff]
  refine ⟨inferInstance, fun S => ?_⟩
  let T : Subrepresentation deletedAction := {
    toSubmodule := S.toSubmodule
    apply_mem_toSubmodule g v hv := by
      rw [← tensorWreathAction_comp_alternatingBase]
      exact S.apply_mem_toSubmodule (alternatingBase g) hv }
  rcases eq_bot_or_eq_top T with ht | ht
  · exact Or.inl (Subrepresentation.toSubmodule_injective
      (congrArg (fun R : Subrepresentation deletedAction => R.toSubmodule) ht))
  · exact Or.inr (Subrepresentation.toSubmodule_injective
      (congrArg (fun R : Subrepresentation deletedAction => R.toSubmodule) ht))

private theorem pair_base_left (g : Sym) (u v : C) :
    FivePair.wreathRepresentation (base (g,1)) (u,v) =
      (coreRepresentation (Fin 5) g u,v) := by
  simp [FivePair.wreathRepresentation_apply, base, FivePair.swapIndex]

private theorem pair_exchange (u v : C) :
    FivePair.wreathRepresentation (⟨fun _ => 1,swapIndex⟩ : Wreath) (u,v) = (v,u) := by
  simp [FivePair.wreathRepresentation_apply]

private theorem pair_projection (S : Subrepresentation FivePair.wreathRepresentation)
    (u v : C) (h : (u,v) ∈ S.toSubmodule) : (u,0) ∈ S.toSubmodule := by
  have hh := S.toSubmodule.sum_mem (fun g (_ : g ∈ FiveCentralExtension.cubes) =>
    S.apply_mem_toSubmodule (base (g,1)) h)
  have he : (∑ g ∈ FiveCentralExtension.cubes,
      FivePair.wreathRepresentation (base (g,1)) (u,v)) = (u,0) := by
    apply Prod.ext
    · simpa only [Prod.fst_sum, pair_base_left] using FiveCentralExtension.core_sum u
    · simp only [Prod.snd_sum, pair_base_left]
      rw [Finset.sum_const, FiveCentralExtension.cubes_card,
        ← Nat.cast_smul_eq_nsmul (R := ZMod 2)]
      change (20 : ZMod 2) • v = 0
      rw [show (20 : ZMod 2) = 0 from rfl, zero_smul]
  exact he ▸ hh

theorem pairWreathAction_irreducible : FivePair.wreathRepresentation.IsIrreducible := by
  let : δ.IsIrreducible := core_irreducible
  let : Nontrivial C := Subrepresentation.irreducible_module_nontrivial δ
  rw [Representation.IsIrreducible, isSimpleOrder_iff]
  refine ⟨inferInstance, fun S => ?_⟩
  let L : Subrepresentation δ := {
    toSubmodule := S.toSubmodule.comap (LinearMap.inl (ZMod 2) C C)
    apply_mem_toSubmodule g u hu := by
      change (coreRepresentation (Fin 5) g.val u, 0) ∈ S.toSubmodule
      rw [← pair_base_left g.val u 0]
      exact S.apply_mem_toSubmodule (base (g.val,1)) hu }
  rcases eq_bot_or_eq_top L with hL | hL
  · left
    apply Subrepresentation.toSubmodule_injective
    apply le_antisymm _ bot_le
    rintro ⟨u,v⟩ huv
    have hu : u = 0 := by
      have h : u ∈ L.toSubmodule := pair_projection S u v huv
      rw [hL] at h
      exact h
    have hv : v = 0 := by
      have hswap : (v,u) ∈ S.toSubmodule :=
        pair_exchange u v ▸ S.apply_mem_toSubmodule (⟨fun _ => 1,swapIndex⟩ : Wreath) huv
      have h : v ∈ L.toSubmodule := pair_projection S v u hswap
      rw [hL] at h
      exact h
    simp [hu,hv]
  · right
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    rintro ⟨u,v⟩ _
    have hl (w : C) : (w,0) ∈ S.toSubmodule := by
      have h : w ∈ L.toSubmodule := by rw [hL]; trivial
      exact h
    have hr : (0,v) ∈ S.toSubmodule :=
      pair_exchange v 0 ▸ S.apply_mem_toSubmodule (⟨fun _ => 1,swapIndex⟩ : Wreath) (hl v)
    simpa only [Prod.mk_add_mk, add_zero, zero_add] using S.toSubmodule.add_mem (hl u) hr

end BinaryPermutation.FiveTensorSquare
