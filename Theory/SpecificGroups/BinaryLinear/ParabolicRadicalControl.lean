module
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.RadicalOrientation.Basic
public import Theory.GroupTheory.ConjugateSpanOrder
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Recovering a binary parabolic from its radical

A subspace invariant under the full block radical is either contained in its
fixed space or contains that fixed space. In particular, the fixed space is
its unique invariant subspace of that dimension. Consequently any subgroup
between the radical and its parabolic has its normalizer in the parabolic.
The same applies to a conjugate closure which remains in the parabolic.

This is the linear geometric step used in Aschbacher--Smith, 12.5.4,
printed p.819. The proof uses rank-one transvections and finite dimension;
no finite subgroup enumeration or classification hypothesis is needed.
-/

public noncomputable section
open Subgroup
namespace BinaryLinear
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Every invariant subspace of a full block radical is comparable with its fixed space. -/
theorem comparable_of_radical_le_parabolic (W U : Submodule (ZMod 2) V)
    (h : radical W ≤ parabolic U) : U ≤ W ∨ W ≤ U := by
  by_cases hu : U ≤ W
  · exact .inl hu
  · right
    obtain ⟨v,hv,hvW⟩ := SetLike.not_le_iff_exists.mp hu
    obtain ⟨f,hfv,hf⟩ := W.exists_le_ker_of_notMem hvW
    have hf1 : f v = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hfv
    intro w hw
    have ht := (h (transvection_mem hw hf) v).mpr hv
    have hh := U.sub_mem ht hv
    change (v + f v • w) - v ∈ U at hh
    simpa only [hf1,one_smul,add_sub_cancel_left] using hh

/-- A block radical has a unique invariant subspace of the fixed-space dimension. -/
theorem eq_of_radical_le_parabolic [FiniteDimensional (ZMod 2) V]
    (W U : Submodule (ZMod 2) V) (hd : Module.finrank (ZMod 2) W = Module.finrank (ZMod 2) U)
    (h : radical W ≤ parabolic U) : W = U := by
  rcases comparable_of_radical_le_parabolic W U h with hu | hw
  · exact (Submodule.eq_of_le_of_finrank_eq hu hd.symm).symm
  · exact Submodule.eq_of_le_of_finrank_eq hw hd

/-- Any subgroup between a radical and its parabolic has its normalizer in the parabolic. -/
theorem normalizer_le_parabolic_of_radical_le [FiniteDimensional (ZMod 2) V]
    (W : Submodule (ZMod 2) V) (N : Subgroup (BinaryLinear.GL V))
    (hR : radical W ≤ N) (hN : N ≤ parabolic W) :
    normalizer (N : Set (BinaryLinear.GL V)) ≤ parabolic W := by
  intro g hg
  have hm : (radical W).map (MulAut.conj g).toMonoidHom ≤ parabolic W := by
    rintro _ ⟨r,hr,rfl⟩
    exact hN ((mem_normalizer_iff.mp hg r).mp (hR hr))
  rw [OuterCyclic.radical_map_conj] at hm
  have he : W.map g.toLinearMap = W := eq_of_radical_le_parabolic _ _
    (g.finrank_map_eq W) hm
  intro v
  constructor
  · intro hv
    rw [←he] at hv
    obtain ⟨w,hw,hwv⟩ := hv
    exact g.injective hwv ▸ hw
  · intro hv
    rw [←he]
    exact ⟨v,hv,rfl⟩

/-- The normal closure of a seed containing the radical cannot stay in the
parabolic if its actor leaves that parabolic. -/
theorem le_parabolic_of_conjugateSpan_le [FiniteDimensional (ZMod 2) V]
    (W : Submodule (ZMod 2) V) (Y A : Subgroup (BinaryLinear.GL V))
    (hR : radical W ≤ Y) (hc : conjugateSpanBy Y A ≤ parabolic W) :
    A ≤ parabolic W :=
  (le_normalizer_conjugateSpanBy Y A).trans
    (normalizer_le_parabolic_of_radical_le W _ (hR.trans (le_conjugateSpanBy Y A)) hc)

end BinaryLinear
