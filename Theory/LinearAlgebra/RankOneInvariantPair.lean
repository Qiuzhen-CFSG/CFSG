module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# A rank-one map on disjoint invariant subspaces

A linear map of rank at most one must vanish on one of two disjoint invariant
subspaces. Otherwise the image of each nontrivial restriction is the whole
one-dimensional image, contradicting disjointness. This supplies the cyclic
rank-one selection on the literal quotient summands of Aschbacher–Smith
B.5.6(3), used in G.6.4 and C.5.12.
-/

public section

namespace LinearMap
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]

theorem invariant_disjoint_pair_rank_one (f : V →ₗ[k] V)
    (hr : Module.finrank k (LinearMap.range f) ≤ 1)
    (U W : Submodule k V) (hd : Disjoint U W)
    (hU : U.map f ≤ U) (hW : W.map f ≤ W) :
    U ≤ LinearMap.ker f ∨ W ≤ LinearMap.ker f := by
  by_cases hu : U.map f = ⊥
  · left
    intro v hv
    have hh : f v ∈ U.map f := ⟨v,hv,rfl⟩
    simpa only [hu, Submodule.mem_bot, LinearMap.mem_ker] using hh
  · right
    have hle : U.map f ≤ LinearMap.range f := by
      rintro _ ⟨v,_,rfl⟩
      exact LinearMap.mem_range_self _ v
    have hpos : 0 < Module.finrank k (U.map f) :=
      Nat.pos_of_ne_zero (fun hz => hu (Submodule.finrank_eq_zero.mp hz))
    have he : U.map f = LinearMap.range f :=
      Submodule.eq_of_le_of_finrank_eq hle (by have := Submodule.finrank_mono hle; omega)
    intro w hw
    have hwu : f w ∈ U := hU (he.symm ▸ LinearMap.mem_range_self f w)
    have hww : f w ∈ W := hW ⟨w,hw,rfl⟩
    exact Submodule.disjoint_def.mp hd (f w) hwu hww
end LinearMap
