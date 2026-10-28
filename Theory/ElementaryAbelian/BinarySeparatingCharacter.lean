module

public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Binary characters separating subgroups

A subgroup of an elementary abelian two-group is a binary subspace. A linear
functional separating a vector from that subspace gives a multiplicative
binary character killing the subgroup. Finiteness is not required.
-/

public section

open scoped IsMulCommutative

namespace IsElementaryAbelian

variable {D : Type*} [Group D] [IsElementaryAbelian 2 D]

/-- A binary character can kill a subgroup while detecting any element outside it. -/
theorem exists_binary_character_of_notMem (T : Subgroup D) {x : D} (hx : x ∉ T) :
    ∃ χ : D →* Multiplicative (ZMod 2), χ x ≠ 1 ∧ T ≤ χ.ker := by
  let U : Submodule (ZMod 2) (Additive D) :=
    AddSubgroup.toZModSubmodule 2 T.toAddSubgroup
  obtain ⟨f, hfx, hfU⟩ := Submodule.exists_dual_map_eq_bot_of_notMem
    (show Additive.ofMul x ∉ U from hx) inferInstance
  let χ : D →* Multiplicative (ZMod 2) := f.toAddMonoidHom.toMultiplicativeRight
  refine ⟨χ, ?_, ?_⟩
  · change f (Additive.ofMul x) ≠ 0
    exact hfx
  · intro t ht
    change f (Additive.ofMul t) = 0
    have hft : f (Additive.ofMul t) ∈ U.map f :=
      Submodule.mem_map_of_mem (show Additive.ofMul t ∈ U from ht)
    rwa [hfU, Submodule.mem_bot] at hft

/-- Every proper subgroup of an elementary abelian two-group is killed by a
nontrivial binary character. -/
theorem exists_nontrivial_binary_character (T : Subgroup D) (hT : T ≠ ⊤) :
    ∃ χ : D →* Multiplicative (ZMod 2), χ ≠ 1 ∧ T ≤ χ.ker := by
  obtain ⟨x, _, hx⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hT)
  obtain ⟨χ, hxχ, hTχ⟩ := exists_binary_character_of_notMem T hx
  refine ⟨χ, ?_, hTχ⟩
  intro hχ
  exact hxχ (by simp only [hχ, MonoidHom.one_apply])

end IsElementaryAbelian
