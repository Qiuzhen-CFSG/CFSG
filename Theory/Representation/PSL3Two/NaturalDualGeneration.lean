module
public import Theory.Representation.PSL3Two.PairedNaturalDual
public import Theory.Representation.SimpleHeadQuotient.DistinctPair
public import Theory.Representation.PSL3Two.IrreducibleCatalogue

/-!
# Generation of a natural--dual component support

The natural and dual binary three-spaces are inequivalent simple modules.
An invariant subspace is therefore one of the four coordinate sums. An outer
operator exchanges the two axes, leaving only zero and the whole six-space.
The embedding theorem applies this to the original component support inside
an ambient module; no orbit-generation hypothesis is required.

Source: Aschbacher--Smith 14.6.24(3), the equality exclusion on printed p.1040.
The literal core-intersection consumer is TwoComponents/Properness.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace BinaryLinearThree.NaturalDual

/-- A nonzero subspace stable under the inner group and one diagram
operator is the whole natural--dual space. -/
theorem eq_top_of_inner_outer_stable
    (S : Submodule (ZMod 2) Space) (hn : S ≠ ⊥)
    (hi : ∀ k v, v ∈ S → action k v ∈ S)
    (a : MulAut Group) (ha : a ∉ MulAut.innerSubgroup Group)
    (hs : ∀ v, v ∈ S → autAction a v ∈ S) : S = ⊤ := by
  let := IrreducibleCatalogue.natural_irreducible
  let := IrreducibleCatalogue.dual_irreducible
  let f := LinearMap.GeneralLinearGroup.toLinearEquiv (autAction.asGroupHom a)
  have hf : ∀ k v, f (action k v) = action (a k) (f v) := by
    intro k v
    change autAction a (action k v) = action (a k) (autAction a v)
    rw [←autAction_inner k,←autAction_inner (a k)]
    have he : a * MulAut.conj k = MulAut.conj (a k) * a := by
      ext x
      simp only [MulAut.mul_apply,MulAut.conj_apply,map_mul,map_inv]
    rw [←Module.End.mul_apply,←map_mul,he,map_mul,Module.End.mul_apply]
  have hswap := outer_swaps a f hf ha
  rcases SimpleHeadQuotient.distinct_pair_submodules W W.dual
    AutomorphismAction.natural_not_equiv_dual S hi with hz | hl | hr | ht
  · exact (hn hz).elim
  · obtain ⟨v,hv⟩ := exists_ne (0 : Vector)
    have hm := hs (v,0) (by rw [hl]; simp)
    rw [hl] at hm
    have he : f (v,0) = 0 := Prod.ext (hswap.1 v) hm.2
    exact (hv (congrArg Prod.fst (f.injective (he.trans f.map_zero.symm)))).elim
  · obtain ⟨v,hv⟩ := exists_ne (0 : Module.Dual (ZMod 2) Vector)
    have hm := hs (0,v) (by rw [hr]; simp)
    rw [hr] at hm
    have he : f (0,v) = 0 := Prod.ext hm.1 (hswap.2 v)
    exact (hv (congrArg Prod.snd (f.injective (he.trans f.map_zero.symm)))).elim
  · exact ht

namespace Paired.Marking
variable {H E : Type*} [_root_.Group H] [AddCommGroup E] [Module (ZMod 2) E]
  {ρ : Representation (ZMod 2) H E} (m : Paired.Marking ρ)

/-- An invariant subspace meeting the first marked support nontrivially
contains that support, provided its normalizer realizes the inner and
an outer action on the same component. -/
theorem left_range_le_of_invariant_intersection
    (S : Submodule (ZMod 2) E) (hs : ∀ a v, v ∈ S → ρ a v ∈ S)
    (hn : S.comap m.leftEmbedding ≠ ⊥)
    (κ : Group →* H) (hκ : ∀ k, m.left (κ k) = MulAut.conj k)
    (a : H) (ha : m.left a ∉ MulAut.innerSubgroup Group) :
    m.leftEmbedding.range ≤ S := by
  have he : S.comap m.leftEmbedding = ⊤ :=
    eq_top_of_inner_outer_stable _ hn
      (fun k v hv => by
        change m.leftEmbedding (action k v) ∈ S
        rw [←autAction_inner k,←hκ k,←m.left_intertwines]
        exact hs (κ k) _ hv)
      (m.left a) ha (fun v hv => by
        change m.leftEmbedding (autAction (m.left a) v) ∈ S
        rw [←m.left_intertwines]
        exact hs a _ hv)
  rintro _ ⟨v,rfl⟩
  have hv : v ∈ S.comap m.leftEmbedding := by rw [he]; trivial
  exact hv
end Paired.Marking
end BinaryLinearThree.NaturalDual
