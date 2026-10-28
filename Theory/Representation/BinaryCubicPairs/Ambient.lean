module

public import Theory.Representation.BinaryCubicPairs.Displacement
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# A small involution in the original ambient representation

Embed the four-dimensional supporting space in the original module. Every
displacement lies in this space and is consequently a cocycle for its faithful
restriction. The checked cubic-pair word gives an actual involution; the
cocycle theorem places all of its ambient displacements in the same span of
two vectors. Its fixed codimension on the original module is at most two.

No involution bound is transferred to a quotient. This is the literal
ambient inequality required in the noncommuting branch of
Aschbacher--Smith E.6.24, printed p.255.
-/

public section
namespace BinaryCubicPairs
open Packed Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- A checked pair in a faithfully represented supporting space forces a
small involution in every ambient extension with trivial quotient. -/
theorem exists_involution_of_certificate
    (ρ : Representation (ZMod 2) G V)
    (j : CoordinateVector →ₗ[ZMod 2] V) (hj : Function.Injective j)
    (μ : G →* CoordinateMatrix) (hμ : Function.Injective μ)
    (haction : ∀ g x, ρ g (j x) = j ((μ g).mulVec x))
    (hquotient : ∀ g v, ∃ x, ρ g v - v = j x)
    (c d : G) (m : BitVec 16)
    (hc : μ c = toMat cubic) (hd : μ d = toMat m)
    (hm : mm (mm m m) m = ident) {k : Certificate} (hk : Valid m k) :
    ∃ t : G, orderOf t = 2 ∧ fixedCodim ρ (Subgroup.zpowers t) ≤ 2 := by
  classical
  let t := groupWord c d k.sequence
  have ht : orderOf t = 2 := orderOf_groupWord μ c d m hc hd hμ hk
  let S : Submodule (ZMod 2) CoordinateVector :=
    Submodule.span (ZMod 2) {toVec k.first, toVec k.second}
  have hN : (ρ t - LinearMap.id).range ≤ S.map j := by
    rintro _ ⟨v, rfl⟩
    let δ : G → CoordinateVector := fun g => Classical.choose (hquotient g v)
    have hδ (g : G) : j (δ g) = ρ g v - v := (Classical.choose_spec (hquotient g v)).symm
    have hδ1 : δ 1 = 0 := by
      apply hj
      rw [hδ, map_one, Module.End.one_apply, sub_self, map_zero]
    have hδmul (g h : G) : δ (g * h) = δ g + (μ g).mulVec (δ h) := by
      apply hj
      rw [map_add, ← haction, hδ, hδ, hδ, map_mul, Module.End.mul_apply, map_sub]
      abel
    have hv : δ t ∈ S := cocycle_mem_span μ δ hδ1 hδmul hμ c d m hc hd hm hk
    exact ⟨δ t, hv, hδ t⟩
  have hdim : Module.finrank (ZMod 2) S ≤ 2 := by
    have hh := finrank_span_le_card
      ({toVec k.first, toVec k.second} : Set CoordinateVector) (R := ZMod 2)
    apply hh.trans
    simp only [Set.toFinset_insert, Set.toFinset_singleton]
    exact (Finset.card_insert_le _ _).trans (by simp)
  refine ⟨t, ht, ?_⟩
  rw [fixedCodim_zpowers_eq_displacement_rank]
  exact (Submodule.finrank_mono hN).trans ((Submodule.finrank_map_le j S).trans hdim)

end BinaryCubicPairs
