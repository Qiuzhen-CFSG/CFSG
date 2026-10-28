module

public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Displacement.Odd
public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Cubic permutations and displacement in the exceptional code branch

The native M22 embedding fixes two distinguished coordinates. Its support
therefore has the same size on 22 and 24 points. The established six fixed
points on 24 points give precisely six three-cycles and four fixed points
on 22 points. A cubic in the full setwise pair stabilizer fixes the pair
pointwise, so the native code and cocode displacement results apply there too.

Source: Aschbacher–Smith, Proposition 8.2.2(1), printed p.715 (PDF p.732),
combined manuscript of 1 March 2004. This establishes the cycle assertion
and displacement six; identifying the number of noncentral chief factors
also requires the binary order-three chief-factor calculation.
-/

public section
open Sporadic.Mathieu MathieuCode Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Exclusion.CodeParabolic
noncomputable section

private theorem coordinates_cover (i : Fin 24) :
    i = 0 ∨ i = 9 ∨ ∃ j : Fin 22, m22Coordinates j = i := by
  revert i
  decide +kernel

/-- The native embedding adds two fixed points and preserves the moved points. -/
theorem support_card_embedding (g : M22) :
    (m22Embedding g).val.support.card = g.val.support.card := by
  classical
  symm
  apply Finset.card_bij (fun i _ => m22Coordinates i)
  · intro i hi
    rw [Equiv.Perm.mem_support] at hi ⊢
    rw [m22Embedding_apply]
    exact fun he => hi (m22Coordinates.injective he)
  · intro i hi j hj he
    exact m22Coordinates.injective he
  · intro i hi
    rw [Equiv.Perm.mem_support] at hi
    rcases coordinates_cover i with rfl | rfl | ⟨j, rfl⟩
    · exact False.elim (hi (m22Embedding_fixed_zero g))
    · exact False.elim (hi (m22Embedding_fixed_nine g))
    · refine ⟨j, ?_, rfl⟩
      rw [Equiv.Perm.mem_support]
      intro hj
      exact hi ((m22Embedding_apply g j).trans (congrArg m22Coordinates hj))

private theorem cyclic_fixed_points (g : M24) :
    MulAction.fixedPoints (zpowers g) (Fin 24) = Function.fixedPoints g.val := by
  ext i
  constructor
  · intro hi
    exact hi ⟨g, mem_zpowers g⟩
  · intro hi k
    have hle : zpowers g ≤ MulAction.stabilizer M24 i := zpowers_le.mpr hi
    exact hle k.property

/-- On the source's 22 points a cubic has exactly six disjoint three-cycles. -/
theorem m22_cubic_cycleType (g : M22) (hg : orderOf g = 3) :
    g.val.cycleType = Multiset.replicate 6 3 := by
  classical
  have hfix := m22_cubic_six_fixed (zpowers g) ((Nat.card_zpowers g).trans hg)
  rw [MonoidHom.map_zpowers, cyclic_fixed_points, Nat.card_eq_fintype_card,
    Equiv.Perm.card_fixedPoints, Equiv.Perm.sum_cycleType,
    support_card_embedding, Fintype.card_fin] at hfix
  have ho : orderOf g.val = 3 :=
    (orderOf_injective M22.subtype M22.subtype_injective g).trans hg
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order (σ := g.val)
    (by rw [ho]; decide)
  rw [ho] at hn
  have hsum := g.val.sum_cycleType
  rw [hn, Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id] at hsum
  have hn6 : n + 1 = 6 := by
    omega
  simpa only [hn6] using hn

/-- In particular there are four fixed points on 22 points, not six. -/
theorem m22_cubic_four_fixed (g : M22) (hg : orderOf g = 3) :
    Nat.card (Function.fixedPoints g.val) = 4 := by
  classical
  rw [Nat.card_eq_fintype_card, Equiv.Perm.card_fixedPoints, m22_cubic_cycleType g hg]
  norm_num

/-- An element of order three cannot exchange the distinguished two points. -/
theorem cubic_pair_fixes_zero (g : MathieuCode.m22PairStabilizer) (hg : orderOf g = 3) :
    g.val.val 0 = 0 := by
  have hmem (i : Fin 24) (hi : i ∈ m22Pair) : g.val.val i ∈ m22Pair :=
    MulAction.mem_stabilizer_finset'.mp g.property hi
  have h0 : g.val.val 0 = 0 ∨ g.val.val 0 = 9 := by
    simpa [m22Pair] using hmem 0 (by simp [m22Pair])
  rcases h0 with h0 | h0
  · exact h0
  have h9 : g.val.val 9 = 0 ∨ g.val.val 9 = 9 := by
    simpa [m22Pair] using hmem 9 (by simp [m22Pair])
  have h90 : g.val.val 9 = 0 := h9.resolve_right (fun he => by
    have hh := g.val.val.injective (h0.trans he.symm)
    exact (by decide : (0 : Fin 24) ≠ 9) hh)
  have hp : g ^ 3 = 1 := hg ▸ pow_orderOf_eq_one g
  have he := congrArg (fun x : MathieuCode.m22PairStabilizer => x.val.val (0 : Fin 24)) hp
  change g.val.val (g.val.val (g.val.val 0)) = 0 at he
  rw [h0, h90, h0] at he
  exact False.elim ((by decide : (9 : Fin 24) ≠ 0) he)

/-- Every cubic in the full outer action comes from the actual native M22. -/
theorem cubic_pair_lifts (g : MathieuCode.m22PairStabilizer) (hg : orderOf g = 3) :
    ∃ u : M22, m22ToPairStabilizer u = g ∧ orderOf u = 3 := by
  have h0 := cubic_pair_fixes_zero g hg
  have h9 : g.val.val 9 = 9 := by
    have hmem := MulAction.mem_stabilizer_finset'.mp g.property
      (by simp [m22Pair] : (9 : Fin 24) ∈ m22Pair)
    change g.val.val 9 ∈ m22Pair at hmem
    have h : g.val.val 9 = 0 ∨ g.val.val 9 = 9 := by simpa [m22Pair] using hmem
    exact h.resolve_left (fun he => (by decide : (9 : Fin 24) ≠ 0)
      (g.val.val.injective (he.trans h0.symm)))
  have hm : g.val ∈ m22Embedding.range := by
    rw [m22Embedding_range]
    exact ⟨h0, h9⟩
  obtain ⟨u, hu⟩ := hm
  have hue : m22ToPairStabilizer u = g := Subtype.ext hu
  refine ⟨u, hue, ?_⟩
  have hinj : Function.Injective m22ToPairStabilizer := by
    intro a b h
    exact m22Embedding_injective (congrArg Subtype.val h)
  rw [← orderOf_injective m22ToPairStabilizer hinj u, hue]
  exact hg

/-- The literal outer code and cocode both have cubic displacement six. -/
theorem outer_cubic_displacement (D : Subgroup MathieuCode.m22PairStabilizer)
    (hD : Nat.card D = 3) :
    fixedCodim m22OuterCodeRepresentation D = 6 ∧
      fixedCodim m22OuterCocodeRepresentation D = 6 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : IsCyclic D := isCyclic_of_prime_card hD
  obtain ⟨g, rfl⟩ := D.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  have hg : orderOf g = 3 := (Nat.card_zpowers g).symm.trans hD
  obtain ⟨u, rfl, hu⟩ := cubic_pair_lifts g hg
  have hc := m22_cubic_code_displacement (zpowers u) ((Nat.card_zpowers u).trans hu)
  have ht := m22_cubic_cocode_displacement (zpowers u) ((Nat.card_zpowers u).trans hu)
  constructor
  · rw [← MonoidHom.map_zpowers, fixedCodim, ← fixedSpace_comp_map]
    exact hc
  · rw [← MonoidHom.map_zpowers, fixedCodim, ← fixedSpace_comp_map]
    exact ht

end
end CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Exclusion.CodeParabolic
