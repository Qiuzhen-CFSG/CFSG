module
public import Theory.SpecificGroups.OmegaSixThree.TriangleLocal.EdgeMarks

/-!
# The unique marked cyclic-four subgroup in the local model

An element centralizing the actual second S₄ factor has trivial second
coordinate, since S₄ has trivial center. A check of the 24 first-factor
permutations shows that the marked double transposition has just two square
roots, the specified reversal and its inverse. This preserves the exact local
coordinates used by the F.5.7 map correction.
Source: Aschbacher--Smith F.5.5 and F.5.7, printed pp.301--303.
-/

public section

namespace OmegaSixThree.TriangleLocal

private theorem four_centerless : ∀ s : Four,
    (∀ t : Four, s*t=t*s) → s=1 := by
  decide +kernel

private theorem graph_square_roots : ∀ p : Four,
    p^2 = Equiv.swap 0 3 * Equiv.swap 1 2 →
      p = reversalPermutation ∨ p = reversalPermutation⁻¹ := by
  decide +kernel

/-- Among elements centralizing the actual second factor, the specified
reversal and its inverse are the only square roots of the graph involution. -/
theorem graph_root_eq_reversal_or_inv (q : H) (hsq : q^2 = graphElement)
    (hc : ∀ g : H, g ∈ complementFactor → q*g=g*q) :
    q = edgeReversal ∨ q = edgeReversal⁻¹ := by
  have hsecond : (productEquiv q).2 = 1 := by
    apply four_centerless
    intro s
    have hh := hc (productEquiv.symm (1,s)) (by
      change productEquiv (productEquiv.symm (1,s)) ∈ (⊥ : Subgroup Four).prod ⊤
      rw [productEquiv.apply_symm_apply]
      exact ⟨rfl,Subgroup.mem_top _⟩)
    simpa only [map_mul,Prod.snd_mul,productEquiv.apply_symm_apply] using
      congrArg (fun x : H => (productEquiv x).2) hh
  have hfirst : (productEquiv q).1^2 = Equiv.swap 0 3 * Equiv.swap 1 2 := by
    have hh := congrArg (fun x : H => (productEquiv x).1) hsq
    simpa only [map_pow,pow_two,map_mul,Prod.fst_mul,graphElement_image] using hh
  rcases graph_square_roots _ hfirst with h | h
  · left
    apply productEquiv.injective
    rw [edgeReversal_image]
    exact Prod.ext h hsecond
  · right
    apply productEquiv.injective
    rw [map_inv,edgeReversal_image]
    exact Prod.ext h (by simpa only [Prod.snd_inv,inv_one] using hsecond)

end OmegaSixThree.TriangleLocal
