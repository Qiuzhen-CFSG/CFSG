module

public import Theory.GroupTheory.AlternatingPowerTwoExtension

/-!
# Transport of alternating-power extensions

A group isomorphism transports the normal subgroup, its two-group upper
quotient, and its surjection onto a finite power of an alternating group.
The lower kernel is pulled back along the induced subgroup isomorphism.

This allows an extension constructed inside a local overgroup to be viewed
in the ambient group, as in the component-orbit construction of
Aschbacher–Smith 2.3.9(7)(f), printed pp.525–526.
-/

public section

namespace Theory.GroupTheory

/-- An isomorphism preserves the actual normal-series and quotient-map
witnesses of an alternating-power extension. -/
theorem AlternatingPowerTwoExtension.of_equiv
    {K K' : Type*} [Group K] [Group K'] {d : ℕ}
    (h : AlternatingPowerTwoExtension K d) (e : K ≃* K') :
    AlternatingPowerTwoExtension K' d := by
  obtain ⟨N, hN, hq, n, f, hf, hk⟩ := h
  let N' := N.map e.toMonoidHom
  let : N'.Normal := hN.map e.toMonoidHom e.surjective
  let eN : N ≃* N' := e.subgroupMap N
  refine ⟨N', inferInstance, hq.of_equiv (QuotientGroup.congr N N' e rfl),
    n, f.comp eN.symm.toMonoidHom, hf.comp eN.symm.surjective, ?_⟩
  rw [← MonoidHom.comap_ker]
  exact hk.comap_of_injective eN.symm.toMonoidHom eN.symm.injective

end Theory.GroupTheory

end
