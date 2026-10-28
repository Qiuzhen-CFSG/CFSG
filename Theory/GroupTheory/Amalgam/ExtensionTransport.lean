module

public import Theory.GroupTheory.Amalgam.SylowRigidity

/-!
# Transport of endpoint extension properties

A commuting square of group isomorphisms transports an automorphism extending
an overlap map. Conjugating both automorphisms preserves the square. Keeping
the proof at the abstract group level avoids unfolding concrete model groups.
The binary G₂ exceptional amalgam is an application.
-/

public section
namespace Theory.GroupTheory.RankTwoAmalgam
variable {L B L' B' : Type*} [Group L] [Group B] [Group L'] [Group B']

/-- Transport a universal overlap-extension property across a commuting square. -/
theorem extendsAcross_of_equivalences
    {i : B →* L} {j : B' →* L'} (f : L ≃* L') (e : B ≃* B')
    (h : ∀ b, f (i b) = j (e b))
    (hall : ∀ d : MulAut B, ExtendsAcross i d) (d : MulAut B') :
    ExtendsAcross j d := by
  let d' := e.trans (d.trans e.symm)
  obtain ⟨a, ha⟩ := hall d'
  have hs (b : B') : f.symm (j b) = i (e.symm b) := by
    apply f.injective
    rw [f.apply_symm_apply, h, e.apply_symm_apply]
  refine ⟨f.symm.trans (a.trans f), fun b => ?_⟩
  change f (a (f.symm (j b))) = j (d b)
  rw [hs, ha, h]
  simp only [d', MulEquiv.trans_apply, MulEquiv.apply_symm_apply]

end Theory.GroupTheory.RankTwoAmalgam
