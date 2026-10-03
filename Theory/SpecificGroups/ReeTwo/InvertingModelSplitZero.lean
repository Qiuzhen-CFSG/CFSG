module

public import Theory.SpecificGroups.ReeTwo.InvertingModelReduction
public import Theory.SpecificGroups.ReeTwo.RootTwistedFirstCore

/-!
# Reusing the split root-twisted certificate

Census action 19 is exactly `rootTwist * a`. The universal property identifies
its split carry model with the existing semidirect product. Conjugation by `c`
identifies action 0 with action 19. Both identifications preserve the last root,
so the existing first-core certificate proves the split action-0 case.

Source: `RootTwistedFirstCore`, the explicit census root tables, and the
universal marked construction `CyclicFourCentralExtension`.
-/

namespace ReeTwo.InvertingModel
open Core.InvertingActionCensus

private theorem action_nineteen : representative 19 = Core.rootTwist * Core.a := by
  apply Core.aut_ext
  intro j
  rw [representative_root]
  exact (by decide +kernel : ∀ j : CoreRoot,
    representativeRoots 19 j = (Core.rootTwist * Core.a) (Core.root j)) j

private theorem twisted_generate :
    (SemidirectProduct.inl : Core →* RootTwistedSylow).range ⊔
      Subgroup.zpowers RootTwistedSylow.actor = ⊤ := by
  apply top_unique
  intro x _
  rw [← SemidirectProduct.inl_left_mul_inr_right x]
  apply Subgroup.mul_mem
  · exact (show (SemidirectProduct.inl : Core →* RootTwistedSylow).range ≤ _
      from le_sup_left) ⟨_, rfl⟩
  · have h : SemidirectProduct.inr x.right = RootTwistedSylow.actor ^ x.right.toAdd.val := by
      rw [RootTwistedSylow.actor, ← map_pow, FiveFour.generator_pow_val]
    rw [h]
    exact (show Subgroup.zpowers RootTwistedSylow.actor ≤ _ from le_sup_right)
      (Subgroup.npow_mem_zpowers _ _)

private theorem twisted_conj (q : Core) :
    RootTwistedSylow.actor * SemidirectProduct.inl q * RootTwistedSylow.actor⁻¹ =
      SemidirectProduct.inl (representative 19 q) := by
  rw [RootTwistedSylow.actor, ← map_inv, ← SemidirectProduct.inl_aut]
  rw [rootTwistedAction, FiveFour.cyclicHom_generator, action_nineteen]

private theorem twisted_four : RootTwistedSylow.actor ^ 4 =
    SemidirectProduct.inl (CyclicFourCentralExtension.mark false) := by
  decide +kernel

private noncomputable def nineteenEquiv : Model 19 false ≃* RootTwistedSylow :=
  CyclicFourCentralExtension.equiv SemidirectProduct.inl RootTwistedSylow.actor
    twisted_conj twisted_four RootTwistedSylow.card twisted_generate

private theorem nineteenEquiv_mark : nineteenEquiv (mark 19 false) = RootTwistedSylow.root 9 :=
  CyclicFourCentralExtension.equiv_embed ..

private theorem nineteen_fixed (a : MulAut (firstCore 19 false)) :
    a (centralInvolution 19 false) = centralInvolution 19 false := by
  let f : firstCore 19 false ≃* RootTwistedSylow.firstCore :=
    Subgroup.centralizerUpperCentralSeriesEquiv nineteenEquiv 2
  have hx : f (centralInvolution 19 false) = RootTwistedSylow.centralInvolution :=
    Subtype.ext nineteenEquiv_mark
  apply f.injective
  have hf := RootTwistedSylow.centralInvolution_fixed (f.symm.trans (a.trans f))
  rw [← hx] at hf
  change f (a (f.symm (f (centralInvolution 19 false)))) = f (centralInvolution 19 false) at hf
  simpa only [f.symm_apply_apply] using hf

/-- The previously proved split root-twisted certificate covers base action 0. -/
public theorem zero_false_fixed (a : MulAut (firstCore 0 false)) :
    a (centralInvolution 0 false) = centralInvolution 0 false := by
  let e : Model 0 false ≃* Model 19 false :=
    CyclicFourCentralExtension.congr (Core.c ^ (conjugatingPower 19).val) (intertwine 19)
  have he : e (mark 0 false) = mark 19 false := CyclicFourCentralExtension.congr_root_nine ..
  exact fixed_of_marked_equiv e he nineteen_fixed a

end ReeTwo.InvertingModel
