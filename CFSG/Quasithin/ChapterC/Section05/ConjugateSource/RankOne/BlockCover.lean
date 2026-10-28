module

public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.Representation.FirstCohomologyDuality
public import Theory.Representation.ElementaryAbelianAction.Commutator
public import Theory.GroupTheory.PResidual.SubnormalCoreAction

/-!
# The intrinsic covering module of a short group

The elementary abelian group U = [O₂(L),L] carries literal conjugation.
Its centrality in O₂(L) factors that action through L/O₂(L), and the
specified BlockModuleModel transports the quotient action to the model actor.
The resulting projection has kernel C_U(L). Two-perfection gives [U,L] = U
by coprime commutator idempotence, so this projection is a genuine covering
module in the sense of I.1.5.

The construction uses only the actual short-group hypotheses and an
equivariant model; it imposes no condition on the size of the central layer.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.7 and
C.1.12–13, printed pp.123–125, and I.1.5, printed p.408.
-/

@[expose] public section

open scoped IsMulCommutative
open Subgroup Representation
open CFSG.Quasithin.ChapterC
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.IntrinsicCover

variable {L A V : Type*} [Group L] [Group A] [AddCommGroup V]
variable {ρ : A →* MulAut (Multiplicative V)}

/-- The actual map from the short group onto its prescribed quotient actor. -/
noncomputable def actorMap (m : BlockModuleModel L ρ) : L →* A :=
  m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))

/-- Every model actor comes from an element of the short group. -/
theorem actorMap_surjective (m : BlockModuleModel L ρ) : Function.Surjective (actorMap m) :=
  m.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _)

/-- Conjugation on U, factored through the actual core quotient. -/
noncomputable def coverAut (h : IsShort L) (m : BlockModuleModel L ρ) :
    A →* MulAut (blockU L) := by
  let c : L →* MulAut (blockU L) := MulAut.conjNormal
  have hc : pCore 2 L ≤ c.ker := by
    intro l hl
    apply MonoidHom.mem_ker.mpr
    ext w
    change l * (w : L) * l⁻¹ = (w : L)
    rw [mem_centralizer_iff.mp (h.central w.property) l hl, mul_inv_cancel_right]
  exact (QuotientGroup.lift (pCore 2 L) c hc).comp m.quotientIso.symm.toMonoidHom

/-- The factored automorphism acts by literal conjugation. -/
theorem coverAut_apply (h : IsShort L) (m : BlockModuleModel L ρ)
    (l : L) (w : blockU L) : coverAut h m (actorMap m l) w = blockConjugate L l w := by
  unfold coverAut actorMap
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, m.quotientIso.symm_apply_apply]
  rfl

variable [IsElementaryAbelian 2 (blockU L)]

/-- The binary representation on the full elementary commutator layer. -/
noncomputable def action (h : IsShort L) (m : BlockModuleModel L ρ) :
    Representation (ZMod 2) A (Additive (blockU L)) where
  toFun g := (coverAut h m g).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext
    intro w
    change Additive.ofMul (coverAut h m 1 w.toMul) = w
    rw [map_one]
    rfl
  map_mul' a b := by
    apply LinearMap.ext
    intro w
    change Additive.ofMul (coverAut h m (a * b) w.toMul) = _
    rw [map_mul]
    rfl

/-- The representation retains the original conjugation formula. -/
theorem action_apply (h : IsShort L) (m : BlockModuleModel L ρ)
    (l : L) (w : Additive (blockU L)) :
    action h m (actorMap m l) w = Additive.ofMul (blockConjugate L l w.toMul) :=
  congrArg Additive.ofMul (coverAut_apply h m l w.toMul)

variable [Module (ZMod 2) V]

/-- The actual quotient by C_U(L), followed by the specified module isomorphism. -/
noncomputable def projectionLinear (m : BlockModuleModel L ρ) :
    Additive (blockU L) →ₗ[ZMod 2] V :=
  (m.moduleIso.toMonoidHom.comp (QuotientGroup.mk' (blockFixed L))).toAdditiveLeft.toZModLinearMap 2

/-- The quotient projection intertwines the full action with the model action. -/
noncomputable def projection (h : IsShort L) (m : BlockModuleModel L ρ)
    (π : Representation (ZMod 2) A V)
    (hρ : ∀ g v, Multiplicative.toAdd (ρ g v) = π g (Multiplicative.toAdd v)) :
    (action h m).IntertwiningMap π :=
  { toLinearMap := projectionLinear m
    isIntertwining' g := by
      apply LinearMap.ext
      intro w
      obtain ⟨l, rfl⟩ := actorMap_surjective m g
      simp only [LinearMap.comp_apply]
      rw [action_apply]
      change Multiplicative.toAdd (m.moduleIso (QuotientGroup.mk' _ (blockConjugate L l w.toMul))) = _
      rw [m.intertwining]
      exact hρ (actorMap m l) (m.moduleIso (QuotientGroup.mk' _ w.toMul)) }

/-- Every vector of the model quotient has a lift in U. -/
theorem projection_surjective (h : IsShort L) (m : BlockModuleModel L ρ)
    (π : Representation (ZMod 2) A V)
    (hρ : ∀ g v, Multiplicative.toAdd (ρ g v) = π g (Multiplicative.toAdd v)) :
    Function.Surjective (projection h m π hρ) := by
  intro v
  obtain ⟨w, hw⟩ :=
    (m.moduleIso.surjective.comp (QuotientGroup.mk'_surjective (blockFixed L)))
      (Multiplicative.ofAdd v)
  exact ⟨Additive.ofMul w, congrArg Multiplicative.toAdd hw⟩

/-- The kernel is precisely the original central layer C_U(L). -/
theorem projection_kernel (m : BlockModuleModel L ρ) (w : Additive (blockU L)) :
    projectionLinear m w = 0 ↔ w.toMul ∈ blockFixed L := by
  change m.moduleIso (QuotientGroup.mk' (blockFixed L) w.toMul) = 1 ↔ _
  rw [map_eq_one_iff _ m.moduleIso.injective]
  exact QuotientGroup.eq_one_iff w.toMul

/-- Two-perfection makes the actual central extension a commutator-generated cover. -/
theorem projection_isCover (h : IsShort L) (m : BlockModuleModel L ρ)
    (π : Representation (ZMod 2) A V)
    (hρ : ∀ g v, Multiplicative.toAdd (ρ g v) = π g (Multiplicative.toAdd v)) :
    OneCohomology.IsCover (projection h m π hρ) := by
  refine ⟨projection_surjective h m π hρ, ?_, ?_⟩
  · intro w hw g
    obtain ⟨l, rfl⟩ := actorMap_surjective m g
    rw [action_apply]
    apply Additive.ofMul.injective
    apply Subtype.ext
    have hwc : (w.toMul : L) ∈ center L := (projection_kernel m w).mp hw
    change l * (w.toMul : L) * l⁻¹ = (w.toMul : L)
    rw [Subgroup.mem_center_iff.mp hwc l, mul_inv_cancel_right]
  · apply coinvariants_ker_eq_top_of_commutator_eq (blockU L) (action h m) (actorMap m)
      (fun l w => congrArg (fun x : Additive (blockU L) => (x.toMul : L)) (action_apply h m l w))
    let := h.finite
    exact Subgroup.commutator_isPPerfect_idempotent (⊤ : Subgroup L) (pCore 2 L)
      (h.twoPerfect.of_surjective (Subgroup.topEquiv (G := L)).symm.toMonoidHom
        (Subgroup.topEquiv (G := L)).symm.surjective)
      pCore_isPGroup (by rw [Subgroup.normalizer_eq_top])
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.IntrinsicCover

end
