module

public import Theory.SpecificGroups.PSp4Three.IrreducibleOvergroups.TrivialTwoCore.NormalizerAction.Comparison

/-!
# A faithful six-point action of the projective quadratic normalizer

The actual matrix normalizer acts on the ten extension-field lines. Its image
lies in the faithful complementary-triple action of the six-point symmetric
group, so that action pulls back to six points. Its kernel is precisely the
ambient symplectic center. Descending along the restriction of the actual
central quotient therefore gives a faithful action of
`projectiveQuadraticNormalizer` on `Fin 6`.

The commuting matrix comparison, conjugation coset, and exact kernel are proved
in the imported descendants. No normalizer-shape hypothesis or order-based
recognition is assumed. This supplies the normalizer action used in the
quadratic-extension branch; coverage of maximal subgroups remains a separate
statement of the assembly owner.

Source application: Aschbacher–Smith, Theorem 0.1.2(4), condition K,
printed pp.4/482 of `refs/quasithin.pdf`. The exceptional `PSL₂(9)`–`A₆`
comparison and its ATLAS attribution are recorded in `Comparison`.
-/

@[expose] public section

noncomputable section
namespace Matrix.PSp4Three.TrivialTwoCore.NormalizerAction
open Atlas.Comparisons.Exceptional

/-- Pull back the faithful complementary-triple action along its actual image. -/
def sixPointAction : quadraticNormalizer →* Equiv.Perm (Fin 6) :=
  (MonoidHom.ofInjective symmetricAction_injective).symm.toMonoidHom.comp
    (tenPointAction.codRestrict TriplePartitions.symmetricAction.range
      tenPointAction_mem_symmetric_range)

theorem sixPointAction_coherence (g : quadraticNormalizer) :
    TriplePartitions.symmetricAction (sixPointAction g) = tenPointAction g :=
  MonoidHom.apply_ofInjective_symm symmetricAction_injective _

/-- Restriction of the ambient central quotient to the explicit normalizer. -/
def normalizerProjection : quadraticNormalizer →* projectiveQuadraticNormalizer :=
  projection.subgroupMap quadraticNormalizer

theorem normalizerProjection_surjective : Function.Surjective normalizerProjection :=
  projection.subgroupMap_surjective quadraticNormalizer

private theorem normalizerProjection_ker_le : normalizerProjection.ker ≤ sixPointAction.ker := by
  intro g hg
  have hcent : g.val ∈ Subgroup.center (Sp 2 (ZMod 3)) := by
    rw [← projection_kernel]
    exact congrArg Subtype.val (show normalizerProjection g = 1 from hg)
  change sixPointAction g = 1
  apply symmetricAction_injective
  rw [sixPointAction_coherence, (tenPointAction_eq_one_iff g).mpr hcent, map_one]

/-- The six-point action on the actual projective image of the normalizer. -/
def projectiveSixPointAction : projectiveQuadraticNormalizer →* Equiv.Perm (Fin 6) :=
  normalizerProjection.liftOfSurjective normalizerProjection_surjective
    ⟨sixPointAction, by exact normalizerProjection_ker_le⟩

@[simp] theorem projectiveSixPointAction_projection (g : quadraticNormalizer) :
    projectiveSixPointAction (normalizerProjection g) = sixPointAction g := by
  exact normalizerProjection.liftOfRightInverse_comp_apply
    (Function.surjInv normalizerProjection_surjective)
    (Function.rightInverse_surjInv normalizerProjection_surjective)
    ⟨sixPointAction, normalizerProjection_ker_le⟩ g

theorem projectiveSixPointAction_injective : Function.Injective projectiveSixPointAction := by
  apply projectiveSixPointAction.ker_eq_bot_iff.mp
  apply bot_unique
  intro g hg
  change g = 1
  obtain ⟨n, rfl⟩ := normalizerProjection_surjective g
  have hs : sixPointAction n = 1 := by
    simpa only [projectiveSixPointAction_projection] using
      (show projectiveSixPointAction (normalizerProjection n) = 1 from hg)
  have ht : tenPointAction n = 1 := by
    rw [← sixPointAction_coherence, hs, map_one]
  apply Subtype.ext
  exact (QuotientGroup.eq_one_iff n.val).mpr ((tenPointAction_eq_one_iff n).mp ht)

end Matrix.PSp4Three.TrivialTwoCore.NormalizerAction

namespace Matrix.PSp4Three.TrivialTwoCore

/-- The explicit projective quadratic normalizer has a faithful six-point action. -/
theorem exists_faithful_sixPointAction :
    ∃ f : projectiveQuadraticNormalizer →* Equiv.Perm (Fin 6), Function.Injective f :=
  ⟨NormalizerAction.projectiveSixPointAction, NormalizerAction.projectiveSixPointAction_injective⟩

end Matrix.PSp4Three.TrivialTwoCore
