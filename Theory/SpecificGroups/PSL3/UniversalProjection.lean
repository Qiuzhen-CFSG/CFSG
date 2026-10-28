module

public import Theory.SpecificGroups.PSL3.UniversalProjection.LiftRelations
public import Theory.SpecificGroups.PSL3.UniversalProjection.Faithfulness

/-!
# Universality of the ordinary degree-three projection

Faithfulness of the Steinberg presentation and the lifted Steinberg relations
assemble the universal property of the literal `SL₃(F) → PSL₃(F)` projection.
For field orders different from two and four, the imported finite-field
calculations discharge both premises. The conclusion includes the exact
lifting square, surjectivity and uniqueness. The unique homomorphism also
exists through arbitrary central extensions, without finiteness or
perfectness of the extension group. The conditional assembly interfaces
remain available separately.

The source is Aschbacher–Smith I.1.3(2), I.1.4(2), printed pp.407–408,
citing GLS98 §6.1 and Steinberg, *Lectures on Chevalley Groups*, §§6–7.
The exclusions `q ≠ 2, 4` are source parameter restrictions; they are not
used to turn a center calculation into a universality proof.
-/

@[expose] public section

namespace Matrix.PSL3.UniversalProjection

open Theory.GroupTheory
open Theory.SpecificGroups.LinearHigher
open Matrix.PSL3
open scoped MatrixGroups

universe u w

variable {F : Type u} [Field F] [Finite F]

/- The input is quantified over the exact target type and covering used by the
Covering.IsUniversal definition. This avoids weakening a central extension to
an unmarked quotient or silently changing the source convention. -/
theorem projection_isUniversal_of_source_inputs
    (hinj : Function.Injective (matrixMap (n := 3) (F := F)))
    (hall : ∀ (M : Type w) [Group M] [Finite M] [IsQuasisimple M]
      (g : Covering M PSL(3, F)), Relations (rootLift g.toMonoidHom g.surjective)) :
    Covering.IsUniversal.{u, u, w} (projectionCovering F) := by
  intro M _ _ _ g
  obtain ⟨s, hs, hsu⟩ :=
    existsUnique_lift_of_faithful_of_relations hinj g.toMonoidHom g.surjective
      g.ker_le_center (hall M g)
  let h : Covering SL(3, F) M := {
    toMonoidHom := s
    surjective := by
      exact projection_lift_surjective F g.toMonoidHom g.ker_le_center s hs
  }
  refine ⟨h, ?_, ?_⟩
  · apply Covering.ext
    intro x
    exact congrArg (fun k : SL(3, F) →* PSL(3, F) => k x) hs
  · intro k hk
    apply Covering.ext
    intro x
    have hkfac : g.toMonoidHom.comp k.toMonoidHom = projection F := by
      have hk' := congrArg (fun z : Covering SL(3, F) PSL(3, F) => z.toMonoidHom) hk
      exact hk'
    have hks : k.toMonoidHom = s := hsu k.toMonoidHom hkfac
    exact congrArg (fun z : SL(3, F) →* M => z x) hks

/-- At ordinary field parameters, only presentation faithfulness remains:
the lifted relations in every finite quasisimple covering are proved. -/
theorem projection_isUniversal_of_faithful
    (h2 : Nat.card F ≠ 2) (h4 : Nat.card F ≠ 4)
    (hinj : Function.Injective (matrixMap (n := 3) (F := F))) :
    Covering.IsUniversal.{u, u, w} (projectionCovering F) := by
  apply projection_isUniversal_of_source_inputs hinj
  intro M _ _ _ g
  exact covering_rootLift_relations h2 h4 g

/-- The unique lift of the literal scalar projection through any central
extension, with both the presentation and root relations discharged. -/
theorem existsUnique_projection_lift {E : Type w} [Group E]
    (f : E →* PSL(3, F)) (hf : Function.Surjective f)
    (hc : f.ker ≤ Subgroup.center E)
    (h2 : Nat.card F ≠ 2) (h4 : Nat.card F ≠ 4) :
    ∃! s : SL(3, F) →* E, f.comp s = projection F :=
  existsUnique_lift_of_faithful f hf hc h2 h4 (matrixMap_injective h2 h4)

/-- At every ordinary finite-field parameter, the actual SL₃ → PSL₃
projection is the universal finite quasisimple covering. -/
theorem projection_isUniversal (h2 : Nat.card F ≠ 2) (h4 : Nat.card F ≠ 4) :
    Covering.IsUniversal.{u, u, w} (projectionCovering F) :=
  projection_isUniversal_of_faithful h2 h4 (matrixMap_injective h2 h4)

end Matrix.PSL3.UniversalProjection
