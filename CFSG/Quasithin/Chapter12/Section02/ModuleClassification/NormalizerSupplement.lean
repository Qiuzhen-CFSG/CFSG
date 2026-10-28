module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.FFQuasisimple
public import Theory.Representation.BinaryOffender.QuasisimpleNormalizer
public import Theory.Representation.BinaryOffender.IrrPlusFitting

/-!
# Complete B.5.1 from a full-linear-normalizer offender

Adjoin an offender to the actual component image on the chosen space.
Irr⁺ kills the two-core of this faithful supplement. Its quotient by the
component is a two-group, so complete B.5.1 applies to the literal offender
subgroup. The original L/O₂(L) projection and its action are retained.
This supplies the classification input; comparison with the seven source
rows still requires the earlier non-FF and model-exclusion theorems.

Source: Aschbacher--Smith 3.2.8 and 12.2.2, pp.582 and 795,
using B.5.1, pp.99--103.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open Representation.BinaryOffender.QuasisimpleNormalizer
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ModuleClassification
universe u
variable {P W : Type u} [Group P] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) P W)

private theorem supplement_irrPlus
    (hi : IsIrrPlus σ ⊤ ⊤) (A : Subgroup (linearNormalizer σ)) :
    IsIrrPlus (linearAction (supplement σ A)) (component σ A) ⊤ := by
  apply hi.of_intertwining σ (linearAction (supplement σ A))
    ((projection σ A).comp (topEquiv (G := P)).toMonoidHom)
    ((projection_surjective σ A).comp (topEquiv (G := P)).surjective)
    LinearMap.id (fun _ _ he => he)
  · intro l v
    rfl
  · exact Submodule.map_id _

private theorem supplement_core [Module.Finite (ZMod 2) W] [IsQuasisimple P]
    (hf : Function.Injective σ) (hi : IsIrrPlus σ ⊤ ⊤)
    (A : Subgroup (linearNormalizer σ)) : pCore 2 (supplement σ A) = ⊥ := by
  have hk : σ.ker ≤ center P := by
    rw [(MonoidHom.ker_eq_bot_iff σ).mpr hf]
    exact bot_le
  let := component_quasisimple σ hk A
  let := component_normal σ A
  let := supplement_finite σ A
  have hs : componentLayer (component σ A) = ⊤ := by
    apply top_unique
    exact le_sSup (show IsComponent (component σ A) ⊤ from
      ⟨Subgroup.IsSubnormal.top,IsQuasisimple.of_mulEquiv topEquiv.symm⟩)
  have hfix := IsIrrPlus.le_fixedSpace_of_twoGroup_centralizes
    (linearAction (supplement σ A)) (supplement_irrPlus σ hi A)
    pCore_isPGroup (twoCore_centralizes_of_normal_layer_or_odd (component σ A) (Or.inl hs))
    (le_subspaceStabilizer _ ⊤ (fun _ _ _ _ => Submodule.mem_top))
  apply bot_unique
  intro g hg
  apply mem_bot.mpr
  apply linearAction_injective _
  apply LinearMap.ext
  intro v
  simpa only [map_one, Module.End.one_apply, MonoidHom.comp_apply,
    Subgroup.subtype_apply] using hfix Submodule.mem_top ⟨g,hg⟩

private theorem supplement_quotient_two
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryAbelian 2 A) :
    let := component_normal σ A
    IsPGroup 2 (supplement σ A ⧸ component σ A) := by
  let := component_normal σ A
  let := hA
  let B := A.map (linearNormalizer σ).subtype
  have hb : IsPGroup 2 (B.subgroupOf (supplement σ A)) :=
    (IsElementaryAbelian.isPGroup (p := 2) (G := A)).map _ |>.comap_subtype
  exact quotient_isPGroup_of_sup_eq_top (B.subgroupOf (supplement σ A)) (component σ A) hb
    (by rw [sup_comm]; exact (codisjoint_subgroupOf_sup (actionImage σ) B).eq_top)

private def supplement_projectionEquiv (hf : Function.Injective σ)
    (A : Subgroup (linearNormalizer σ)) : P ≃* component σ A :=
  MulEquiv.ofBijective (projection σ A)
    ⟨fun _ _ he => hf (congrArg (fun k : component σ A =>
      linearAction (supplement σ A) k) he),projection_surjective σ A⟩

/-- All six source clauses on the actual offender subgroup of the supplement.
The abbreviation fixes its exact action and instances before application
at a concrete chosen space. -/
@[expose] def NormalizerConclusion (A : Subgroup (linearNormalizer σ)) : Prop :=
  component σ A ≤ offenderSubgroup (linearAction (supplement σ A)) ∧
    Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      ((linearAction (supplement σ A)).comp
        (offenderSubgroup (linearAction (supplement σ A))).subtype)
      ((component σ A).subgroupOf (offenderSubgroup (linearAction (supplement σ A)))))

/-- Complete B.5.1 applies to an offender supplement of a faithful Irr⁺
quasisimple action, without assuming that the offender lies in that actor. -/
theorem normalizer_source_of_irrPlus [Finite P] [Module.Finite (ZMod 2) W]
    [IsQuasisimple P] (hf : Function.Injective σ)
    (hi : IsIrrPlus σ ⊤ ⊤) (hsq : IsSQTK KnownSimple.IsKnownSimple P)
    (A : Subgroup (linearNormalizer σ))
    (hA : IsOffender (normalizerRepresentation σ) A) :
    NormalizerConclusion σ A := by
  have hk : σ.ker ≤ center P := by
    rw [(MonoidHom.ker_eq_bot_iff σ).mpr hf]
    exact bot_le
  let := component_quasisimple σ hk A
  let := component_normal σ A
  let := supplement_finite σ A
  have hsqK : IsSQTK KnownSimple.IsKnownSimple (component σ A) :=
    (IsSQTK.equiv (supplement_projectionEquiv σ hf A)).mp hsq
  exact ChapterB.QuasisimpleSource.SourceCompletion.ff_quasisimple_source_conclusion
    (linearAction (supplement σ A)) (component σ A)
    (supplement_quotient_two σ A hA.1.2) (supplement_core σ hf hi A)
    hsqK (linearAction_injective _) (supplement_ff σ A hA)

end CFSG.Quasithin.Chapter12.Section02.ModuleClassification
