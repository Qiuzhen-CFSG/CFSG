module

public import CFSG.Quasithin.ChapterD.Section03.SourceInternal
public import Theory.GroupTheory.ReducedNormal.RepresentationEmbedding
public import Theory.GroupTheory.ReducedNormal.ActionCore
public import Theory.GroupTheory.PCoreActionSplitting
public import Theory.GroupTheory.ReducedNormal.AmbientInclusion

/-!
# Applying D.3.3 to the original reduced-module seed

Embed the specified Irr⁺ seed from R₂(X T) into R₂(M) using A.1.11.
The original actor remains Irr⁺ under this literal inclusion. Reducedness
of R₂(M) supplies the trivial two-core of the normal actor image, and
the original two-core fixes every seed in R₂(X T). Injective core
transport therefore supplies the exact seed invariance in M.

Both source structural alternatives are retained in the actor hypothesis;
the resulting faithful action is constructed by D.3.3. Its seed is proved
to be exactly the same ambient subgroup as the original seed.

Source: Aschbacher–Smith, Lemma 3.2.2, combined manuscript of
1 March 2004, printed p.579.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter3.Section02
open ChapterD.Section03
universe u
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
  (T : Sylow 2 G) (X M : Subgroup G) (hXM : X ≤ M) (hTM : (T : Subgroup G) ≤ M)
  [(X.subgroupOf M).Normal]

/-- The genuine internal hypotheses for the image of the original seed.
No action-image or seed-invariance conclusion is assumed. -/
theorem internalHypotheses_of_reduced_seed
    (hM : IsSQTK K M)
    (hX : pResidual 2 (X.subgroupOf M) = ⊤)
    (hc : InternalActorCases (T.subtype hTM) (X.subgroupOf M)
      (by rw [normalizer_eq_top]; exact le_top))
    (hR : (ReducedNormal.ModuleGroup (X ⊔ (T : Subgroup G))).map
        (X ⊔ (T : Subgroup G)).subtype ≤
      (ReducedNormal.ModuleGroup M).map M.subtype)
    (I : Submodule (ZMod 2)
      (Additive (ReducedNormal.ModuleGroup (X ⊔ (T : Subgroup G)))))
    (hI : IsIrrPlus (ReducedNormal.representation (X ⊔ (T : Subgroup G)))
      (X.subgroupOf (X ⊔ (T : Subgroup G))) I) :
    InternalModuleHypotheses K (ReducedNormal.representation M) (T.subtype hTM)
      (X.subgroupOf M)
      (I.map (ReducedNormal.moduleInclusion (sup_le hXM hTM) hR)) := by
  let H := X ⊔ (T : Subgroup G)
  let f : H →* M := inclusion (sup_le hXM hTM)
  have hr : f.range = X.subgroupOf M ⊔ (T : Subgroup G).subgroupOf M := by
    rw [← subgroupOf_sup hXM hTM]
    ext m
    constructor
    · rintro ⟨x, rfl⟩
      exact x.property
    · intro hm
      exact ⟨⟨m, hm⟩, rfl⟩
  refine ⟨hM, inferInstance, inferInstance, hX, hc,
    ReducedNormal.normal_actor_representation_twoCore_eq_bot M (X.subgroupOf M),
    ReducedNormal.isIrrPlus_ambientInclusion (sup_le hXM hTM) hR le_sup_left hI, ?_⟩
  have hi := map_le_subspaceStabilizer_embedding (ReducedNormal.representation H)
    (ReducedNormal.representation M) f
    (ReducedNormal.moduleInclusion (sup_le hXM hTM) hR)
    (ReducedNormal.moduleInclusion_equivariant (sup_le hXM hTM) hR)
    (ReducedNormal.representation_twoCore_stabilizes H I)
  rw [← pCoreIn_range_of_injective 2 f (inclusion_injective (sup_le hXM hTM)), hr] at hi
  exact hi

omit [Finite G] [(X.subgroupOf M).Normal] in
/-- The original seed in the actual ambient group is unchanged by the
inclusion used to construct the internal action. -/
theorem reduced_seed_ambient_identity
    (hR : (ReducedNormal.ModuleGroup (X ⊔ (T : Subgroup G))).map
        (X ⊔ (T : Subgroup G)).subtype ≤
      (ReducedNormal.ModuleGroup M).map M.subtype)
    (I : Submodule (ZMod 2)
      (Additive (ReducedNormal.ModuleGroup (X ⊔ (T : Subgroup G))))) :
    ReducedNormal.subspaceImage M
        (I.map (ReducedNormal.moduleInclusion (sup_le hXM hTM) hR)) =
      ReducedNormal.subspaceImage (X ⊔ (T : Subgroup G)) I :=
  ReducedNormal.subspaceImage_moduleInclusion (sup_le hXM hTM) hR I

include hXM

/-- The simple QTKE and maximal-local hypotheses discharge A.1.11 and
the SQTK-cover condition for the original seed. Both actor alternatives
are the original structural alternatives inside M. -/
theorem source_reduced_seed_internal
    (hG : IsSimpleQTKE K G) (hM : IsMaximalTwoLocal M)
    (hX : pResidual 2 (X.subgroupOf M) = ⊤)
    (hc : InternalActorCases (T.subtype hTM) (X.subgroupOf M)
      (by rw [normalizer_eq_top]; exact le_top))
    (I : Submodule (ZMod 2)
      (Additive (ReducedNormal.ModuleGroup (X ⊔ (T : Subgroup G)))))
    (hI : IsIrrPlus (ReducedNormal.representation (X ⊔ (T : Subgroup G)))
      (X.subgroupOf (X ⊔ (T : Subgroup G))) I) :
    ∃ J : Submodule (ZMod 2) (Additive (ReducedNormal.ModuleGroup M)),
      ReducedNormal.subspaceImage M J =
        ReducedNormal.subspaceImage (X ⊔ (T : Subgroup G)) I ∧
      InternalModuleHypotheses K (ReducedNormal.representation M) (T.subtype hTM)
        (X.subgroupOf M) J := by
  have hR := reducedPSubgroup_ambient_le T (X ⊔ (T : Subgroup G)) M
    le_sup_right (sup_le hXM hTM) (hG.evenCharacteristic T M hM hTM)
  exact ⟨I.map (ReducedNormal.moduleInclusion (sup_le hXM hTM) hR),
    reduced_seed_ambient_identity T X M hXM hTM hR I,
    internalHypotheses_of_reduced_seed T X M hXM hTM (hG.twoLocal_sqtk hM.1)
      hX hc hR I hI⟩

/-- The D.3.1 assertion of 3.2.2(7) on the actual faithful orbit module,
with the original ambient seed and both actor alternatives retained. -/
theorem source_reduced_seed_faithful_module
    (hG : IsSimpleQTKE K G) (hM : IsMaximalTwoLocal M)
    (hX : pResidual 2 (X.subgroupOf M) = ⊤)
    (hc : InternalActorCases (T.subtype hTM) (X.subgroupOf M)
      (by rw [normalizer_eq_top]; exact le_top))
    (I : Submodule (ZMod 2)
      (Additive (ReducedNormal.ModuleGroup (X ⊔ (T : Subgroup G)))))
    (hI : IsIrrPlus (ReducedNormal.representation (X ⊔ (T : Subgroup G)))
      (X.subgroupOf (X ⊔ (T : Subgroup G))) I) :
    ∃ J : Submodule (ZMod 2) (Additive (ReducedNormal.ModuleGroup M)),
      ReducedNormal.subspaceImage M J =
        ReducedNormal.subspaceImage (X ⊔ (T : Subgroup G)) I ∧
      SourceHypotheses K
        (subspaceImageRepresentation (ReducedNormal.representation M)
          (orbitSpan (ReducedNormal.representation M) ⊤ J))
        ((T.subtype hTM).mapSurjective (invariantActionHom_surjective
          (ReducedNormal.representation M) _ (orbitSpan_invariant _ ⊤ J)))
        (restrictedSubgroup (ReducedNormal.representation M)
          (orbitSpan (ReducedNormal.representation M) ⊤ J) (X.subgroupOf M))
        (J.comap (orbitSpan (ReducedNormal.representation M) ⊤ J).subtype) := by
  obtain ⟨J, hJ, hi⟩ := source_reduced_seed_internal T X M hXM hTM hG hM hX hc I hI
  exact ⟨J, hJ, hi.faithfulOrbit_source⟩

end CFSG.Quasithin.Chapter3.Section02
