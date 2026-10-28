module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SplitSeed
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.Coordinates
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.NaturalMarking.Sylow

/-!
# The split-model source contradictions in an arbitrary S₈ marking

Sylow conjugacy adjusts the permutation marking and the model coordinates
together. The actual source section stays fixed. Thus the cyclic flag
obstructions apply to any marked product of natural modules or any marked
surjection onto the augmentation core, without a Sylow-placement premise.
-/

public noncomputable section
open Subgroup Representation BinaryPermutation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter15.Section03.AbelianAmalgam
open AlternatingSevenSource
open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
universe u v
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {I : Subgroup G} [IsElementaryAbelian 2 (F.UH I)]

/-- The original source excludes two natural copies in any permutation marking. -/
theorem local_double_natural_impossible_of_marking_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1))
    (eH : (I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 8))
    (E : Additive ((F.UH I) ⧸ (F.Vi 1).subgroupOf (F.UH I)) ≃ₗ[ZMod 2]
      (natural (Fin 8) × natural (Fin 8)))
    (hE : ∀ g w, E (a.representation g w) =
      (naturalRepresentation (Fin 8) (eH g) (E w).1,
       naturalRepresentation (Fin 8) (eH g) (E w).2)) : False := by
  let q := QuotientGroup.mk' (pCore 2 I)
  let P := (T.subtype (F.sylow_le_of_mem_Hz hI)).mapSurjective
    (f := q) (QuotientGroup.mk'_surjective _)
  let τ := (naturalRepresentation (Fin 8)).prod (naturalRepresentation (Fin 8))
  obtain ⟨b,hb,⟨m⟩⟩ := NaturalMarking.exists_sylow_marking 2 P treeSylow τ
    (τ.comp eH.toMonoidHom) eH (Representation.Equiv.refl _)
  let E' := E.trans m.symm.toLinearEquiv
  have he' (g) (w) : E' (a.representation g w) = τ (b g) (E' w) := by
    change m.symm (E (a.representation g w)) = _
    rw [hE]
    exact LinearMap.congr_fun (m.symm.isIntertwining' g) (E w)
  have hT : ((T : Subgroup G).subgroupOf I).map (b.toMonoidHom.comp q) = treeGroup := by
    rw [←Subgroup.map_map]
    exact hb
  exact local_double_natural_impossible_at h hI (b.toMonoidHom.comp q) hT
    (localQuotientSection a) E' (fun g w => he' (q g) w)

/-- The original source excludes a core quotient in any permutation marking. -/
theorem local_core_quotient_impossible_of_marking_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1))
    (eH : (I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 8))
    (f : Additive ((F.UH I) ⧸ (F.Vi 1).subgroupOf (F.UH I)) →ₗ[ZMod 2] core (Fin 8))
    (hsur : Function.Surjective f)
    (hf : ∀ g w, f (a.representation g w) = coreRepresentation (Fin 8) (eH g) (f w)) :
    False := by
  let q := QuotientGroup.mk' (pCore 2 I)
  let P := (T.subtype (F.sylow_le_of_mem_Hz hI)).mapSurjective
    (f := q) (QuotientGroup.mk'_surjective _)
  let τ := coreRepresentation (Fin 8)
  obtain ⟨b,hb,⟨m⟩⟩ := NaturalMarking.exists_sylow_marking 2 P treeSylow τ
    (τ.comp eH.toMonoidHom) eH (Representation.Equiv.refl _)
  let f' := m.symm.toLinearMap.comp f
  have hf' (g) (w) : f' (a.representation g w) = τ (b g) (f' w) := by
    change m.symm (f (a.representation g w)) = _
    rw [hf]
    exact LinearMap.congr_fun (m.symm.isIntertwining' g) (f w)
  have hT : ((T : Subgroup G).subgroupOf I).map (b.toMonoidHom.comp q) = treeGroup := by
    rw [←Subgroup.map_map]
    exact hb
  exact local_core_quotient_impossible_at h hI (b.toMonoidHom.comp q) hT
    (localQuotientSection a) f' (m.symm.toLinearEquiv.surjective.comp hsur)
    (fun g w => hf' (q g) w)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource
