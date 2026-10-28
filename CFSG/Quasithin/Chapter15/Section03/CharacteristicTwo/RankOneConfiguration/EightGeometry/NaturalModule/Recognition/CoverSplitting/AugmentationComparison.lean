module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.Models
public import Theory.Representation.BinaryPermutationNaturalCover
public import Theory.Representation.FirstCohomologyDuality.OneDimensionalCover

/-!
# Identifying the nontrivial orthogonal cover with augmentation

Transport the supplied component action along its marked isomorphism with A₈.
The orthogonal-cover record supplies an equivariant surjection with fixed kernel
and a commutator-generated source. The augmentation projection is another such
cover, of dimension seven. Self-duality of the six-dimensional natural module
and I.1.6(1) give a one-dimensional universal-cover kernel. The universal-cover
comparison therefore identifies any cover with nonzero kernel with augmentation.
Transporting the coordinates back gives precisely component equivariance.

This is the covering comparison used in the proof of 15.3.32(1); extension to
the full marked S₈ action and the moving-line obstruction belong to the parent.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), I.1.5–I.1.6(1),
printed p.408 (PDF p.419), and 15.3.32(1), printed pp.1132–1133.
-/

@[expose] public section

open Module Representation Representation.OneCohomology Equiv
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.CoverSplitting

variable {K V : Type*} [Group K] [AddCommGroup V] [Module (ZMod 2) V]

/-- A perfect orthogonal cover with nonzero kernel is the augmentation module
as a module for the marked alternating component. -/
theorem augmentation_coordinates_of_nonzero_kernel [Finite K] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) K V) (e : K ≃* Perm (Fin 8)) (L : Subgroup K)
    (hL : L.map e.toMonoidHom = alternatingGroup (Fin 8))
    (cover : Models.OrthogonalCover ρ L e) (hn : cover.projection.ker ≠ ⊥) :
    ∃ f : V ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 8),
      ∀ (l : L) v, f (ρ l v) = BinaryPermutation.coreRepresentation (Fin 8) (e l) (f v) := by
  let eL : L ≃* alternatingGroup (Fin 8) :=
    (e.subgroupMap L).trans (MulEquiv.subgroupCongr hL)
  have heL (l : L) : (eL l).val = e l := rfl
  have heLi (g : alternatingGroup (Fin 8)) : e (eL.symm g) = g.val :=
    congrArg Subtype.val (eL.apply_symm_apply g)
  let σ : Representation (ZMod 2) (alternatingGroup (Fin 8)) V :=
    (ρ.comp L.subtype).comp eL.symm.toMonoidHom
  let p : σ.IntertwiningMap (BinaryPermutation.alternatingNaturalRepresentation (Fin 8)) :=
    cover.projection.intertwiningMap_of_isIntertwiningMap _ _ (by
      intro g v
      change cover.projection (ρ (eL.symm g) v) =
        BinaryPermutation.naturalRepresentation (Fin 8) g.val (cover.projection v)
      rw [cover.equivariant, heLi])
  have hp : IsCover p := by
    refine ⟨cover.onto, ?_, ?_⟩
    · intro v hv g
      have hv' : v ∈ Representation.BinaryOffender.fixedSpace ρ L := by
        rw [← cover.kernel]
        exact hv
      exact hv' (eL.symm g)
    · have hle : Coinvariants.ker (ρ.comp L.subtype) ≤ Coinvariants.ker σ := by
        apply Submodule.span_le.mpr
        rintro _ ⟨⟨l, v⟩, rfl⟩
        have h := Coinvariants.sub_mem_ker (ρ := σ) (eL l) v
        change ρ (eL.symm (eL l)) v - v ∈ Coinvariants.ker σ at h
        change ρ l v - v ∈ Coinvariants.ker σ
        simpa only [eL.symm_apply_apply] using h
      rw [cover.generated] at hle
      exact top_unique hle
  obtain ⟨f, hf⟩ := equiv_of_cover_of_finrank_dual_H1_eq_one p hp
    (BinaryPermutation.alternatingCoreProjection (Fin 8))
    BinaryPermutation.alternatingEight_coreProjection_isCover
    BinaryPermutation.alternatingEight_natural_dual_finrank_H1 hn (by
      rw [BinaryPermutation.finrank_core,
        BinaryPermutation.finrank_natural_even (Fin 8) (by decide)]
      decide)
  refine ⟨f, ?_⟩
  intro l v
  have h := hf (eL l) v
  change f (ρ (eL.symm (eL l)) v) =
    BinaryPermutation.coreRepresentation (Fin 8) (eL l).val (f v) at h
  simpa only [eL.symm_apply_apply, heL] using h

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.CoverSplitting
