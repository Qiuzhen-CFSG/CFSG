module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourCubicInspection
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.FourSpaceInspection.CommutingRank

/-!
# The completed cubic four-space component comparison

A surjective natural A5 marking identifies the literal conjugation image on
U. The original commuting S3 section and the SQTK rank bound force cubic
rank at most one in the containing component. The checked finite overgroup
inspection then bounds its action by the same A5 image. Quasisimplicity
and the original two-core placement lift action containment to equality of
the component and residual, with normality inside the actual N_G(U).

The finite coverage is reused from `HermitianSourceFieldFourCubicInspection`;
its statement concerns the marked binary deleted-permutation space and is
independent of the Hermitian source. The M22-code Chapter12 consumer
supplies all premises on its unchanged selected pair.
Source: Aschbacher--Smith 8.2.8(1), printed p.719, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.FourSpaceInspection
variable {G : Type*} [Group G]

/-- A surjective five-point action identifies the literal conjugation image. -/
theorem actionImage_marking_of_surjective (R U : Subgroup G)
    (hRU : R ≤ normalizer (U : Set G)) (e : U ≃* FiveModule)
    (r : R →* alternatingGroup (Fin 5)) (hr : Function.Surjective r)
    (he : ∀ (x : R) (u : U),
      (e (U.normalizerMonoidHom (inclusion hRU x) u)).toAdd =
        BinaryPermutation.naturalRepresentation (Fin 5) (r x).val (e u).toAdd) :
    (actionImage R U).map (MulAut.congr e).toMonoidHom = alternatingImage := by
  have ht (x : R) : MulAut.congr e (U.normalizerMonoidHom (inclusion hRU x)) =
      BinaryPermutation.naturalMulAction (Fin 5) (r x).val := by
    apply MulEquiv.ext
    intro v
    obtain ⟨u,rfl⟩ := e.surjective v
    change e (U.normalizerMonoidHom (inclusion hRU x) (e.symm (e u))) = _
    rw [e.symm_apply_apply]
    exact congrArg Multiplicative.ofAdd (he x u)
  rw [actionImage_eq_range R U hRU]
  apply le_antisymm
  · rintro _ ⟨_,⟨x,rfl⟩,rfl⟩
    exact ⟨(r x).val,(r x).property,(ht x).symm⟩
  · rintro _ ⟨s,hs,rfl⟩
    obtain ⟨x,hx⟩ := hr ⟨s,hs⟩
    refine ⟨_,⟨x,rfl⟩,?_⟩
    change MulAut.congr e (U.normalizerMonoidHom (inclusion hRU x)) = _
    rw [ht,hx]

/-- The actual commuting S3 section gives the cubic bound. The complete
finite inspection and the original two-core/Sylow placement then identify
the containing component with the residual, including relative normality. -/
theorem localResidual_eq_and_normal_of_commuting_s3 [Finite G]
    (C : CFSG.Quasithin.GroupClass) (L K U I T : Subgroup G)
    [Group.IsPerfect K] [IsQuasisimple (K ⧸ pCore 2 K)]
    (hSQTK : IsSQTK C (normalizer (U : Set G)))
    (e : U ≃* FiveModule)
    (hmark : (actionImage (localResidual L U) U).map (MulAut.congr e).toMonoidHom =
      alternatingImage)
    (hRK : localResidual L U ≤ K) (hKU : K ≤ normalizer (U : Set G))
    (hNK : normalizer (U : Set G) ≤ normalizer (K : Set G))
    (hQT : K.pCoreIn 2 ≤ T) (hTL : T ≤ normalizer (L : Set G))
    (hTU : T ≤ normalizer (U : Set G))
    (hnon : ¬ localResidual L U ≤ centralizer (U : Set G))
    (hIC : I ≤ centralizer (U : Set G))
    (eI : (I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 3)) :
    primeRank 3 K ≤ 1 ∧ localResidual L U = K ∧
      ((localResidual L U).subgroupOf (normalizer (U : Set G))).Normal := by
  have hr := containingComponent_threeRank_le_one C L K U I
    hSQTK hRK hKU hNK hnon hIC eI
  have heq := localResidual_eq_of_quasisimple_actionImage L K U T hRK hKU
    hQT hTL hTU hnon (actionImage_le_of_inspection L K U
      MatrixInspection.HermitianCoverage.cubicOvergroupInspection e hmark hRK hKU hr)
  exact ⟨hr,heq,heq ▸ normal_subgroupOf_of_le_normalizer hNK⟩

end CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.FourSpaceInspection
