module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourCubicInspection
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourLevi
public import Theory.GroupTheory.SylowNormalizerOvergroup
public import Theory.Representation.OrthogonalFourMinusFirstCohomology.AlternatingFive.Intertwining
/-!
# The cubic comparison on the original Hermitian four-space

The actual Hermitian SL₂(4) action transports to the deleted-permutation A₅
module using the five singular vectors. The completed finite inspection then
bounds every cubic-rank-one overgroup of that marked action by its S₅
normalizer; perfectness removes the sign quotient. The source Sylow absorbs
O₂(K), and quasisimplicity lifts equality of action images to R=K without
removing the full central kernel by assumption.

The Chapter 12 consumer discharges the marking and rank bound on the same
selected U, R and K. Source: Aschbacher–Smith H.4.6(2) and 8.2.8(1), printed
pp.382,719, refs/quasithin.pdf.
-/
public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterE Normalizer.SmallOvergroups
set_option backward.isDefEq.respectTransparency false
/-- The literal Hermitian SL₂(4) marking on U is the deleted-permutation A₅
marking required by the finite overgroup comparison. -/
theorem hermitian_fixed_action_marking
    {G : Type*} [Group G] (R U : Subgroup G) [IsElementaryAbelian 2 U]
    (b : Additive U ≃ₗ[ZMod 2] OrthogonalFourMinus.FiniteModel.Space 1)
    (f : SL(2,E 1) →* Automizer U)
    (hrange : f.range = inducedAutomizer U R)
    (he : ∀ a u, b (automizerRepresentation U (f a) u) =
      OrthogonalFourMinus.FiniteModel.action 1 a (b u)) :
    ∃ e : U ≃* FourSpaceInspection.FiveModule,
      (actionImage R U).map (MulAut.congr e).toMonoidHom =
        FourSpaceInspection.alternatingImage := by
  let c := b.trans OrthogonalFourMinus.AlternatingFive.moduleEquiv
  let e : U ≃* FourSpaceInspection.FiveModule := c.toAddEquiv.toMultiplicative
  have ht (a : SL(2,E 1)) :
      MulAut.congr e (f a).val = BinaryPermutation.naturalMulAction (Fin 5)
        (OrthogonalFourMinus.AlternatingFive.groupEquiv a).val := by
    apply MulEquiv.ext
    intro v
    obtain ⟨u,rfl⟩ := e.surjective v
    change e ((f a).val (e.symm (e u))) = _
    rw [e.symm_apply_apply]
    change c (automizerRepresentation U (f a) (Additive.ofMul u)) =
      BinaryPermutation.naturalRepresentation (Fin 5)
        (OrthogonalFourMinus.AlternatingFive.groupEquiv a).val (c (Additive.ofMul u))
    change OrthogonalFourMinus.AlternatingFive.moduleEquiv
      (b (automizerRepresentation U (f a) (Additive.ofMul u))) = _
    rw [he,OrthogonalFourMinus.AlternatingFive.intertwines]
    rfl
  have him : actionImage R U = (inducedAutomizer U R).map (Automizer U).subtype := by
    rw [inducedAutomizer,map_map]
    rfl
  refine ⟨e,?_⟩
  rw [him,←hrange,map_map]
  apply le_antisymm
  · rintro _ ⟨_,⟨a,rfl⟩,rfl⟩
    exact ⟨_,(OrthogonalFourMinus.AlternatingFive.groupEquiv a).property,(ht a).symm⟩
  · rintro _ ⟨s,hs,rfl⟩
    obtain ⟨a,ha⟩ := OrthogonalFourMinus.AlternatingFive.groupEquiv.surjective ⟨s,hs⟩
    refine ⟨f a,⟨a,rfl⟩,?_⟩
    change MulAut.congr e (f a).val = _
    rw [ht,ha]

/-- The cubic source component equals the original residual. The comparison
uses the actual module marking, rank bound and original Sylow; its full
central kernel and two-core are retained throughout the lifting. -/
theorem cubic_component_eq
    {G : Type*} [Group G] [Finite G] (L K U : Subgroup G) (T : Sylow 2 G)
    [IsElementaryAbelian 2 U] [Group.IsPerfect K] [IsQuasisimple (K ⧸ pCore 2 K)]
    (hRK : Normalizer.localResidual L U ≤ K)
    (hKU : K ≤ normalizer (U : Set G))
    (hNK : normalizer (U : Set G) ≤ normalizer (K : Set G))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hnon : ¬ Normalizer.localResidual L U ≤ centralizer (U : Set G))
    (hrank : primeRank 3 K ≤ 1)
    (b : Additive U ≃ₗ[ZMod 2] OrthogonalFourMinus.FiniteModel.Space 1)
    (f : SL(2,E 1) →* Automizer U)
    (hrange : f.range = inducedAutomizer U (Normalizer.localResidual L U))
    (he : ∀ a u, b (automizerRepresentation U (f a) u) =
      OrthogonalFourMinus.FiniteModel.action 1 a (b u)) :
    Normalizer.localResidual L U = K := by
  obtain ⟨e,hmark⟩ := hermitian_fixed_action_marking _ U b f hrange he
  have hQT : K.pCoreIn 2 ≤ (T : Subgroup G) :=
    (isPGroup_pCoreIn 2 K).le_sylow_of_normalized T
      ((hTU.trans hNK).trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K)))
  exact localResidual_eq_of_quasisimple_actionImage L K U T hRK hKU hQT hTL hTU hnon
    (FourSpaceInspection.actionImage_le_of_inspection L K U
      FourSpaceInspection.MatrixInspection.HermitianCoverage.cubicOvergroupInspection
      e hmark hRK hKU hrank)

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
