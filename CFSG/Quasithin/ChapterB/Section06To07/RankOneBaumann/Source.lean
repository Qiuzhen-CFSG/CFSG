module
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.Dimensions
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.FrattiniSource
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.SL2Geometry
public import Theory.GroupTheory.SylowNormalRestriction
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents

/-!
# The natural SL₂ Baumann Sylow theorem

The genuine marked natural quotient determines the Thompson and Baumann
images, and the actual residual supplies two generating conjugates. Exact
fixed codimensions and the source Frattini theorem discharge every clause
of B.2.18. Its alpha decomposition then lifts the Sylow image through the
original two-closed centralizer, retaining its possible odd Frattini kernel.
The natural marker is the single-factor input supplied by B.6.9; neither
splitting of U nor any Sylow or action conclusion is an input.
Source: Aschbacher–Smith B.6.10, printed p.117, and E.2.3(2), pp.216–217.
-/

open Subgroup Stellmacher Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB.RankOneBaumann
open BaumannArgument
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]
  [Algebra (ZMod 2) F]
local notation "D" => Matrix.SpecialLinearGroup (Fin 2) F
local notation "N" => SL2NaturalOffenders.NoStrong.natural (F := F)

public theorem natural_baumann_sylow_and_alpha
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* D) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (f : Additive U →ₗ[ZMod 2] (Fin 2 → F)) (hf : Function.Surjective f)
    (he : ∀ g v, f (NormalElementaryQuotient.representation U q hq hker g v) = N g (f v))
    (hk : f.ker = BinaryOffender.fixedSpace
      (NormalElementaryQuotient.representation U q hq hker) ((pResidual 2 G).map q)) :
    Chapter1.IsSylowIn 2 (baumann (T : Subgroup G))
      (pResidual 2 G ⊔ baumann (T : Subgroup G)) ∧
      thompsonAlpha (T : Subgroup G) =
        (thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)) ⊔
          (U ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) := by
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  have hUT : U ≤ T := hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal T)
  obtain ⟨hJq,hBq⟩ := thompson_baumann_images_of_natural_quotient T U q hq hker hUT hJ f hf he
  obtain ⟨g,hg,hgen⟩ := exists_residual_conjugate_thompson_images_sup_eq_top T q hq hJq
  have hgenJ : (pResidual 2 G).map q ≤
      (elementaryAbelianMaxJ (T : Subgroup G)).map q ⊔
      ((elementaryAbelianMaxJ (T : Subgroup G)).map (MulAut.conj g).toMonoidHom).map q := hgen.symm ▸ le_top
  have hcod : 2 * fixedCodim U (elementaryAbelianMaxJ (T : Subgroup G)) ≤
      fixedCodim U (pResidual 2 G) := by
    rw [thompson_fixedCodim_of_natural_quotient T U q hq hker hUT hJ f hf he,
      residual_fixedCodim_of_natural_kernel U q hq hker f hf hk]
  have halpha := (two_conjugate_alpha_and_saturation T hP U hU hJ q hker
    (residual_centralizer_le_coreFrattini T hP U hU hJ)
    (noStrong_of_natural_quotient U q hq hker f hf he _) g hg hgenJ hcod).2.1
  refine ⟨?_,halpha⟩
  apply sylow_lift_of_decomposition U (T : Subgroup G) (pResidual 2 G)
    T.isPGroup' halpha (centralizer_sylow T U)
  have has : Function.Surjective (actionMap U) := QuotientGroup.mk'_surjective _
  have hBa : (baumann (T : Subgroup G)).map (actionMap U) =
      (T : Subgroup G).map (actionMap U) := by
    apply comap_injective has
    rw [comap_map_eq,comap_map_eq,actionMap_ker]
    have hh := congrArg (comap q) hBq
    simpa only [comap_map_eq,hker] using hh
  rw [hBa,←Subgroup.map_sup,pResidual_sup_sylow_eq_top,
    map_top_of_surjective (actionMap U) has]
  obtain ⟨P,hP⟩ := (T.mapSurjective (f := actionMap U) has).exists_sylow_map_eq_inf_of_normal ⊤
  exact ⟨P,by simpa only [inf_top_eq,Sylow.coe_mapSurjective] using hP⟩
end CFSG.Quasithin.ChapterB.RankOneBaumann
