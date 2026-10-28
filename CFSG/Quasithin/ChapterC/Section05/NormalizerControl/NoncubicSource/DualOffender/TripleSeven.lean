module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.DualOffender.Faithfulness
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.DualOffender.MovedSource
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.TripleSevenExclusion.Reducible

/-!
# The actual triple-seven exclusion in C.5.13

The original moved dual is faithful and inherits the source quadratic-ratio
bound. The cubic-center section theorem now excludes 3·A₇ on this complete
module, without assuming it irreducible or removing its central layers. Both
natural and A₅ source endpoints retain the literal image in N/C_N(V).

Source: Aschbacher–Smith C.5.13, printed p.163, using K.1, printed p.452.
-/

public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.DualOffender
open ConjugateSource ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G]

/-- The complete faithful moved dual excludes the actual three-cover model. -/
theorem moved_not_triple_seven_of_reduced (V K : Subgroup G)
    [V.Normal] [IsElementaryAbelian 2 V] (hV : Theory.GroupTheory.IsPReduced 2 V)
    (hq : quadraticRatio (movedRepresentation V K).dual ≤ 2) :
    ¬ Chapter1.Section02.LocalModels.IsAlternatingCover (closureImage V K) 7 := by
  exact ChapterK.Alternating.not_alternating_seven_cover_of_cubic_ratio _
    (moved_faithful_of_reduced V K hV).2
    ((cubicRatio_le_quadraticRatio _).trans hq)

/-- The original natural source marking excludes the literal triple-seven component image. -/
theorem natural_source_moved_not_triple_seven {K T : Subgroup G} {F : Type*} [Field F]
    (h : Setup T K F) {n : ℕ} (hn : IsL2EvenBlock K n) (hT : IsPGroup 2 T)
    (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (X : Subgroup G) (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    {x : G} (hx : x ∈ normalizer (T : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G)) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let V := conjugateSpanBy (omegaOneCenterAmbient T) N
    let hs := natural_source_omega_span h hn hT hTK P hP X hA hAX
    let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
    let : IsElementaryAbelian 2 V := hs.1
    let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hs.2.1
    ¬ Chapter1.Section02.LocalModels.IsAlternatingCover (closureImage (V.subgroupOf N) (K.subgroupOf N)) 7 := by
  let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
  let V := conjugateSpanBy (omegaOneCenterAmbient T) N
  have hs := natural_source_omega_span h hn hT hTK P hP X hA hAX
  let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
  let : IsElementaryAbelian 2 V := hs.1
  let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hs.2.1
  exact moved_not_triple_seven_of_reduced (V.subgroupOf N) (K.subgroupOf N)
    (source_omega_span_reduced K T X P hP hA hAX S hS)
    (natural_source_moved_dual_ratio h hn hT hTK P hP X hA hAX hx hnc)

/-- The original A₅ source marking excludes the literal triple-seven component image. -/
theorem alternating_source_moved_not_triple_seven {K T L : Subgroup G}
    (h : AlternatingPairSetup T K L) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (X : Subgroup G) (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    {x : G} (hx : x ∈ normalizer (T : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let V := conjugateSpanBy (omegaOneCenterAmbient T) N
    let hs := alternating_five_source_omega_span h hTK P hP X hA hAX
    let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
    let : IsElementaryAbelian 2 V := hs.1
    let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hs.2.1
    ¬ Chapter1.Section02.LocalModels.IsAlternatingCover (closureImage (V.subgroupOf N) (K.subgroupOf N)) 7 := by
  let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
  let V := conjugateSpanBy (omegaOneCenterAmbient T) N
  have hs := alternating_five_source_omega_span h hTK P hP X hA hAX
  let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
  let : IsElementaryAbelian 2 V := hs.1
  let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hs.2.1
  exact moved_not_triple_seven_of_reduced (V.subgroupOf N) (K.subgroupOf N)
    (source_omega_span_reduced K T X P hP hA hAX S hS)
    (alternating_source_moved_dual_ratio h hTK P hP X hA hAX hx hnc)
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.DualOffender
