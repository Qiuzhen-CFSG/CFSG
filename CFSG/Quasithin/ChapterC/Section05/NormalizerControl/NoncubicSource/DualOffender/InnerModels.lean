module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.DualOffender.Faithfulness
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.DualOffender.MovedSource
public import Theory.SpecificGroups.PSL2.BinaryTwentyFiveRatio
public import Theory.SpecificGroups.Janko1.Model.BinaryCubicRatio
/-!
# The actual PSL₂(25) and J₁ exclusions in C.5.13

The source moved module and its inverse dual are faithful, including their
central layer. The actual natural and A₅ actors give dual quadratic ratio
at most two. The inner involution bounds in PSL₂(25) and J₁ contradict this
ratio, so neither group is the literal normal-closure image in N/C_N(V).
No irreducibility, chief-factor replacement, or ambient outer-action
hypothesis is introduced.
Source: Aschbacher–Smith C.5.13, printed p.163, using K.2 and K.4.
-/
public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.DualOffender
open ConjugateSource ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G]
/-- The faithful moved dual of a reduced section cannot have either inner actor. -/
theorem moved_model_exclusions_of_reduced (V K : Subgroup G)
    [V.Normal] [IsElementaryAbelian 2 V] (hV : Theory.GroupTheory.IsPReduced 2 V)
    (hq : quadraticRatio (movedRepresentation V K).dual ≤ 2) :
    ¬ ClassicalGroup.IsPSL (closureImage V K) 2 25 ∧
      ¬ Nonempty (closureImage V K ≃* Janko1.Model) := by
  have hf := (moved_faithful_of_reduced V K hV).2
  have hc := (cubicRatio_le_quadraticRatio (movedRepresentation V K).dual).trans hq
  constructor
  · rintro ⟨F,_,_,hF,⟨e⟩⟩
    exact (not_lt_of_ge hc) (Theory.PSL2.two_lt_cubicRatio_of_twentyFive _ hf hF e)
  · rintro ⟨e⟩
    exact (not_lt_of_ge hc) (Janko1.two_lt_cubicRatio_of_model _ hf e)

/-- The original natural source marking excludes both literal component images. -/
theorem natural_source_moved_model_exclusions {K T : Subgroup G} {F : Type*} [Field F]
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
    ¬ ClassicalGroup.IsPSL (closureImage (V.subgroupOf N) (K.subgroupOf N)) 2 25 ∧
      ¬ Nonempty (closureImage (V.subgroupOf N) (K.subgroupOf N) ≃* Janko1.Model) := by
  let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
  let V := conjugateSpanBy (omegaOneCenterAmbient T) N
  have hs := natural_source_omega_span h hn hT hTK P hP X hA hAX
  let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
  let : IsElementaryAbelian 2 V := hs.1
  let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hs.2.1
  exact moved_model_exclusions_of_reduced (V.subgroupOf N) (K.subgroupOf N)
    (source_omega_span_reduced K T X P hP hA hAX S hS)
    (natural_source_moved_dual_ratio h hn hT hTK P hP X hA hAX hx hnc)

/-- The original A₅ source marking excludes both literal component images. -/
theorem alternating_source_moved_model_exclusions {K T L : Subgroup G}
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
    ¬ ClassicalGroup.IsPSL (closureImage (V.subgroupOf N) (K.subgroupOf N)) 2 25 ∧
      ¬ Nonempty (closureImage (V.subgroupOf N) (K.subgroupOf N) ≃* Janko1.Model) := by
  let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
  let V := conjugateSpanBy (omegaOneCenterAmbient T) N
  have hs := alternating_five_source_omega_span h hTK P hP X hA hAX
  let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
  let : IsElementaryAbelian 2 V := hs.1
  let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hs.2.1
  exact moved_model_exclusions_of_reduced (V.subgroupOf N) (K.subgroupOf N)
    (source_omega_span_reduced K T X P hP hA hAX S hS)
    (alternating_source_moved_dual_ratio h hTK P hP X hA hAX hx hnc)
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.DualOffender
