module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.Overgroup.Rigidity.Rows
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.Overgroup.SourceApplication

/-!
# Surviving components fill the original overgroup

Apply the complete constrained A.3.12 calculation to the literal star images
constructed by 1.2.4. This proves G₁=H=KT, relative component normality,
and the original critical endpoint's line-normalizer description in both
the ordinary A₆ and covered L₄ setups. The source flag supplies the normal
two-subgroup; neither overgroup equality nor survivor rigidity is an input.

Only the universal earlier embedding theorem, uniform earlier component
reductions, and the source K-group hypothesis remain explicit. Their discharge
belongs to the final 13.8.27 assembly `qt-d-138-six-g2-source`.

Source: Aschbacher–Smith, 13.8.27(2), printed p.963.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.Overgroup.Rigidity
open AlternatingAndLinear.LinearReduction.Overgroup
open CriticalGeometry SourceCompletion
open TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

/-- The actual source application with the constrained-list premise discharged. -/
theorem source_equalities {𝒦 : GroupClass.{u}}
    (earlier : EarlierEmbeddings 𝒦)
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (facts : UniformComponentFacts L (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hQ : IsSQTK 𝒦 (G₁ ⧸ pCore 2 G₁)) :
    (K.subgroupOf G₁).IsCComponent ∧ (K.subgroupOf G₁).Normal ∧
      G₁ = H ∧ H = K ⊔ (T : Subgroup G) := by
  exact Overgroup.source_equalities earlier survivor_rigidity d facts hH hKH hK hQ

open scoped Pointwise in
/-- The actual source application with the constrained-list premise discharged. -/
theorem source_set_product {𝒦 : GroupClass.{u}}
    (earlier : EarlierEmbeddings 𝒦)
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (facts : UniformComponentFacts L (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hQ : IsSQTK 𝒦 (G₁ ⧸ pCore 2 G₁)) :
    G₁ = H ∧ (H : Set G) = (K : Set G) * (T : Set G) := by
  exact Overgroup.source_set_product earlier survivor_rigidity d facts hH hKH hK hQ

/-- The actual source application with the constrained-list premise discharged. -/
theorem source_endpoint_normalizers {𝒦 : GroupClass.{u}}
    (earlier : EarlierEmbeddings 𝒦)
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (facts : UniformComponentFacts L (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hQ : IsSQTK 𝒦 (G₁ ⧸ pCore 2 G₁))
    (c : CriticalPair L (T : Subgroup G) H V) :
    vertexGroup L (T : Subgroup G) H c.gamma = normalizer (c.Aone V₁ : Set G) ∧
      Source.starImage H (normalizer (c.Aone V₁ : Set G)) ≤
        normalizer (Source.starImage H (c.Ugamma V₃) : Set (Source.Hstar H)) ∧
      Source.starImage H (normalizer (c.Aone V₁ : Set G)) ≤
        normalizer (Source.starImage H c.Vgamma : Set (Source.Hstar H)) := by
  exact Overgroup.source_endpoint_normalizers earlier survivor_rigidity d facts hH hKH hK hQ c

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.Overgroup.Rigidity
