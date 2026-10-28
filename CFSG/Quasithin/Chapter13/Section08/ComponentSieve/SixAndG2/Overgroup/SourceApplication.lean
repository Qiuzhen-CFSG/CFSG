module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.Overgroup.Reduction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.Overgroup.FullDenominators
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Terminal

/-!
# Source applications to the ordinary and covered terminal setups

The original flag line supplies the nontrivial normal two-subgroup used
by the overgroup construction. These applications retain the actual
`sourceOne`, common Sylow, component, quotient and critical pair. The
result identifies the terminal vertex with the normalizer of the original
transported line, and gives relative normality of both star images there.

`source_equalities` works in both the ordinary A₆ and covered L₄ terminal
setups, conditionally on the constrained A.3.12 survivor calculation.
`linear_source_equalities` discharges that input in the L₄ branch using
the previously proved binary-linear theorem. No application assumes H=G₁.
The universal earlier embeddings and uniform reductions remain the genuine
earlier-source inputs of the parent source-theorem assembly.

Source: Aschbacher–Smith, 13.8.25 and 13.8.27(2), printed pp.960,963.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.Overgroup
open AlternatingAndLinear.LinearReduction.Overgroup
open CriticalGeometry SourceCompletion
open TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

private theorem source_line_data (d : LocalSetup T L V V₁ V₂ V₃ M G₁) :
    V₁ ≠ ⊥ ∧ IsPGroup 2 V₁ ∧ V₁ ≤ sourceOne L T V₁ ⊔ (T : Subgroup G) ∧
      G₁ ≤ normalizer (V₁ : Set G) := by
  refine ⟨?_, IsPGroup.of_card (n := 1) (by simpa only [pow_one] using d.line_card), ?_,
    d.first_normalizer.le⟩
  · intro he
    have hc := d.line_card
    rw [he, card_bot] at hc
    contradiction
  · exact ((d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)).trans
      (localNaturalSetup d).chosen.le_sylow).trans le_sup_right

/-- The original source setup, with its flag supplying every auxiliary
normal-two-subgroup premise of the containing-component construction. -/
theorem source_equalities {𝒦 : GroupClass.{u}}
    (earlier : EarlierEmbeddings 𝒦) (rigidity : SurvivorRigidity.{u})
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (facts : UniformComponentFacts L (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hQ : IsSQTK 𝒦 (G₁ ⧸ pCore 2 G₁)) :
    (K.subgroupOf G₁).IsCComponent ∧ (K.subgroupOf G₁).Normal ∧
      G₁ = H ∧ H = K ⊔ (T : Subgroup G) := by
  obtain ⟨hne, hp, hb, hn⟩ := source_line_data d
  exact equalities_of_survivor_rigidity earlier rigidity facts hH hKH hK hne hp hb hn hQ

/-- Covered L₄ source application: the existing linear theorem removes the
constrained-list premise from the actual overgroup equality. -/
theorem linear_source_equalities {𝒦 : GroupClass.{u}}
    (earlier : EarlierEmbeddings 𝒦)
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (facts : UniformComponentFacts L (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hmodel : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 4 2)
    (hQ : IsSQTK 𝒦 (G₁ ⧸ pCore 2 G₁)) : G₁ = H ∧ H = K ⊔ (T : Subgroup G) := by
  obtain ⟨hne, hp, hb, hn⟩ := source_line_data d
  exact ⟨(eq_overgroup_of_uniform_linear_reduction earlier facts hH hKH hK hmodel
    hne hp hb hn hQ).symm, facts.join_eq hH hKH hK⟩

open scoped Pointwise in
/-- The source product KT is the actual set product, by normality relative
 to H. This accompanies the subgroup-join form used by the terminal APIs. -/
theorem source_set_product {𝒦 : GroupClass.{u}}
    (earlier : EarlierEmbeddings 𝒦) (rigidity : SurvivorRigidity.{u})
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (facts : UniformComponentFacts L (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hQ : IsSQTK 𝒦 (G₁ ⧸ pCore 2 G₁)) :
    G₁ = H ∧ (H : Set G) = (K : Set G) * (T : Set G) := by
  have he := source_equalities earlier rigidity d facts hH hKH hK hQ
  refine ⟨he.2.2.1, ?_⟩
  have hn : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    (le_sup_right.trans hH.1.2).trans
      ((normal_subgroupOf_iff_le_normalizer hKH).mp (facts.normal hH hKH hK))
  rw [he.2.2.2, coe_mul_of_right_le_normalizer_left K (T : Subgroup G) hn]
  rfl

/-- The ordinary/covered terminal line-normalizer application, with H=G₁
proved from the containing-component construction rather than supplied. -/
theorem source_endpoint_normalizers {𝒦 : GroupClass.{u}}
    (earlier : EarlierEmbeddings 𝒦) (rigidity : SurvivorRigidity.{u})
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
  have he := (source_equalities earlier rigidity d facts hH hKH hK hQ).2.2.1.symm
  exact ⟨Terminal.endpoint_eq_line_normalizer d c he, Terminal.endpoint_star_normality d c he⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.Overgroup
