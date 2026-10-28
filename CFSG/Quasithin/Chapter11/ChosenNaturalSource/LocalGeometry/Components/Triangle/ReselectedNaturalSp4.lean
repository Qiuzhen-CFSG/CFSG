module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.MaximalFaithfulSp4
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ReselectedNatural

/-!
# Natural comparison for the literal common-normal third vertex

The actual join I = K₀ ∨ L₂ is faithful maximal and has a chosen Irr⁺
module on R₂(IT). Its three-model catalogue leaves SL₃(4), or the preceding
7.0.1 and 3.2.5 conclusions recognize that same chosen module as the
natural Sp₄(4) or G₂(4) central quotient. Both the actual group marking
and its intertwining map use the field stored in the resulting input.

The common normal Q remains explicit. This does not exclude SL₃(4), place
the reselected point stabilizer or assert either triangle orientation.
Those obligations and final 11.1.2 assembly remain with
qt-d-1222-natural-relative-components. The earlier source inputs retain
producers qt-d-1222-normalized-nonff and qt-baumann-fsu, and final discharge
by qt-d-1222-natural-local-geometry.
Source: Aschbacher--Smith, 11.1.2, printed pp.763--764.
-/

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
public noncomputable section

variable {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (f : InvariantFlag (.sp4 m))

/-- The literal maximal faithful join has the retained SL₃(4) row, or
its actual chosen module is recognized naturally from the preceding sources.
No orientation or replacement seed is assumed. -/
theorem sp4_triangle_reselected_natural_of_common_normal
    (hu : f.IsInnerUnique)
    (hm₁ : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    (hm₂ : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2^S.field.degree))
    (hfour : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K K₀ X Q : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hTK₀ : (T : Subgroup G) ≤ normalizer (K₀ : Set G))
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 1) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 1) ≤ centralizer (f.Vi 0 : Set G))
    (hQ : Q ≠ ⊥) (hQT : Q ≤ (T : Subgroup G))
    (hTQ : (T : Subgroup G) ≤ normalizer (Q : Set G))
    (hKQ : K₀ ≤ normalizer (Q : Set G)) (hLQ : f.Li 1 ≤ normalizer (Q : Set G)) :
    let I := K₀ ⊔ f.Li 1
    FaithfulMaximalLocal T I ∧ Hypothesis1223 KnownSimple.IsKnownSimple T I ∧
      ∃ (U : Subgroup G) (D_I : ChosenModule T I U),
        Source.IsSL (I ⧸ pCore 2 I) 3 4 ∨
        (Chapter7.NormalizedSource.Alternatives G D_I.orbitRepresentation D_I.orbitComponent →
         D_I.Source325Alternatives →
         ∃ S_I : D_I.NonbinaryNaturalInput, S_I.field.degree = 2 ∧
           ((Source.IsSp (I ⧸ pCore 2 I) 2 4 ∧ Nonempty
             (ActionEquiv D_I.centralQuotientAction (binarySymplectic S_I.field))) ∨
            (ClassificationModels.IsG2At (I ⧸ pCore 2 I) 4 ∧ Nonempty
             (ActionEquiv D_I.centralQuotientAction (binaryG2 S_I.field))))) := by
  intro I
  obtain ⟨hmax,hsource,U,⟨D_I⟩⟩ := sp4_triangle_maximal_faithful_of_common_normal
    D S m f hu hm₁ hm₂ hfour hfix hX hK hLK hK₀ hK₀K hTK₀ hk hp hcard hmove
    hQ hQT hTQ hKQ hLQ
  obtain ⟨_,hmI⟩ := sp4_triangle_join_three_models_of_common_normal
    D S m f hu hm₁ hm₂ hfour hfix hX hK hLK hK₀ hK₀K hTK₀ hk hp hcard hmove
    hQ hQT hTQ hKQ hLQ
  refine ⟨hmax,hsource,U,D_I,?_⟩
  rcases hmI with hsl | hmI
  · exact Or.inl hsl
  · exact Or.inr (simple_four_natural_of_source701325 D_I hsource hmI S.many)

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
