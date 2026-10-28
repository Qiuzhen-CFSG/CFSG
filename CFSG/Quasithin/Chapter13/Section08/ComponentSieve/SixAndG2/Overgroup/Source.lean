module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.Overgroup.Rigidity.Source
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.Overgroup.Symmetry.Denominators

/-!
# The original overgroup and case-(1) conclusions

The containing component is constructed through the actual 1.2.4/A.3.12
embedding. The constrained survivor calculation proves equality with K and
hence G₁=H=KT, including the literal set product and relative normality.
This supplies H=G₁ to denominator symmetry for the original critical pair.
The case-(1) disjunction of 13.8.8 then yields every assertion in 13.8.27(3):
both full denominators, the transvection action with center V₁, its containment
in Uγ, and Vγ escaping Q_H.

The same application covers the ordinary A₆ and covered L₄ terminal setups;
no component model, pair or conjugator is replaced. The universal earlier
embedding theorem, uniform earlier component reductions, F.9.16, ambient
centralizer input and the literal quotient-module alternatives of 13.8.5/13.7.6
remain the genuine earlier source inputs. Their final discharge, and the
13.8.27 dichotomy, belong to `qt-d-138-six-g2-source`. There is no survivor
rigidity, marked transport, overgroup equality, or symmetry premise.

Source: Aschbacher--Smith, 13.8.27(2--3), printed p.963, PDF p.980.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.Overgroup
open AlternatingAndLinear.LinearReduction.Overgroup
open CriticalGeometry CriticalGeometry.AsymmetricPair SourceCompletion
open TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {K : Subgroup G}

/-- Source clauses (2--3) with all local rigidity, transport, and fusion
premises discharged, on the unchanged source critical pair. -/
theorem source_case_one {𝒦 : GroupClass.{u}}
    (earlier : EarlierEmbeddings 𝒦)
    {T : Sylow 2 G} {L H V V₁ V₂ V₃ M G₁ : Subgroup G}
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (facts : UniformComponentFacts L (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hQ : IsSQTK 𝒦 (G₁ ⧸ pCore 2 G₁))
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalPair L (T : Subgroup G) H V)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (Q : letI := d.uh_elementary hHz
      CenterQuotientAction H (Source.UH H V₃) V₁)
    (b : Source.UH H V₃) (hb : (b : G) ∈ V₂) (hbZ : (b : G) ∉ V₁)
    (hmodels : letI := d.uh_elementary hHz
      (∃ t : H, Q.action t ≠ 1 ∧ binaryLinear (Q.action t) ∈
        LinearEquiv.transvections (ZMod 2) (Additive (Source.Utilde H V₃ V₁))) →
      (Nonempty (Q.Model linearFourRepresentation) ∨
        Nonempty (Q.Model (BinaryPermutation.naturalRepresentation (Fin 6))) ∨
        ∃ N : Q.Model (BinaryPermutation.coreRepresentation (Fin 7)),
          (N.moduleEquiv (CenterQuotientAction.vector b)).val =
            (Pi.single (4 : Fin 7) (1 : ZMod 2) : Fin 7 → ZMod 2) + Pi.single (5 : Fin 7) 1) ∨
      Nonempty (CoverHyperplanes.CoverCoordinates H V₃ V₁))
    (hcase : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃ ∨
      Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃) :
    let _ : IsElementaryAbelian 2 (Source.UH H V₃) := d.uh_elementary hHz
    let _ : IsElementaryAbelian 2 (c.Ugamma V₃) := IsElementaryAbelian.map _
    (K.subgroupOf G₁).IsCComponent ∧ (K.subgroupOf G₁).Normal ∧
      G₁ = H ∧ H = K ⊔ (T : Subgroup G) ∧
      (H : Set G) = (K : Set G) * (T : Set G) ∧
    Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃ ∧
      Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃ ∧
      ⁅V, c.Ugamma V₃⁆ = V₁ ∧ V₁ ≤ c.Ugamma V₃ ∧ ¬ c.Vgamma ≤ Source.QH H ∧
      ∃ action : V →* MulAut (c.Ugamma V₃),
        (∀ v : V, ∀ u : c.Ugamma V₃,
          (action v u : G) = (v : G) * (u : G) * (v : G)⁻¹) ∧
        (∃ v : V, action v ≠ 1) ∧
        (∀ v : V, binaryLinear (action v) ∈
          LinearEquiv.transvections (ZMod 2) (Additive (c.Ugamma V₃))) := by
  have he := Rigidity.source_equalities earlier d facts hHz hKH hK hQ
  have hp := Rigidity.source_set_product earlier d facts hHz hKH hK hQ
  exact ⟨he.1, he.2.1, he.2.2.1, he.2.2.2, hp.2,
    Symmetry.case_one d hHz hF9 c he.2.2.1.symm hcentral Q b hb hbZ hmodels hcase⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.Overgroup
