module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.OmegaCentralization
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ReselectedPointSp4

/-!
# Source omega-centralization in the literal common-Q triangle

The faithful-envelope and FF contradiction now discharges [Z,K] = 1
in the checked reselected-point construction. The original earlier-source
7.0.1 and 3.2.5 hypotheses also supply the natural module on I itself.
The resulting flag has first residual K₀, second residual L₂, unchanged
second radical, transferred Cartan and whole-K point centralization.

The common normal Q remains explicit, as does the SL₃(4) alternative.
Their discharge, reselected relative-component recognition, both orientations
and original 11.1.1--3 assembly remain with
qt-d-1222-natural-relative-components. Earlier-source producers and final
discharge retain the owners documented in OmegaCentralization.
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

/-- Earlier source 7.0.1 and 3.2.5 now discharge omega-centralization
for the original common-Q reselected flag. All quotient and radical
identifications refer to the original join K₀ ∨ L₂. -/
theorem sp4_triangle_reselected_flag_of_common_normal_and_source701325
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
    (hKQ : K₀ ≤ normalizer (Q : Set G)) (hLQ : f.Li 1 ≤ normalizer (Q : Set G))
    (hpre : ∀ (J W : Subgroup G) (D_J : ChosenModule T J W),
      Hypothesis1223 KnownSimple.IsKnownSimple T J →
      Chapter7.NormalizedSource.Alternatives G D_J.orbitRepresentation D_J.orbitComponent ∧
        D_J.Source325Alternatives) :
    let I := K₀ ⊔ f.Li 1
    FaithfulMaximalLocal T I ∧ Hypothesis1223 KnownSimple.IsKnownSimple T I ∧
      ∃ (U : Subgroup G) (D_I : ChosenModule T I U),
        Source.IsSL (I ⧸ pCore 2 I) 3 4 ∨
        (∃ S_I : D_I.NonbinaryNaturalInput, S_I.field.degree = 2 ∧
           U ⊓ centralizer (I : Set G) = ⊥ ∧
           (Source.IsSp (I ⧸ pCore 2 I) 2 4 ∨
             ClassificationModels.IsG2At (I ⧸ pCore 2 I) 4) ∧
           IsCartan T I X ∧
           ∃ f_I : InvariantFlag (coordinates D_I S_I), f_I.IsInnerUnique ∧
             K ≤ centralizer (f_I.Vi 0 : Set G) ∧
             f_I.Li 0 = K₀ ∧ f_I.Li 1 = f.Li 1 ∧ f_I.Ri 1 = f.Ri 1) := by
  have hKZ := first_projective_component_centralizes_omega_of_source701325 D S f hK hk hpre
  obtain ⟨hmax,hsource,U,D_I,hcases⟩ :=
    sp4_triangle_reselected_flag_of_common_normal_and_omega_centralization
      D S m f hu hm₁ hm₂ hfour hfix hX hK hLK hK₀ hK₀K hTK₀ hk hp hcard hmove
      hQ hQT hTQ hKQ hLQ hKZ
  refine ⟨hmax,hsource,U,D_I,?_⟩
  rcases hcases with hsl | hnat
  · exact .inl hsl
  · obtain ⟨h701,h325⟩ := hpre _ U D_I hsource
    exact .inr (hnat h701 h325)

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
