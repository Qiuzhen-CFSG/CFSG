module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ReselectedComponent
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.OmegaCentralizationSp4

/-!
# The same containing component at the common-Q reselected point

Apply relative-component recognition to the flag already constructed on
the literal I = K₀ ∨ L₂. The actual first residual is K₀ < K, and K is
normal as a C-component of the new point normalizer, belongs to He, and
is the unique C-component containing that residual. Both original
residual identities, the full second radical and the transferred Cartan
are retained. The quotient (K ∨ X)/O₂(K ∨ X) is the original PGL₃(4)
quotient appearing among the hypotheses.

The common normal Q and the SL₃(4) alternative remain explicit. Their
source discharge, both orientations and full 11.1.1--3 assembly remain
with qt-d-1222-natural-relative-components. Original 7.0.1 and 3.2.5
inputs retain the producers and final assembly documented in
OmegaCentralizationSp4; no later nonbinary exclusion is used.
Source: Aschbacher--Smith, 11.1.2, printed pp.763--764.
-/

open Subgroup Theory.GroupTheory Representation
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

/-- The literal common-Q join retains its flag data and the original K
is now its relatively normal, unique first containing C-component. -/
theorem sp4_triangle_reselected_component_of_common_normal_and_source701325
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
             f_I.Li 0 = K₀ ∧ f_I.Li 1 = f.Li 1 ∧ f_I.Ri 1 = f.Ri 1 ∧
             Source.NormalComponentIn (normalizer (f_I.Vi 0 : Set G)) K ∧
             f_I.Li 0 < K ∧ K ∈ Chapter1.He G ∧
             ∀ J : Subgroup G, Source.ComponentIn (normalizer (f_I.Vi 0 : Set G)) J →
               f_I.Li 0 ≤ J → J = K) := by
  obtain ⟨hmax,hsource,U,D_I,hcases⟩ :=
    sp4_triangle_reselected_flag_of_common_normal_and_source701325
      D S m f hu hm₁ hm₂ hfour hfix hX hK hLK hK₀ hK₀K hTK₀ hk hp hcard hmove
      hQ hQT hTQ hKQ hLQ hpre
  refine ⟨hmax,hsource,U,D_I,?_⟩
  rcases hcases with hsl | ⟨S_I,hd,hf,hmI,hcartan,f_I,hinner,hpoint,hfirst,hsecond,hradical⟩
  · exact .inl hsl
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    (f.invariant 0).trans ((normal_subgroupOf_iff_le_normalizer hK.1.1).mp hK.2)
  have hlocalK : K ∈ Chapter1.L G T := by
    refine ⟨hK.1.2.subgroupOf_of_le le_sup_left (sup_le hK.1.1 (f.invariant 0)),
      ⟨T.subtype le_sup_right,?_⟩,?_⟩
    · simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right]
    · intro he
      apply f.V_ne_bot 0
      apply bot_unique
      have hUT : f.Vi 0 ≤ (T : Subgroup G) :=
        (D.centralQuotientPreimage_le _).trans D.le_sylow
      have hcore := le_pCoreIn_of_normalizes (T.isPGroup'.to_le hUT)
        (hUT.trans (show (T : Subgroup G) ≤ K ⊔ (T : Subgroup G) from le_sup_right))
        (sup_le hK.1.1 (f.invariant 0))
      exact he ▸ hcore
  have hfirstK : f_I.Li 0 < K := by rw [hfirst]; exact hK₀K
  obtain ⟨hrelative,hHe,hunique⟩ := projective_four_relative_component_of_point_centralization
    D_I S_I f_I hd hf (simple_four_fixed_line D_I S_I hd hmI hf f_I)
    hcartan hlocalK hTK hk hfirstK.le hpoint
  exact .inr ⟨S_I,hd,hf,hmI,hcartan,f_I,hinner,hpoint,hfirst,hsecond,hradical,
    hrelative,hfirstK,hHe,hunique⟩

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
