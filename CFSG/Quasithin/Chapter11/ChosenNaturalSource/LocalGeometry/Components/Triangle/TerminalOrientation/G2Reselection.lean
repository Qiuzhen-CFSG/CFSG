module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.TerminalOrientation.G2Faithful

/-!
# Reselection at the original G₂ common-normal triangle

The faithful maximal join has a chosen module; outside its retained SL₃(4)
row, original 7.0.1 and 3.2.5 recognize its natural action. The same source
inputs make K centralize the Sylow omega-center. Nonsolvable uniqueness
removes the new fixed layer and identifies its point residual with K₀ and
its plane residual and radical with the original L₂ and R₂. The original
Cartan transfers unchanged, and K is the unique relatively normal component
at the new point.

This removes the reselected-natural-input premise of the previous G₂/G₂
Cartan identity. Common-normal existence and the source SL₃ exclusion remain
with their original producers; the terminal cubic comparison
and final triangle assembly are subsequent steps. No orientation is assumed.
Source: Aschbacher--Smith, 11.1.2, printed p.764.
-/

open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.TerminalOrientation
public noncomputable section
variable {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
    (f : InvariantFlag (.g2 m))

/-- The original G₂ common-Q join supplies the same containing component
at its reselected natural point. Only the preceding source inputs and the
SL₃ row remain explicit. -/
theorem g2_triangle_reselected_component_of_common_normal_and_source701325
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
  intro I
  obtain ⟨hmax,hsource,U,⟨D_I⟩⟩ := g2_triangle_maximal_faithful_of_common_normal
    D S m f hu hm₁ hm₂ hfour hfix hX hK hLK hK₀ hK₀K hTK₀ hk hp hcard hmove
    hQ hQT hTQ hKQ hLQ
  obtain ⟨_,hmI⟩ := g2_triangle_join_three_models_of_common_normal
    D S m f hu hm₁ hm₂ hfour hfix hX hK hLK hK₀ hK₀K hTK₀ hk hp hcard hmove
    hQ hQT hTQ hKQ hLQ
  refine ⟨hmax,hsource,U,D_I,?_⟩
  rcases hmI with hsl | hmI
  · exact .inl hsl
  obtain ⟨h701,h325⟩ := hpre I U D_I hsource
  obtain ⟨S_I,hd,_⟩ := simple_four_natural_of_source701325 D_I hsource hmI S.many h701 h325
  have hKZ := first_projective_component_centralizes_omega_of_source701325 D S f hK hk hpre
  have hgen : f.Li 0 ⊔ f.Li 1 = L := by
    have he (i : Fin 2) : f.Li i = (G2.flag S m).Li i := by
      change localResidual L ((Coordinates.g2 m).preimage (f.space i.castSucc)) = _
      rw [G2.flag_inner_unique S m i.castSucc (f.space i.castSucc)
        (f.dimension i.castSucc) (inf_le_left.trans (f.invariant i.castSucc))]
      rfl
    rw [he 0,he 1]
    exact G2.ResidualIncidence.flag_Li_sup S m
  obtain ⟨hproper₀,hproper₂,_,_⟩ := g2_triangle_proper_residuals D S m f hu hm₁ hfour
    hX hK hLK hK₀ hK₀K hk hp
  obtain ⟨hf,f_I,hinner,_,hfirst,hsecond,hradical⟩ :=
    reselected_paired_flag_of_component_centralizes_omega D S f hm₁ hgen hK.1 hLK
      hK₀ hK₀K.le hproper₀ hproper₂ hKZ D_I S_I hd hmI
  have hXI := g2_triangle_cartan_le_join D S m f hu hm₁ hfour
    hX hK hLK hK₀ hK₀K hk hp
  have hcartan := ShadowReduction.ComponentGeometry.Triangle.Reselection.cartan_transfer
    D S hfour hX D_I S_I hd hXI
  have hXK : X ≤ normalizer (K : Set G) :=
    (f.cartan_normalizes hu hX 0).trans
      ((normal_subgroupOf_iff_le_normalizer hK.1.1).mp hK.2)
  have hpoint := ShadowReduction.ComponentGeometry.Triangle.Reselection.component_centralizes_point_of_cartan
    D_I S_I f_I hf (simple_four_fixed_line D_I S_I hd hmI hf f_I)
      K X hcartan hXK hKZ
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
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.TerminalOrientation
