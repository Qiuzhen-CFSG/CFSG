module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ReselectedPoint
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ReselectedNaturalSp4

/-!
# Reselected point placement in the literal common-normal triangle

The actual I = K₀ ∨ L₂ is already faithful maximal. Outside its retained
SL₃(4) row, earlier 7.0.1 and 3.2.5 recognize its chosen natural module.
Assuming the preceding source [Z,K] = 1 assertion, nonsolvable uniqueness
kills its fixed layer. The new point and plane residuals are exactly K₀
and the original L₂, with the same second radical. The original Cartan
transfers to I and its orbit puts the whole K in the point centralizer.
No triangle orientation, later shadow result or extra fixed-line identity
is assumed.

The common normal Q and [Z,K] = 1 remain genuine source obligations.
Their construction, the SL₃(4) exclusion, both final orientations and
original 11.1.1--3 assembly remain with qt-d-1222-natural-relative-components.
Earlier 7.0.1 and 3.2.5 retain producers qt-d-1222-normalized-nonff and
qt-baumann-fsu, with final discharge by qt-d-1222-natural-local-geometry.
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

/-- The original common-Q join has its unchanged SL₃(4) row, or its
reselected natural flag has the required original residuals and point
centralization. The source omega-centralization premise stays explicit. -/
theorem sp4_triangle_reselected_flag_of_common_normal_and_omega_centralization
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
    (hKZ : K ≤ centralizer
      (omegaOneAmbient ((center (T : Subgroup G)).map (T : Subgroup G).subtype) : Set G)) :
    let I := K₀ ⊔ f.Li 1
    FaithfulMaximalLocal T I ∧ Hypothesis1223 KnownSimple.IsKnownSimple T I ∧
      ∃ (U : Subgroup G) (D_I : ChosenModule T I U),
        Source.IsSL (I ⧸ pCore 2 I) 3 4 ∨
        (Chapter7.NormalizedSource.Alternatives G D_I.orbitRepresentation D_I.orbitComponent →
         D_I.Source325Alternatives →
         ∃ S_I : D_I.NonbinaryNaturalInput, S_I.field.degree = 2 ∧
           U ⊓ centralizer (I : Set G) = ⊥ ∧
           (Source.IsSp (I ⧸ pCore 2 I) 2 4 ∨
             ClassificationModels.IsG2At (I ⧸ pCore 2 I) 4) ∧
           IsCartan T I X ∧
           ∃ f_I : InvariantFlag (coordinates D_I S_I), f_I.IsInnerUnique ∧
             K ≤ centralizer (f_I.Vi 0 : Set G) ∧
             f_I.Li 0 = K₀ ∧ f_I.Li 1 = f.Li 1 ∧ f_I.Ri 1 = f.Ri 1) := by
  intro I
  obtain ⟨hmax,hsource,U,D_I,hcases⟩ := sp4_triangle_reselected_natural_of_common_normal
    D S m f hu hm₁ hm₂ hfour hfix hX hK hLK hK₀ hK₀K hTK₀ hk hp hcard hmove
    hQ hQT hTQ hKQ hLQ
  refine ⟨hmax,hsource,U,D_I,?_⟩
  rcases hcases with hsl | hnat
  · exact Or.inl hsl
  right
  intro h701 h325
  obtain ⟨S_I,hd,hmodels⟩ := hnat h701 h325
  have hmI : Source.IsSp (I ⧸ pCore 2 I) 2 4 ∨
      ClassificationModels.IsG2At (I ⧸ pCore 2 I) 4 := hmodels.elim
        (fun h => .inl h.1) (fun h => .inr h.1)
  have hgen : f.Li 0 ⊔ f.Li 1 = L := by
    have he (i : Fin 2) : f.Li i = (Sp4.flag m S).Li i := by
      change localResidual L ((Coordinates.sp4 m).preimage (f.space i.castSucc)) = _
      rw [Sp4.flag_inner_unique m S i.castSucc (f.space i.castSucc)
        (f.dimension i.castSucc) (inf_le_left.trans (f.invariant i.castSucc))]
      rfl
    rw [he 0,he 1]
    exact Sp4.flag_Li_sup m S S.nonbinary
  obtain ⟨hproper₀,hproper₂,_,_⟩ := sp4_triangle_proper_residuals D S m f hu hm₁ hfour
    hX hK hLK hK₀ hK₀K hk hp
  obtain ⟨hf,f_I,hinner,_,hfirst,hsecond,hradical⟩ :=
    reselected_paired_flag_of_component_centralizes_omega D S f hm₁ hgen hK.1 hLK
      hK₀ hK₀K.le hproper₀ hproper₂ hKZ D_I S_I hd hmI
  have hXI := sp4_triangle_cartan_le_join D S m f hu hm₁ hfour
    hX hK hLK hK₀ hK₀K hk hp
  have hcartan := ShadowReduction.ComponentGeometry.Triangle.Reselection.cartan_transfer
    D S hfour hX D_I S_I hd hXI
  have hXK : X ≤ normalizer (K : Set G) :=
    (f.cartan_normalizes hu hX 0).trans
      ((normal_subgroupOf_iff_le_normalizer hK.1.1).mp hK.2)
  have hpoint := ShadowReduction.ComponentGeometry.Triangle.Reselection.component_centralizes_point_of_cartan
    D_I S_I f_I hf (simple_four_fixed_line D_I S_I hd hmI hf f_I)
      K X hcartan hXK hKZ
  exact ⟨S_I,hd,hf,hmI,hcartan,f_I,hinner,hpoint,hfirst,hsecond,hradical⟩

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
