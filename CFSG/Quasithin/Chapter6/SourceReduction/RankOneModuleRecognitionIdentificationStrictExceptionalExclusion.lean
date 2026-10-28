module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationStrictExceptionalCohomology
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationStrictExceptionalGeometry
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationStrictElimination

/-!
# Ambient exclusion of the exceptional full-four strict action

The layer closure has nontrivial normal image in the strict actor. The
exceptional whole-action coordinates therefore make its dual H¹ vanish.
The literal central cover U/⟨z⟩ → U/Z(U) forces Z(U) to have order two,
so the actual crossed-center image is trivial. In the same marked action,
the relative normal Sylow condition and exchanged summands force this
smaller actor to be nontrivial. This is the required ambient contradiction.

All crossing, binary and Sylow inputs are constructed from the original
LocalAnalysis and Hypothesis611. Only the exceptional whole-action
identification is a branch hypothesis. Source: Aschbacher--Smith 6.2.15--19,
printed pp.688--691, with the exceptional G.10.15 correction recorded in
`docs/quasithin-proof-basis.md`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open ChapterG.Section11.FullLinearFour
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

theorem LocalAnalysis.false_of_strict_whole_full_four
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    [IsElementaryAbelian 2 (StrictVectorQuotient (T : Subgroup G) L R z)]
    {D : Subgroup (StrictActor (T : Subgroup G) L R z)}
    {I J : Submodule (ZMod 2) (Additive (StrictVectorQuotient (T : Subgroup G) L R z))}
    (m : WholeActionModel (strictRepresentation (T : Subgroup G) L R z) D I J) : False := by
  let := A.sourceEqualityVectorQuotient_elementary h611 hz
  obtain ⟨d,hdres,_,hdS,_,hd3,hdH⟩ := strict_exists_crossing_cubic h611 hnatural hz horder
  obtain ⟨he,hX,B,v,h,_,_,_,_,hSv,hXS,hXn,_⟩ :=
    A.strict_g11_inputs h611 hnatural hz horder hTH hstrict hdres hdH hdS hd3
  let := hX
  have hzero := A.strict_crossing_center_image_eq_bot_of_full_four
    h611 hnatural hz horder hTH hstrict m hdres hdH
  have hnon := full_four_smaller_actor_ne_bot m h ⟨_,hSv,hXS,hXn⟩
  apply hnon
  rw [hzero]
  exact Subgroup.bot_subgroupOf (strictCrossingImage (T : Subgroup G) L R z d)

/-- The original strict data rule out the separately named marked exceptional row. -/
theorem LocalAnalysis.not_strict_marked_full_four
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    [IsElementaryAbelian 2 (StrictVectorQuotient (T : Subgroup G) L R z)]
    (B : LinearMap.BilinForm (ZMod 2) (Additive (StrictVectorQuotient (T : Subgroup G) L R z)))
    (v : Additive (StrictVectorQuotient (T : Subgroup G) L R z))
    (W : Submodule (ZMod 2) (Additive (StrictVectorQuotient (T : Subgroup G) L R z)))
    (X : Subgroup (StrictActor (T : Subgroup G) L R z)) (X₀ : Subgroup X) :
    ¬ MarkedAlternative (strictRepresentation (T : Subgroup G) L R z) B v W X X₀ := by
  rintro ⟨D,I,J,m,_⟩
  exact A.false_of_strict_whole_full_four h611 hnatural hz horder hTH hstrict m

theorem LocalAnalysis.false_of_strict_corrected_catalogue
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    {d : G} (hdres : d ∈ strictCrossingResidual (T : Subgroup G) L R)
    (hdH : d ∉ centralizer ({z} : Set G))
    (hdS : d ∈ normalizer ((T : Subgroup G) ⊓ L : Set G)) (hd3 : orderOf d = 3)
    [IsElementaryAbelian 2 (StrictVectorQuotient (T : Subgroup G) L R z)]
    [IsElementaryAbelian 2 (strictCrossingImage (T : Subgroup G) L R z d)]
    (B : LinearMap.BilinForm (ZMod 2) (Additive (StrictVectorQuotient (T : Subgroup G) L R z)))
    (v : Additive (StrictVectorQuotient (T : Subgroup G) L R z))
    (h : ChapterG.Section10.Hypothesis (strictRepresentation (T : Subgroup G) L R z) B v
      (strictHatSpace (T : Subgroup G) L R z (strictCrossingIntersection (T : Subgroup G) L R z d))
      (strictCrossingImage (T : Subgroup G) L R z d)
      ((strictCrossingCenterImage (T : Subgroup G) L R z d).subgroupOf
        (strictCrossingImage (T : Subgroup G) L R z d)))
    (hB : ∀ u w : sourceClosure (T : Subgroup G) L R z,
      B (strictHatElement (T : Subgroup G) L R z u)
        (strictHatElement (T : Subgroup G) L R z w) = 0 ↔ Commute u w)
    (hc : ConclusionWithFullLinearFour (strictRepresentation (T : Subgroup G) L R z) B v
      (strictHatSpace (T : Subgroup G) L R z (strictCrossingIntersection (T : Subgroup G) L R z d))
      (strictCrossingImage (T : Subgroup G) L R z d)
      ((strictCrossingCenterImage (T : Subgroup G) L R z d).subgroupOf
        (strictCrossingImage (T : Subgroup G) L R z d))) :
    False := by
  rcases hc with hc | hc
  · exact A.false_of_strict_catalogue h611 hnatural hz horder hTH hstrict
      hdres hdH hdS hd3 B v h hB hc
  · exact A.not_strict_marked_full_four h611 hnatural hz horder hTH hstrict B v _ _ _ hc

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
