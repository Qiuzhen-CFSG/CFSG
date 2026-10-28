module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.AugmentationAlternative

/-!
# The doubled-component contradiction from natural MS exhaustion

The original ordinary A₆ quotient is centerless. Its actual Baumann MS pair
therefore needs only the natural branch of C.1.32. The proved initial
recognition and complete distance-two theorem reduce whole-core shortness
to the independent large-distance bound. The original five-dimensional
chief-factor budget then excludes the doubled natural component; original
residual containment is discharged by its earlier Sylow-fixed-point proof.

This is an application of the actual reconstruction contracts, with all
local MS premises proved. It does not assert the large-distance theorem.
Its existing producer is qt-e-ms-small-a6-exhaustion-large-distance; this
consumer does not require the separate cubic-cover reconstruction branch.
The source owner qt-d-1341-nonsolvable-source retains that premise's final
discharge, the other module rows, reciprocal comparison, commutators and
graph assembly. Universal nonsolvability at both escaping weights remains
required for the full source contradiction.

Source: Aschbacher–Smith C.1.32(2), pp.135–136, and 13.4.10(4), p.909;
MS93 (3.6), Section 5 and Section 7, pp.870–872,913–927,932–933.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural AlternatingSixReconstruction.Natural.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original doubled-natural row is impossible once the independent
natural large-distance theorem is supplied. No shortness, residual containment,
MS-pair or full reconstruction premise is left to the caller. -/
theorem ordinary_doubled_excluded_of_largeDistance
    {K : Subgroup G}
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (e : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ : Subgroup G) ≃*
      Multiplicative (BinaryLinearThree.Vector × BinaryLinearThree.Vector))
    (he : let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
      letI := conjMulDistribMulActionOfLeNormalizer K U (normalizer_commutator_ge_right _ _)
      ∀ (k : K) (v : U), (e (k • v)).toAdd =
        (Representation.prod BinaryLinearThree.W BinaryLinearThree.W)
          (eK (QuotientGroup.mk' (pCore 2 K) k)) (e v).toAdd) : False := by
  rcases ordinary_augmentation_baumann_alternative_of_largeDistance
      hl h structural D m eL z hzT hzL with hbound | hshort
  · exact (ordinary_doubled_original_baumann h₀ h structural D m eL z hzT hzL
      hKz hHN hTK hKM eK e he).2.2 hbound
  · exact core_block_excludes_doubled_without_containment h₀ h structural D m z hzT hzL
      hKz hHN hTK hKM hshort eK e he

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
