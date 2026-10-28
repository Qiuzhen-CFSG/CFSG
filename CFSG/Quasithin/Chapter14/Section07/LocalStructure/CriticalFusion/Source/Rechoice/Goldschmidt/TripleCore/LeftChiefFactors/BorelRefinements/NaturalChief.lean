module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.TripleCore.LeftChiefFactors.BorelRefinements.SourceCoordinates
public import Theory.GroupTheory.NoncentralChiefRefinement.BinaryFlagSections

/-!+# The two natural chief factors on the original source section

The literal map from `U/V₁` to the natural binary four-space is equivariant
for the original `L₁T` conjugation action. Its invariant Borel line and its
quotient are irreducible and noncentral. Pulling back this flag, and refining
below the map's kernel, yields two noncentral two-chief factors between the
original point and U nodes. Equivariant Jordan–Hölder gives the same lower
bound for any chief series on that interval.

This supplies the natural contribution in Aschbacher–Smith 14.7.70,
printed p.1074/PDF p.1091. `CompatibleBorel` remains the original marking
obligation of the source assembly owner. `SectionCentralizer` is the genuine
earlier 14.5.15(4) input, produced by qt-14-05. Neither is replaced by a chief
count hypothesis. The dual contribution and the final five-factor assembly
remain with qt-14-07-left-borel-chief-refinements.
-/

@[expose] public section
noncomputable section
open Subgroup NoncentralChiefRefinement Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements
open Chapter12.Section08 Representation.SL2FourNatural
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

local notation "B" => (F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G)

/-- The two natural factors, on a chief refinement of the literal source U/V₁ section. -/
theorem exists_sourceNaturalChief (h : CompatibleBorel d) (hc : d.SectionCentralizer) :
    ∃ s : ChiefSeries B,
      s.head = sourcePointNode (F := F) (L := L) ∧ s.last = sourceUNode d ∧
        2 ≤ s.noncentralTwoCount := by
  let := sourceLine_irreducible d h
  let := sourceQuotient_irreducible d h
  have hAB : sourcePointNode (F := F) (L := L) ≤ sourceUNode d :=
    fun _ hx => (source_filtration_containments d hc).1 hx
  exact BinaryFlag.exists_refinement_of_surjection hAB (sourceLine d h)
    (sourceLine_noncentral d h) (sourceQuotient_noncentral d h)
    (sourceNaturalMap d) (sourceNaturalMap_surjective d hc)
    (sourceNaturalMap_equivariant d)

/-- The natural contribution holds for every chief series between the original source nodes. -/
theorem sourceNaturalChief_count (h : CompatibleBorel d) (hc : d.SectionCentralizer)
    (s : ChiefSeries B) (hs0 : s.head = sourcePointNode (F := F) (L := L))
    (hsl : s.last = sourceUNode d) : 2 ≤ s.noncentralTwoCount := by
  obtain ⟨t, ht0, htl, ht⟩ := exists_sourceNaturalChief d h hc
  rw [s.noncentralTwoCount_eq t (hs0.trans ht0.symm) (hsl.trans htl.symm)]
  exact ht

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements
