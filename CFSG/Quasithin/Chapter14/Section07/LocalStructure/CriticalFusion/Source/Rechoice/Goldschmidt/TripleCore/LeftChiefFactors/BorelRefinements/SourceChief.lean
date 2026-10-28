module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.TripleCore.LeftChiefFactors.BorelRefinements.NaturalChief
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.TripleCore.LeftChiefFactors.BorelRefinements.MarkedChief

/-!
# The conditional 2+2+1 family on the original left source sections

The natural epimorphism supplies two factors on U/V₁. The earlier duality
embeds the literal dual natural module in Q_H/C_H(U), giving two more via
its annihilator flag. The unchanged qH map has kernel exactly Q_H in L₁T;
its preimage of the marked root is the actual two-core of L₁T. Additive F₄
coordinates give its one chief factor above Q_H. Equivariant Jordan–Hölder
then gives the respective bounds for every chief series of the three
coarse intervals in SourceFiltration.

Source: Aschbacher–Smith 14.7.70, printed p.1074/PDF p.1091. This completes
the conditional refinement family, not the source theorem. The source
marking, SectionCentralizer adapter, concatenation and residual comparison
remain with qt-14-07-rechoice-left-chief-factors. SectionCentralizer comes
from the earlier local-kernel theorem (qt-12-08-local-kernel and setup),
with genuine structural and uniqueness inputs retained by that owner.
SourceDuality and [U,Q_H]=V₁ remain with qt-14-05-terminal-duality.
No chief count, nontrivial ambient core, or dual surjectivity is assumed.
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

/-- The source actor kernel is exactly the original Q_H node, with the original qH. -/
theorem sourceNormalizerMap_kernel (h : CompatibleBorel d) :
    ConjugationPullback.kernelNode (sourceNormalizerMap d h) =
      sourceQNode (F := F) (L := L) := by
  apply Subtype.ext
  ext b
  change sourceNormalizerMap d h b = 1 ↔ b.val ∈ F.H.pCoreIn 2
  rw [Subtype.ext_iff]
  change Subgroup.inclusion group_le_H b ∈ d.qH.ker ↔ b.val ∈ F.H.pCoreIn 2
  rw [d.qH_ker]
  rfl

/-- The literal preimage of the marked root above Q_H in the source actor L₁T. -/
def sourceCoreNode (h : CompatibleBorel d) : NormalNode B :=
  ConjugationPullback.preimageNode (sourceNormalizerMap d h)
    (rootNode d.naturalQuotient (normalizer d.naturalQuotient)
      (borel d.naturalQuotient).le_normalizer le_rfl)

/-- The upper node uses the actual root and the unchanged source map. -/
theorem sourceCoreNode_val (h : CompatibleBorel d) :
    (sourceCoreNode d h).val = (root d.naturalQuotient).comap (sourceActorMap d) := rfl

/-- Equivalently it is the preimage of the intrinsic core of the symmetric normalizer. -/
theorem sourceCoreNode_val_eq_core_preimage (h : CompatibleBorel d) :
    (sourceCoreNode d h).val =
      (pCore 2 (normalizer d.naturalQuotient)).comap (sourceNormalizerMap d h) := by
  change (rootNode d.naturalQuotient (normalizer d.naturalQuotient)
    (borel d.naturalQuotient).le_normalizer le_rfl).val.comap _ = _
  rw [rootNode_normalizer_eq_core]

/-- The original kernel is a two-group, so this numerator is also the actual
intrinsic two-core of L₁T, not just an abstract isomorphic subgroup. -/
theorem sourceCoreNode_eq_twoCore (h : CompatibleBorel d) :
    (sourceCoreNode d h).val = pCore 2 B := by
  rw [sourceCoreNode_val_eq_core_preimage]
  apply (sourceNormalizerMap d h).comap_pCore_of_ker_isPGroup
    (sourceNormalizerMap_surjective d h)
  have hk : (sourceNormalizerMap d h).ker = (sourceQNode (F := F) (L := L)).val :=
    congrArg Subtype.val (sourceNormalizerMap_kernel d h)
  rw [hk]
  exact (isPGroup_pCoreIn 2 F.H).comap_subtype

theorem sourceQ_le_sourceCore (h : CompatibleBorel d) :
    sourceQNode (F := F) (L := L) ≤ sourceCoreNode d h := by
  rw [← sourceNormalizerMap_kernel d h]
  exact ConjugationPullback.kernel_le_preimage _ _

/-- One-copy coordinates on the literal relative quotient above Q_H. -/
def sourceCoreCoordinates (h : CompatibleBorel d) :
    SectionCoordinates (sourceQNode (F := F) (L := L)) (sourceCoreNode d h)
      ((actorCore d.naturalQuotient (normalizer d.naturalQuotient) le_rfl).comp
        (sourceNormalizerMap d h)) 1 := by
  have c := pulledCoreCoordinates d.naturalQuotient (normalizer d.naturalQuotient)
    (borel d.naturalQuotient).le_normalizer le_rfl (sourceNormalizerMap d h)
    (sourceNormalizerMap_surjective d h)
  rw [sourceNormalizerMap_kernel d h] at c
  exact c

/-- The core contribution is exactly one on its pulled-back chief section. -/
theorem exists_sourceCoreChief (h : CompatibleBorel d) :
    ∃ s : ChiefSeries B, s.head = sourceQNode (F := F) (L := L) ∧
      s.last = sourceCoreNode d h ∧ s.length = 1 ∧ s.noncentralTwoCount = 1 := by
  obtain ⟨s, hs0, hsl, hn, hc⟩ := exists_coreChief_of_actorMap d.naturalQuotient
    (normalizer d.naturalQuotient) (borel d.naturalQuotient).le_normalizer le_rfl
    (sourceNormalizerMap d h) (sourceNormalizerMap_surjective d h)
  rw [sourceNormalizerMap_kernel d h] at hs0
  exact ⟨s, hs0, hsl, hn, hc⟩

theorem sourceCoreChief_count (h : CompatibleBorel d) (s : ChiefSeries B)
    (hs0 : s.head = sourceQNode (F := F) (L := L)) (hsl : s.last = sourceCoreNode d h) :
    s.noncentralTwoCount = 1 := by
  obtain ⟨t, ht0, htl, _, ht⟩ := exists_sourceCoreChief d h
  exact (s.noncentralTwoCount_eq t (hs0.trans ht0.symm) (hsl.trans htl.symm)).trans ht

/-- The final coarse interval of SourceFiltration retains the core contribution. -/
theorem exists_sourceAboveQChief (h : CompatibleBorel d) :
    ∃ s : ChiefSeries B, s.head = sourceQNode (F := F) (L := L) ∧
      s.last = ⊤ ∧ 1 ≤ s.noncentralTwoCount := by
  obtain ⟨s, hs0, hsl, _, hc⟩ := exists_sourceCoreChief d h
  obtain ⟨t, ht0, htl, ht⟩ := BinaryFlag.extend_count le_rfl le_top s hs0 hsl
  rw [hc] at ht
  exact ⟨t, ht0, htl, ht⟩

theorem sourceAboveQChief_count (h : CompatibleBorel d) (s : ChiefSeries B)
    (hs0 : s.head = sourceQNode (F := F) (L := L)) (hsl : s.last = ⊤) :
    1 ≤ s.noncentralTwoCount := by
  obtain ⟨t, ht0, htl, ht⟩ := exists_sourceAboveQChief d h
  rw [s.noncentralTwoCount_eq t (hs0.trans ht0.symm) (hsl.trans htl.symm)]
  exact ht

variable {X Y : Type u} [AddCommGroup X] [Module (ZMod 2) X]
  [AddCommGroup Y] [Module (ZMod 2) Y]

/-- The original dual embedding and annihilator flag give the two dual factors. -/
theorem exists_sourceDualChief (h : CompatibleBorel d) (hc : d.SectionCentralizer)
    (duality : CriticalIntersections.SourceDuality F X Y)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) :
    ∃ s : ChiefSeries B, s.head = sourceCentralizerNode d ∧
      s.last = sourceQNode (F := F) (L := L) ∧ 2 ≤ s.noncentralTwoCount := by
  obtain ⟨j, hj, he⟩ := exists_sourceDualEmbedding d hc duality hcomm
  exact exists_dualChief_of_actorMap d.naturalQuotient (normalizer d.naturalQuotient)
    (borel d.naturalQuotient).le_normalizer le_rfl (sourceNormalizerMap d h)
    (sourceNormalizerMap_surjective d h)
    (fun _ hx => (source_filtration_containments d hc).2.2.1 hx) j hj he

theorem sourceDualChief_count (h : CompatibleBorel d) (hc : d.SectionCentralizer)
    (duality : CriticalIntersections.SourceDuality F X Y)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) (s : ChiefSeries B)
    (hs0 : s.head = sourceCentralizerNode d) (hsl : s.last = sourceQNode (F := F) (L := L)) :
    2 ≤ s.noncentralTwoCount := by
  obtain ⟨t, ht0, htl, ht⟩ := exists_sourceDualChief d h hc duality hcomm
  rw [s.noncentralTwoCount_eq t (hs0.trans ht0.symm) (hsl.trans htl.symm)]
  exact ht

/-- The three literal source intervals supply the 2+2+1 refinement family. Final
concatenation and comparison with the original L₁ remain with source assembly. -/
theorem sourceChief_refinement_family (h : CompatibleBorel d) (hc : d.SectionCentralizer)
    (duality : CriticalIntersections.SourceDuality F X Y)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) :
    (∃ s : ChiefSeries B, s.head = sourcePointNode (F := F) (L := L) ∧
      s.last = sourceUNode d ∧ 2 ≤ s.noncentralTwoCount) ∧
    (∃ s : ChiefSeries B, s.head = sourceCentralizerNode d ∧
      s.last = sourceQNode (F := F) (L := L) ∧ 2 ≤ s.noncentralTwoCount) ∧
    (∃ s : ChiefSeries B, s.head = sourceQNode (F := F) (L := L) ∧
      s.last = ⊤ ∧ 1 ≤ s.noncentralTwoCount) := by
  refine ⟨?_, exists_sourceDualChief d h hc duality hcomm, exists_sourceAboveQChief d h⟩
  exact exists_naturalChief_of_actorMap d.naturalQuotient (normalizer d.naturalQuotient)
    (borel d.naturalQuotient).le_normalizer le_rfl (sourceNormalizerMap d h)
    (sourceNormalizerMap_surjective d h)
    (fun _ hx => (source_filtration_containments d hc).1 hx)
    (sourceNaturalMap d) (sourceNaturalMap_surjective d hc) (sourceNaturalMap_equivariant d)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements
