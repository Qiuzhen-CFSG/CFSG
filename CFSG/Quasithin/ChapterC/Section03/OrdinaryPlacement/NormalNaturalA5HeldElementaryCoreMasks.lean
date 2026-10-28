module
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.ExtensionChecks.NodeMembers
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.NormalNaturalA5HeldElementaryNative
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.AmbientIdentities.RankSixCertificate.CoreIdentification

/-! The two native maximal elementary masks are the literal local cores. -/
public section
open Subgroup
namespace Held.OrdinaryElementary
open NativeCoverage LocalPairs.SylowGeometry.Calculations
open TwoLocalCandidates.MaximalNormalizerCatalogue
open IntrinsicEnumeration IntrinsicEnumeration.ExtensionChecks
open RankSixCertificate
open LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.CoreKernel

set_option maxRecDepth 8192 in
private theorem core_mask_members : ∀k : Fin 2,∀v : Fin 192,
    (candidateMask ⟨32+k.val,by omega⟩).testBit v.val=true →
      vertexIndex v∈members (some (row k)) := by
  decide +kernel

/-- The two maximal native elementary masks lie in the stated actual
conjugates of the marked local cores. -/
theorem native_core_mask_le (k : Fin 2) (E : Subgroup He)
    (hmask : ∀x:E,∃v : Fin 192,
      (candidateMask ⟨32+k.val,by omega⟩).testBit v.val=true ∧ (native v).val=x.val) :
    E≤(ambientWordCore (k==0)).map
      (MulAut.conj (conjugator (index k))).toMonoidHom := by
  have hc : (ambientWordCore (k==0)).map
      (MulAut.conj (conjugator (index k))).toMonoidHom=ambient (row k) := by
    rw [ambient_eq_conjugated_pCore,ambientWordCore,wordCore_eq_pCore]
    fin_cases k <;> rfl
  rw [hc]
  intro x hx
  obtain ⟨v,hv,he⟩ := hmask ⟨x,hx⟩
  have hm : native v∈entry (row k) :=
    (certified_members (some (row k)) _).mpr ⟨vertexIndex v,core_mask_members k v hv,rfl⟩
  exact ⟨native v,hm,he⟩

end Held.OrdinaryElementary
