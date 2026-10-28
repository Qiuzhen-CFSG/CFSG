module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCover.Tables

/-! Kernel checks for the literal ATLAS J2G1-P2 dihedral coset certificate.
Each retained deduction is checked against earlier facts and proved relator loops.
Sequential declarations bound the reduction cache. See `source/README.md`. -/

public section
namespace Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCertificate
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 4096 in
theorem checked_671744 : Scan.checkChunk context facts instructions 671744 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_672256 : Scan.checkChunk context facts instructions 672256 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_672768 : Scan.checkChunk context facts instructions 672768 215 = true := by
  decide +kernel

theorem sound_671744 (prior : ∀ n, n < 671744 →
    Holds dihedral generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 672983 → Holds dihedral generator (definitions.repr generator) (facts n) := by
  have h672256 := Scan.chunk_sound context_valid facts instructions 671744 512
    prior checked_671744
  have h672768 := Scan.chunk_sound context_valid facts instructions 672256 512
    h672256 checked_672256
  have h672983 := Scan.chunk_sound context_valid facts instructions 672768 215
    h672768 checked_672768
  exact h672983

end Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCertificate
