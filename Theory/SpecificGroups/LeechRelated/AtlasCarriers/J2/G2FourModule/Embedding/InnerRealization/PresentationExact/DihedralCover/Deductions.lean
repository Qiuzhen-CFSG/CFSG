module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCover.Deductions0
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCover.Deductions1
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCover.Deductions2
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCover.Deductions3
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCover.Deductions4
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCover.Deductions5
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCover.Deductions6
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCover.Deductions7

/-!
# All deductions in the Hall--Janko dihedral coset certificate

Starting from the empty prefix, compose the eight checked deduction ranges.
Every retained fact is thereby a subgroup-witness equation in the abstract
five-relator presentation, with no remaining assumptions about earlier facts.
`DihedralCover.lean` uses these equations for its signed generator transitions.

Source: ATLAS J2G1-P2; see `source/README.md` for the certificate and its rules.
-/

namespace Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCertificate
open Subgroup.CosetWordCertificate

/-- Every retained deduction holds in the original abstract presentation. -/
public theorem all_deductions :
    ∀ n, n < 672983 → Holds dihedral generator (definitions.repr generator) (facts n) := by
  have h0 := deductions_0 (fun n hn => (Nat.not_lt_zero n hn).elim)
  have h1 := deductions_1 h0
  have h2 := deductions_2 h1
  have h3 := deductions_3 h2
  have h4 := deductions_4 h3
  have h5 := deductions_5 h4
  have h6 := deductions_6 h5
  exact deductions_7 h6

end Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCertificate
