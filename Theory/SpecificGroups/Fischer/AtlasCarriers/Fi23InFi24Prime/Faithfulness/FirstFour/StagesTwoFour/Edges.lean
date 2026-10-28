module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesTwoFour.Edges.Checker
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesTwoFour.Edges.Tables

/-!
# Full ambient certificates for the middle Schreier edges

The retained signed words are evaluated using eight cached forward and inverse
permutation tables. `Edges.nonTreeEdges_of_checks` derives the exact membership
contract from full ambient table comparisons and numerical factor checks.
Both inputs remain explicit until their separate certificates are proved;
this module does not yet assert the unconditional `nonTreeEdges` theorem.

The subsequent stabilizer application is in `Edges.Application`, keeping the
membership API independent of the stabilizer assembly and inverse-action proof.
Source: GLS3 Table 5.3v, ATLAS F24G1-p306936B0 and the retained factor witnesses.
-/
