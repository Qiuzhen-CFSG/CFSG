module

public import Theory.Alternating.HexEvenQuasisimpleExtension
public import CFSG.Quasithin.ChapterF.Section06.Elementary.Residual

/-!
# The hatted degree-six extension in F.6.18(8)

An actual HexEven component under the original split Sylow gives the cubic
kernel, symmetric-six quotient, derived triple cover and sign inversion
required by the hatted source alternative. The lower construction proves
the natural automorphism image from the split Sylow and does not assume an
ambient model. The final theorem uses the original Goldschmidt intersection
and O²(G); F.6.17 supplies the generalized-Fitting identity and the complete
component sieve supplies the literal HexEven equivalence.

This is the ambient extension conclusion. It makes no assertion about
local vertex markings of an arbitrary Goldschmidt pair.

Source: Aschbacher–Smith F.6.17–18(8), printed pp.309–310.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly
open Theory.HexEvenExtension
variable {G : Type*} [Group G] [Finite G]

/-- The actual HexEven component produces every field of the hatted symmetric-six record. -/
theorem triple_symmetric_six_of_hex_component
    (T : Sylow 2 G) (eT : T ≃* (Multiplicative (ZMod 2) × DihedralGroup 4))
    (K : Subgroup G) [K.Normal] (hquot : IsPGroup 2 (G ⧸ K))
    (hFstar : generalizedFitting G = K) (j : K ≃* Atlas.Codes.HexEvenAutomorphisms) :
    Nonempty (TripleSymmetricExtension G) :=
  ⟨tripleExtension T eT K hquot hFstar j⟩

/-- Literal F.6.18(8) hatted ambient application on the original source residual and Sylow. -/
theorem source_triple_symmetric_six_extension
    {G₁ G₂ : Subgroup G} (h : IsGoldschmidtTriple G₁ G₂)
    (hFstar : pResidual 2 G = generalizedFitting G)
    (eT : (G₁ ⊓ G₂ : Subgroup G) ≃* (Multiplicative (ZMod 2) × DihedralGroup 4))
    (hm : Nonempty (pResidual 2 G ≃* Atlas.Codes.HexEvenAutomorphisms)) :
    Nonempty (TripleSymmetricExtension G) := by
  obtain ⟨T, hT⟩ := h.intersection_sylow
  obtain ⟨j⟩ := hm
  exact triple_symmetric_six_of_hex_component T
    ((MulEquiv.subgroupCongr hT.symm).trans eT) (pResidual 2 G)
    (isPGroup_quotient_pResidual 2) hFstar.symm j

end CFSG.Quasithin.ChapterF.SourceAssembly
