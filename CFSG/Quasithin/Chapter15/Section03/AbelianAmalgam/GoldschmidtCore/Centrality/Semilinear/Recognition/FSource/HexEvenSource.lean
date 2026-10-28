module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.SplitSixteen.HexEvenLocals

/-!
# The literal hatted symmetric-six alternative in F.6.18

The lower ambient extension retains its cubic kernel and actual sign
inversion. The lower local theorem supplies both original vertices as
C₂ × S₄. Together with the original common Sylow and residual marking,
these construct row (8) of the unchanged thirteen-row source interface.

Source: Aschbacher–Smith, F.6.18(8), printed p.310. The component catalogue
and F.6.17 produce the residual marking and generalized-Fitting identity.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
open ChapterF.SourceAssembly

/-- Preserve every field of the already proved lower ambient extension. -/
def tripleSymmetricOfHexExtension {G : Type*} [Group G]
    (r : Theory.HexEvenExtension.TripleSymmetricExtension G) : TripleSymmetric G 6 where
  kernel := r.kernel
  normal := r.normal
  kernelEquiv := r.kernelEquiv
  quotientEquiv := r.quotientEquiv
  kernel_le := r.kernel_le
  derived := ⟨r.derived_perfect, r.derived_center, r.derived_quotient⟩
  center_eq := r.center_eq
  inverse_action := r.inverse_action

/-- The hatted row (8), on the original ambient group, local vertices and Sylow. -/
theorem alternative_eight_of_hex_even {G : Type*} [Group G] [Finite G]
    {G₁ G₂ : Subgroup G} (h : ChapterF.IsGoldschmidtTriple G₁ G₂)
    (hFstar : pResidual 2 G = generalizedFitting G)
    (eT : (G₁ ⊓ G₂ : Subgroup G) ≃* (C 2 × DihedralGroup 4))
    (hm : Nonempty (pResidual 2 G ≃* Atlas.Codes.HexEvenAutomorphisms)) :
    ∃ S : Sylow 2 G, G₁ ⊓ G₂ = (S : Subgroup G) ∧ Alternative G₁ G₂ S := by
  obtain ⟨r⟩ := source_triple_symmetric_six_extension h hFstar eT hm
  obtain ⟨ha,hb⟩ := source_hex_even_vertices h hFstar eT hm
  obtain ⟨S,hS⟩ := h.intersection_sylow
  let eS := (MulEquiv.subgroupCongr hS.symm).trans eT
  let : IsQuasisimple Atlas.Codes.HexEvenAutomorphisms := Representation.Hexacode.even_isQuasisimple
  have hq : IsQuasisimple (generalizedFitting G) := by
    obtain ⟨j⟩ := hm
    exact IsQuasisimple.of_mulEquiv (j.symm.trans (MulEquiv.subgroupCongr hFstar))
  exact ⟨S,hS,.eight (.inl ⟨tripleSymmetricOfHexExtension r⟩) hq ⟨eS⟩ ha hb⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
