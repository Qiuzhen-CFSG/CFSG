module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.Reduction

/-!
# Assembly of elementary J₄ normalizer placement

An exhaustive cover of the maximal elementary normalizers by conjugates
of max1, the standard involution centralizer and max4 splits the ambient
incidence calculation into two absorption calculations. Their transport
keeps the original ambient Sylow subgroup and elementary complement.

All three inputs remain unproved. In particular the conditional theorem
below is not `fixedTwoElementaryNormalizerPlacement` and does not finish
the order-nine branch of Proposition 1.3.4.

Source: Aschbacher–Smith, printed p.511 (PDF p.528 of
`refs/quasithin.pdf`), citing Aschbacher (1986), *Overgroups of Sylow
subgroups in sporadic groups*.
-/

public section

open Subgroup
open Janko4.OuterReduction.OddIndex
open Janko4.LocalStructure.SymmetricLinear

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction

/-- Conditional assembly from the actual normalizer cover and the two
remaining local absorption theorems. No incidence premise is discharged here. -/
theorem fixedTwoElementaryNormalizerPlacement_of_cover_and_absorption
    (hcover : FixedTwoElementaryNormalizerCover)
    (hmathieu : ElementaryMathieuAbsorption)
    (hinvolution : ElementaryInvolutionAbsorption) :
    FixedTwoElementaryNormalizerPlacement := by
  intro _ _ _ S hS R h hE hcard A hA hRA
  obtain ⟨g, hM | hC | hF⟩ := hcover S hS A hA
  · obtain ⟨k, hkS, hkR⟩ := elementaryLocalAbsorption_of_conjugate hmathieu
      S R h hE hcard g (hS ▸ hA.normalized.trans hM) (hRA.trans hM)
    exact ⟨k, hS ▸ hkS, hkR⟩
  · obtain ⟨k, hkS, hkR⟩ := elementaryLocalAbsorption_of_conjugate hinvolution
      S R h hE hcard g (hS ▸ hA.normalized.trans hC) (hRA.trans hC)
    exact ⟨k, hS ▸ hkS, hkR⟩
  · exact ⟨g, hA.normalized.trans hF, hRA.trans hF⟩

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction
