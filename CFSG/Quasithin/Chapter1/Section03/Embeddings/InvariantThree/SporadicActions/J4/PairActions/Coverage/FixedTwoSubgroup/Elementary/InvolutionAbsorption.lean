module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.Reduction

/-!
# Assembly of elementary-pair absorption from the J₄ involution centralizer

There are two independent remaining inputs. Full generation identifies the
centralizer with the certified conjugate of the original max2 word subgroup.
The local quotient incidence theorem places pairs in that word subgroup into
an actual max4 conjugate. Quotient lifting and composition of the ambient
conjugators then absorb pairs from the full centralizer.

Both inputs remain explicit below: these conditional theorems do not yet
establish `elementaryInvolutionAbsorption`. In particular, no assertion about
the word subgroup is used as an assertion about the full centralizer without
the generation premise.

Source context: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`), citing Aschbacher (1986); GLS3,
Table 5.3i, printed p.270. The actual ATLAS max2 conjugacy bridge is
proved in `TwoCoreCentralizer.Generation.Conjugacy`.
-/

public section

open Subgroup
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open Janko4.LocalStructure.SymmetricLinear

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction

attribute [local irreducible] Janko4.modelGroup max4Subgroup

/-- Full generation, when proved, identifies the actual ambient subgroups. -/
theorem involutionSource_conjugate_eq_centralizer (hgen : localSubgroup = ⊤) :
    sourceSubgroup.map (MulAut.conj h⁻¹).toMonoidHom =
      centralizer ({Janko4.a} : Set Janko4.Model) := by
  rw [sourceSubgroup_map_conj, hgen, ← MonoidHom.range_eq_map,
    centralizerToModel_range]

/-- The quotient incidence calculation absorbs pairs in the word subgroup. -/
theorem elementaryInvolutionSourceAbsorption_of_quotientIncidence
    (hi : ElementaryInvolutionQuotientIncidence) :
    ElementaryLocalAbsorption sourceSubgroup := by
  intro _ _ _ S R hp hE hc hS hR
  obtain ⟨g, hcore, himage⟩ := hi S R hp hE hc hS hR
  exact ⟨g, involutionSource_pair_le_max4_of_quotient S R hS hR g hcore himage⟩

/-- Conditional assembly for the full centralizer. The assembly owner must
discharge both generation and local incidence before claiming absorption. -/
theorem elementaryInvolutionAbsorption_of_generation_and_quotientIncidence
    (hgen : localSubgroup = ⊤) (hi : ElementaryInvolutionQuotientIncidence) :
    ElementaryInvolutionAbsorption := by
  intro _ _ _ S R hp hE hc hS hR
  rw [← involutionSource_conjugate_eq_centralizer hgen] at hS hR
  exact elementaryLocalAbsorption_of_conjugate
    (elementaryInvolutionSourceAbsorption_of_quotientIncidence hi)
    S R hp hE hc h⁻¹ hS hR

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction
