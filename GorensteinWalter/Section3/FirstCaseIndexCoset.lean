module

public import GorensteinWalter.Section3.FirstCaseJNCoset
import all GorensteinWalter.CosetInvolutionCount

/-!
# The unrestricted coset index sum

Before the source proves that no non-base coset contains five or more
involutions, the generic fibre API gives the full finite sum over all fibre
sizes.  This is the exact bookkeeping form of source identity (3).
-/

noncomputable section

namespace GorensteinWalter

universe u

/-- The index of `Ĥ` is one plus the number of non-base involution fibres. -/
public theorem firstCase_index_eq_one_add_sum_coset_b
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) :
    c.Hhat.index =
      1 + ∑ n ∈ Finset.range (Nat.card {x : G // IsInvolution x} + 1),
        cosetInvolution_b c.Hhat n := by
  exact cosetInvolution_index_eq_one_add_sum_b c.Hhat

end GorensteinWalter
