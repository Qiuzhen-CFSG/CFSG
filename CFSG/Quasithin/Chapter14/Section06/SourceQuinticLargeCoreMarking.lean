module

public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticCoreCenter
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticFiveResidualSeed
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticFiveSemilinearData

/-!
# Marked coordinates for the original large quintic core

The reciprocal geometry proves the full residual centralizer, and the actual
order-twenty action supplies an involution outside the derived span. These
source results discharge both remaining inputs of the semilinear construction.
The resulting core equivalence retains the original central line and the
fixed cyclic-four subgroup. No complement or endpoint recognition is assumed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original order-1024 core has genuine marked Ree coordinates. -/
theorem source_quintic_large_five_core_marking_of_original
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hlarge : Nat.card (H.pCoreIn 2) = 1024)
    (A : Subgroup G) (hAH : A ≤ H) (hA : Nat.card A = 5) :
    ∃ eQ : ReeTwo.Core ≃* H.pCoreIn 2,
      zpowers (eQ (ReeTwo.Core.root 9) : G) = centralInvolutions T ∧
      zpowers (eQ (ReeTwo.Core.root 2) : G) = H.pCoreIn 2 ⊓ centralizer (A : Set G) := by
  exact source_quintic_large_five_core_marking
    hG T hempty hM hu hmany hcard e H hH hi hlarge A hAH hA
    (source_quintic_large_five_residual_centralizer
      hG T hempty hM hu hmany hcard e H hH hi hlarge A hAH hA)
    (source_quintic_large_five_residual_seed
      hG T hempty hM hu hmany hcard e H hH hi hlarge A hAH hA)

end CFSG.Quasithin.Chapter14.Section06
