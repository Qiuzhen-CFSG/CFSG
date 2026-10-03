module

public import Stellmacher.Recognition.NormalFourLargeCoreActionSetup
public import Theory.GroupTheory.PCoreKernelRange
public import Theory.GroupTheory.ExtraspecialThirtyTwoFivePointAction
public import Theory.GroupTheory.SolvableFivePointSylow

/-!
# Transferring the core action to a cyclic-four Sylow quotient

An action of the central-omega normalizer quotient with kernel its actual
two-core has solvable range with trivial two-core. The original Sylow modulo
the core preimage is isomorphic to a Sylow two-subgroup of that same range.
If those Sylow subgroups are cyclic of order at most four, the higher-index
hypothesis forces the original quotient to be cyclic of order exactly four.

These transfers use no elementary-rank bound on the ambient group or Sylow.
For the quaternion–dihedral core its faithful five-point outer action and
the Sylow bound for solvable subgroups of the symmetric group on five letters
with trivial two-core give the unconditional cyclic-four conclusion.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, printed p.389.
-/

namespace Stellmacher.Recognition.NormalEightNonnormalImage

open Subgroup NormalFourCentralOmegaTwo

variable {G : Type*} [Group G] [Finite G]

/-- Every action with the actual core as kernel retains solvability, has
trivial two-core, and models the original Sylow quotient inside its range. -/
public theorem omegaCorePreimage_action_range_data
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    {X : Type*} [Group X] (f : OmegaQuotient S →* X)
    (hker : f.ker = pCore 2 (OmegaQuotient S)) :
    Group.IsSolvable f.range ∧ pCore 2 f.range = ⊥ ∧
      ∃ R : Sylow 2 f.range, Nonempty ((S ⧸ omegaCorePreimage S) ≃* R) := by
  let : Group.IsSolvable (OmegaQuotient S) := omegaQuotient_solvable hN S hZ
  exact ⟨Group.isSolvable_of_surjective f.rangeRestrict_surjective,
    pCore_range_eq_bot_of_ker_eq_pCore 2 f hker,
    omegaCorePreimage_quotient_equiv_sylow_range S f hker⟩

/-- Cyclic Sylow two-subgroups of order at most four in the actual action
range give the exact cyclic-four conclusion in the higher-index branch. -/
public theorem omegaCorePreimage_index_four_and_isCyclic_of_action
    (S : Sylow 2 G) (hindex : 4 ≤ (omegaCorePreimage S).index)
    {X : Type*} [Group X] (f : OmegaQuotient S →* X)
    (hker : f.ker = pCore 2 (OmegaQuotient S))
    (haction : ∀ R : Sylow 2 f.range, IsCyclic R ∧ Nat.card R ≤ 4) :
    (omegaCorePreimage S).index = 4 ∧ IsCyclic (S ⧸ omegaCorePreimage S) := by
  obtain ⟨R, ⟨e⟩⟩ := omegaCorePreimage_quotient_equiv_sylow_range S f hker
  obtain ⟨hcyclic, hcard⟩ := haction R
  let : IsCyclic R := hcyclic
  have hsize : (omegaCorePreimage S).index = Nat.card R :=
    (index_eq_card _).trans (Nat.card_congr e.toEquiv)
  exact ⟨by omega, isCyclic_of_injective e.toMonoidHom e.injective⟩

/-- In the higher-index branch, an extraspecial core of order thirty-two
with core-local elementary rank at most two has cyclic-four Sylow quotient.
No elementary rank bound on the ambient group or its Sylow is required. -/
public theorem omegaCorePreimage_index_four_and_isCyclic_of_core_rank
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (hcoreRank : ∀ E : Subgroup (pCore 2 (OmegaQuotient S)),
      IsElementaryAbelian 2 E → Nat.card E < 8)
    (hindex : 4 ≤ (omegaCorePreimage S).index) :
    (omegaCorePreimage S).index = 4 ∧ IsCyclic (S ⧸ omegaCorePreimage S) := by
  obtain ⟨f, hker⟩ := pCore_exists_five_point_action_of_extraspecial_card_thirty_two
    hcoreRank hH (omegaQuotient_centralizer_pCore_le hN S hZ)
  obtain ⟨hsolv, hcore, _⟩ := omegaCorePreimage_action_range_data hN S hZ f hker
  exact omegaCorePreimage_index_four_and_isCyclic_of_action S hindex f hker
    (Sylow.isCyclic_and_card_le_four_of_solvable_five_point f.range hsolv hcore)

end Stellmacher.Recognition.NormalEightNonnormalImage
