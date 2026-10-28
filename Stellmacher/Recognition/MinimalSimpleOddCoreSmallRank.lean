module

public import Stellmacher.Recognition.MinimalSimpleOddCoreOvergroups
public import Stellmacher.Recognition.MinimalSimpleOddCoreInternalControl
public import GorensteinWalter.Section2.BenderSolvableUniqueness

/-!
# The Bender obstruction for small-rank odd-core normalizer control

Let R be the nontrivial completed odd-core closure of a rank-three binary
actor. A maximal overgroup M of N_G(R) has nontrivial odd core. Since M is
solvable, Bender's theorem rules out a distinct maximal subgroup N with
nontrivial two-core and mutual generalized-Fitting containment.

Solvability and the rank-two quotient fusion exclusion now show that every
proper overgroup of N_G(R) equals N_G(R). Thus N_G(R) itself is maximal,
and internal normalizer control is proved. This equality does not follow
from the odd-core sandwich or Fitting containment alone.

The original two-input assembly interface is retained. A second assembly
uses the proved internal result and leaves only construction of a Bender
pair for an escaping normalizer. Equivalently, it suffices to show that the
join of the two normalizers is proper. Neither remaining input is asserted,
so unconditional small-rank normalizer control is still open here.

Source: GLS2, Chapter F, Theorem 19.1 and Sections 21–22. The construction
of the pair is a separate uniqueness argument, not a consequence of
Theorem 19.1 alone.
-/

namespace Stellmacher.Recognition

/-- The completed closure normalizer is maximal when the closure is
nontrivial. Proper-overgroup equality uses the solvable quotient obstruction
and ambient involution fusion. -/
public theorem minimalSimple_oddCore_normalizer_isCoatom
    {G : Type*} [Group G] [Finite G] (hG : IsMinimalSimple G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hR : involutionOddCoreClosure A ≠ ⊥) :
    IsCoatom (Subgroup.normalizer (involutionOddCoreClosure A : Set G)) := by
  obtain ⟨M, hM, -, hNM, -⟩ := minimalSimple_oddCore_maximal_overgroup hG A hA hR
  rwa [minimalSimple_oddCore_proper_overgroup_eq_normalizer hG A M hA hM.lt_top hNM]
    at hM

/-- A proper join with the closure normalizer suffices for control, without
any rank condition on Q. Proving that the join is proper remains a separate
uniqueness problem. -/
public theorem minimalSimple_oddCore_normalizer_control_of_proper_join
    {G : Type*} [Group G] [Finite G] (hG : IsMinimalSimple G)
    (A Q : Subgroup G) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hjoin : Subgroup.normalizer (involutionOddCoreClosure A : Set G) ⊔
      Subgroup.normalizer (Q : Set G) < ⊤) :
    Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer (involutionOddCoreClosure A : Set G) := by
  have heq := minimalSimple_oddCore_proper_overgroup_eq_normalizer
    hG A _ hA hjoin le_sup_left
  exact heq ▸ (le_sup_right : Subgroup.normalizer (Q : Set G) ≤ _ ⊔ _)

/-- The odd core of a proper overgroup of the closure normalizer is
nontrivial when the closure is nontrivial. -/
public theorem minimalSimple_oddCore_overgroup_oddCore_ne_bot
    {G : Type*} [Group G] [Finite G] (hG : IsMinimalSimple G)
    (A M : Subgroup G) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hR : involutionOddCoreClosure A ≠ ⊥) (hM : M < ⊤)
    (hNM : Subgroup.normalizer (involutionOddCoreClosure A : Set G) ≤ M) :
    pPrimeCore 2 M ≠ ⊥ := by
  intro hbot
  have hle := (minimalSimple_oddCore_overgroup_sandwich hG A M hA hM hNM).1
  rw [hbot, Subgroup.map_bot] at hle
  exact hR (bot_unique hle)

/-- A maximal overgroup of the closure normalizer cannot form a distinct
Bender pair with a maximal subgroup having nontrivial two-core. -/
public theorem minimalSimple_oddCore_maximal_pair_eq
    {G : Type*} [Group G] [Finite G] (hG : IsMinimalSimple G)
    (A M N : Subgroup G) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hR : involutionOddCoreClosure A ≠ ⊥)
    (hM : IsCoatom M) (hN : IsCoatom N)
    (hNM : Subgroup.normalizer (involutionOddCoreClosure A : Set G) ≤ M)
    (hcore : pCore 2 N ≠ ⊥)
    (hFMN : fittingSubgroupOf M ≤ N)
    (hFNM : fittingSubgroupOf N ≤ M) : M = N := by
  have hMlt : M < ⊤ := lt_top_iff_ne_top.mpr hM.ne_top
  exact GorensteinWalter.maximal_eq_of_solvable_mutual_fitting_and_incompatible_cores
    hG.isSimpleGroup M N hM hN (hG.solvable_of_lt M hMlt)
    (hG.solvable_of_lt N (lt_top_iff_ne_top.mpr hN.ne_top)) 2
    (minimalSimple_oddCore_overgroup_oddCore_ne_bot hG A M hA hR hMlt hNM)
    hcore hFMN hFNM

/-- Explicit assembly interface for the two outstanding uniqueness inputs.
Choose an actual maximal overgroup M. A normalizer contained in M is
handled by the internal control input; one escaping M must produce a
Bender pair. Neither input assumes that M equals the closure normalizer. -/
public theorem minimalSimple_oddCore_normalizer_control_of_overgroup_inputs
    {G : Type*} [Group G] [Finite G] (hG : IsMinimalSimple G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hR : involutionOddCoreClosure A ≠ ⊥) (Q : Subgroup G)
    (hinside : ∀ M : Subgroup G, IsCoatom M →
      Subgroup.normalizer (involutionOddCoreClosure A : Set G) ≤ M →
      Subgroup.normalizer (Q : Set G) ≤ M →
      Subgroup.normalizer (Q : Set G) ≤
        Subgroup.normalizer (involutionOddCoreClosure A : Set G))
    (hlink : ∀ M : Subgroup G, IsCoatom M →
      Subgroup.normalizer (involutionOddCoreClosure A : Set G) ≤ M →
      ¬ Subgroup.normalizer (Q : Set G) ≤ M →
      ∃ N : Subgroup G, IsCoatom N ∧
        Subgroup.normalizer (Q : Set G) ≤ N ∧ pCore 2 N ≠ ⊥ ∧
        fittingSubgroupOf M ≤ N ∧ fittingSubgroupOf N ≤ M) :
    Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer (involutionOddCoreClosure A : Set G) := by
  obtain ⟨M, hM, _, hNM, _⟩ := minimalSimple_oddCore_maximal_overgroup hG A hA hR
  by_cases hQM : Subgroup.normalizer (Q : Set G) ≤ M
  · exact hinside M hM hNM hQM
  · obtain ⟨N, hN, hQN, hcore, hMN, hNM'⟩ := hlink M hM hNM hQM
    have heq := minimalSimple_oddCore_maximal_pair_eq hG A M N hA hR
      hM hN hNM hcore hMN hNM'
    exact (hQM (hQN.trans heq.ge)).elim

/-- Only the escaping Bender-pair input remains after internal control.
This preserves the precise small-rank hypotheses for the final assembly. -/
public theorem minimalSimple_oddCore_normalizer_control_of_bender_input
    {G : Type*} [Group G] [Finite G] (hG : IsMinimalSimple G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hR : involutionOddCoreClosure A ≠ ⊥) (S : Sylow 2 G) (hAS : A ≤ S)
    (Q : Subgroup G) (hQ : Q ≠ ⊥) (hQtwo : IsPGroup 2 Q) (hQS : Q ≤ S)
    (hQsmall : ∀ B : Subgroup G, B ≤ Q → IsElementaryAbelian 2 B → Nat.card B < 8)
    (hlink : ∀ M : Subgroup G, IsCoatom M →
      Subgroup.normalizer (involutionOddCoreClosure A : Set G) ≤ M →
      ¬ Subgroup.normalizer (Q : Set G) ≤ M →
      ∃ N : Subgroup G, IsCoatom N ∧
        Subgroup.normalizer (Q : Set G) ≤ N ∧ pCore 2 N ≠ ⊥ ∧
        fittingSubgroupOf M ≤ N ∧ fittingSubgroupOf N ≤ M) :
    Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer (involutionOddCoreClosure A : Set G) :=
  minimalSimple_oddCore_normalizer_control_of_overgroup_inputs hG A hA hR Q
    (minimalSimple_oddCore_internal_control hG A hA hR S hAS Q hQ hQtwo hQS hQsmall)
    hlink

end Stellmacher.Recognition
