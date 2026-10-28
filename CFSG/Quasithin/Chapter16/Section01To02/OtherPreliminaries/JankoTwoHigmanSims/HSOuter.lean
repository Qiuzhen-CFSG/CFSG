module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.Conventions
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.KernelExclusion
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.Representatives
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Reductions and component consequences for outer involutions of HS

The point-stabilizer certificates cover all abstract automorphisms. The only
common fixed point of two certified stabilizer generators is zero; transitivity
then makes the permutation centralizer trivial. Thus the normalizer action is
an actual equivalence with Aut(HS), and every outer involution lifts to an
involution outside the carrier in its permutation normalizer.

A component of S₈ lies in its commutator subgroup A₈ and hence equals A₈ by
component containment. The checked HS order gives index 1100 for an S₈ fixed
subgroup. The other case has no components once its actual normal two-kernel
is proved self-centralizing. This kernel property is transported separately
from the extension shape: shape alone does not exclude components.

Source: Aschbacher–Smith 16.1.5(10), 16.1.7(h), 16.1.8, printed pp.1172–1173;
GLS3 Table 5.3m. Exhaustive conjugacy coverage and the structures of the two
representative centralizers remain concrete model obligations. The conditional
component result below is not asserted as completion of those source clauses.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSOuter

/-- The only component of the actual symmetric group S₈ is its alternating subgroup. -/
theorem symmetric_component_eq (K : Subgroup S8) (hK : IsComponent S8 K) :
    K = alternatingGroup (Fin 8) := by
  let := hK.2
  have hle : K ≤ alternatingGroup (Fin 8) := by
    rw [← alternatingGroup.commutator_perm_eq (by simp : 5 ≤ Nat.card (Fin 8)),
      commutator_def, ← commutator_eq_self (H := K)]
    exact commutator_mono le_top le_top
  let : IsQuasisimple A8 := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    simple := by
      let : IsSimpleGroup A8 := alternatingGroup.isSimpleGroup (by simp)
      exact ((QuotientGroup.quotientMulEquivOfEq
        (alternatingGroup.center_eq_bot (by simp : 4 ≤ Nat.card (Fin 8)))).trans
          QuotientGroup.quotientBot).isSimpleGroup }
  have hA : IsComponent S8 (alternatingGroup (Fin 8)) :=
    ⟨(inferInstance : (alternatingGroup (Fin 8)).Normal).isSubnormal, inferInstance⟩
  exact hK.eq_of_le hA hle

/-- Transport identifies every component of a group isomorphic to S₈ with A₈. -/
theorem component_equiv_alternating {C : Type*} [Group C] (e : C ≃* S8)
    (K : Subgroup C) (hK : IsComponent C K) : Nonempty (K ≃* A8) := by
  exact ⟨(e.subgroupMap K).trans
    (MulEquiv.subgroupCongr (symmetric_component_eq _ (hK.map_equiv e)))⟩

open Sporadic.LeechRelated.HS Sporadic.LeechRelated.HS.OrderCertificate

set_option maxRecDepth 20000

private theorem stabilizer_common_fixed :
    ∀ x : Fin 100, p2 x = x → p3 x = x → x = 0 := by
  decide +kernel

/-- No nonidentity permutation centralizes the exact degree-100 HS carrier. -/
theorem permutation_centralizer_eq_bot :
    centralizer (generated : Set (Equiv.Perm (Fin 100))) = ⊥ := by
  apply le_antisymm _ bot_le
  intro c hc
  have hcomm (g : Carrier) (x : Fin 100) : g.val (c x) = c (g.val x) :=
    congrArg (fun p : Equiv.Perm (Fin 100) => p x)
      (mem_centralizer_iff.mp hc g.val g.property)
  have hfix (i : Fin 17) : gen1 i (c 0) = c 0 := by
    have hm : gen1 i ∈ H1 := ⟨[i], mul_one _⟩
    have hg : gen1 i ∈ generated := NormalizerIndex.H0_eq_generated ▸ H1_le hm
    exact (hcomm ⟨gen1 i, hg⟩ 0).trans (congrArg c (next0_fix ⟨_, hm⟩))
  have hc0 : c 0 = 0 := stabilizer_common_fixed (c 0) (hfix 0) (hfix 1)
  apply mem_bot.mpr
  apply Equiv.ext
  intro x
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Carrier (0 : Fin 100) x
  change g.val 0 = x at hg
  change c x = x
  rw [← hg, ← hcomm, hc0]

/-- The full permutation normalizer acts faithfully on the exact HS carrier. -/
theorem normalizer_action_injective : Function.Injective generated.normalizerMonoidHom := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [normalizerMonoidHom_ker, permutation_centralizer_eq_bot]
  simp

/-- The actual permutation normalizer is the full abstract automorphism group. -/
noncomputable def fullAutomorphismEquiv :
    normalizer (generated : Set (Equiv.Perm (Fin 100))) ≃* MulAut Carrier :=
  MulEquiv.ofBijective generated.normalizerMonoidHom
    ⟨normalizer_action_injective,
      normalizer_surjective_of_pointStabilizer_map pointStabilizer_map⟩

/-- Fixed points of the induced automorphism are the centralizer inside HS. -/
theorem fixedSubgroup_eq_permutationCentralizer
    (n : normalizer (generated : Set (Equiv.Perm (Fin 100)))) :
    (generated.normalizerMonoidHom n).fixedSubgroup = permutationCentralizer n.val := by
  ext x
  rw [MulAut.mem_fixedSubgroup]
  change (⟨n.val * x.val * n.val⁻¹, _⟩ : Carrier) = x ↔
    x.val ∈ centralizer ({n.val} : Set (Equiv.Perm (Fin 100)))
  rw [Subtype.ext_iff, mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul, eq_comm]

/-- Every abstract outer involution comes from a genuine permutation involution. -/
theorem outer_involution_lift (r : MulAut Carrier) (hr : orderOf r = 2)
    (ho : ¬ ∃ g : Carrier, r = MulAut.conj g) :
    ∃ n : normalizer (generated : Set (Equiv.Perm (Fin 100))),
      generated.normalizerMonoidHom n = r ∧ orderOf n = 2 ∧ n.val ∉ generated := by
  obtain ⟨n, hn⟩ := fullAutomorphismEquiv.surjective r
  refine ⟨n, hn, (fullAutomorphismEquiv.orderOf_eq n).symm.trans (hn ▸ hr), ?_⟩
  intro hmem
  exact ho ⟨⟨n.val, hmem⟩, hn.symm⟩

/-- The S₈ case has the exact index needed for the two-part bound in 16.1.8. -/
theorem index_eq_of_symmetric_fixed (r : MulAut Carrier)
    (h : Nonempty (r.fixedSubgroup ≃* S8)) : r.fixedSubgroup.index = 1100 := by
  obtain ⟨e⟩ := h
  have hc : Nat.card r.fixedSubgroup = 40320 := by
    rw [Nat.card_congr e.toEquiv]
    simp only [S8, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide
  have hi := r.fixedSubgroup.card_mul_index
  rw [hc, NormalizerIndex.card_carrier] at hi
  omega

/-- Once the model alternatives and kernel action are proved, all components
are A₈ and the ambient fixed-subgroup index is divisible by four. -/
theorem component_consequences (r : MulAut Carrier)
    (h : Nonempty (r.fixedSubgroup ≃* S8) ∨
      HasSelfCentralizingNormalTwoSubgroup r.fixedSubgroup)
    (K : Subgroup r.fixedSubgroup) (hK : IsComponent r.fixedSubgroup K) :
    Nonempty (K ≃* A8) ∧ 4 ∣ r.fixedSubgroup.index := by
  rcases h with h | he
  · obtain ⟨e⟩ := h
    refine ⟨component_equiv_alternating e K hK, ?_⟩
    rw [index_eq_of_symmetric_fixed r ⟨e⟩]
    decide
  · exact (he.not_isComponent K hK).elim

/-- An actual group isomorphism transports both the normal kernel and quotient. -/
theorem elementaryExtension_of_equiv {C D : Type*} [Group C] [Group D]
    (e : C ≃* D) (h : IsHSElementaryExtension C) : IsHSElementaryExtension D := by
  obtain ⟨Q, hQn, ⟨eQ⟩, ⟨eR⟩⟩ := h
  let := hQn
  let R := Q.map e.toMonoidHom
  let : R.Normal := hQn.map e.toMonoidHom e.surjective
  refine ⟨R, inferInstance, ⟨(e.subgroupMap Q).symm.trans eQ⟩, ?_⟩
  exact ⟨(QuotientGroup.congr Q R e rfl).symm.trans eR⟩

/-- The normal two-kernel action condition is preserved by actual isomorphisms. -/
theorem selfCentralizingTwoSubgroup_of_equiv {C D : Type*} [Group C] [Group D]
    (e : C ≃* D) (h : HasSelfCentralizingNormalTwoSubgroup C) :
    HasSelfCentralizingNormalTwoSubgroup D := by
  obtain ⟨Q, hQn, hQp, hQc⟩ := h
  let := hQn
  refine ⟨Q.map e.toMonoidHom, hQn.map e.toMonoidHom e.surjective,
    hQp.of_equiv (e.subgroupMap Q), ?_⟩
  intro x hx
  obtain ⟨y, rfl⟩ := e.surjective x
  apply mem_map_of_mem
  apply hQc
  intro z hz
  apply e.injective
  simpa only [map_mul] using hx (e z) (mem_map_of_mem e.toMonoidHom hz)

end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSOuter
