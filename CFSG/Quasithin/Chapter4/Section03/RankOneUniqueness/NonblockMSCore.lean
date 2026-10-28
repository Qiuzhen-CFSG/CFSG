module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSetup
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockModuleContainment
public import Theory.GroupTheory.PResidual.RelativeCoreCommutator

/-!
# The original nonblock commutator and its crossed copy

Perfectness and relative subnormality identify [O₂(KR),K] and [O₂(KS),K]
with the literal Q=[O₂(K),K]. The intrinsic characteristic layer transported
through K ≤ H ≤ G is the same Q. The source full module W is a proper
subgroup of Q; in particular Q is nonzero and lies in the full Sylow
intersection S.

The crossing-normalizer argument now proves [K,Qᵗ] is not contained in Q,
and consequently Qᵗ is not contained in O₂(KS). These statements require
no block hypothesis or MS classification. They discharge MSData's
commutator_eq clause and supply the source crossing input for the
case-(2) exclusion. Construction of the module markings and final assembly
remain with qt-d-1222-rankone-uniqueness-nonblock.
Source: Aschbacher--Smith, original 4.3.8--10, printed pp.616--617;
A.4.2(2), p.57, and C.1.34, pp.136--137.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
private theorem component_perfect (c : SourceConfiguration T L) : Group.IsPerfect (K c) := by
  let := c.component.perfect
  exact Group.IsPerfect.map c.H.subtype

private theorem component_twoPerfect (c : SourceConfiguration T L) : IsPPerfect 2 (K c) := by
  let := component_perfect c
  intro N hN hq
  let := hN
  have hs : Subsingleton (K c ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (K c ⧸ N) hq.isNilpotent
  apply eq_top_iff.mpr
  intro x _
  exact (QuotientGroup.eq_one_iff x).mp (Subsingleton.elim _ _)

omit [Finite G] in
/-- The original intrinsic commutator layer, through both subtype maps. -/
theorem core_eq_blockLayer (c : SourceConfiguration T L) : Q c = c.blockLayer := by
  change ⁅(K c).pCoreIn 2,K c⁆ =
    ((⁅pCore 2 c.K, (⊤ : Subgroup c.K)⁆).map c.K.subtype).map c.H.subtype
  rw [map_commutator, ←MonoidHom.range_eq_map, range_subtype, map_commutator]
  change ⁅(K c).pCoreIn 2,K c⁆ = ⁅(c.K.pCoreIn 2).map c.H.subtype,K c⁆
  rw [map_pCoreIn_of_injective 2 c.K c.H.subtype c.H.subtype_injective]

/-- The MS-pair commutator on KR is exactly the source Q=[O₂(K),K].
This identification needs neither an MS classification nor a block hypothesis. -/
theorem ms_commutator_eq (c : SourceConfiguration T L) :
    msQ (K c) (c.I.pCoreIn 2) = Q c := by
  have hn : K c ⊔ c.I.pCoreIn 2 ≤ normalizer (K c : Set G) :=
    sup_le (K c).le_normalizer c.block_radical_normalizes
  exact commutator_pCoreIn_eq_intrinsic_of_subnormal _ _ le_sup_left
    (normal_subgroupOf_of_le_normalizer hn).isSubnormal (component_twoPerfect c)

/-- The same intrinsic commutator is obtained from the full Sylow join KS. -/
theorem sylow_join_commutator_eq (c : SourceConfiguration T L) :
    ⁅(K c ⊔ S c).pCoreIn 2,K c⁆ = Q c := by
  have hn : K c ⊔ S c ≤ normalizer (K c : Set G) :=
    sup_le (K c).le_normalizer (inf_le_right.trans c.normalizer_component.le)
  exact commutator_pCoreIn_eq_intrinsic_of_subnormal _ _ le_sup_left
    (normal_subgroupOf_of_le_normalizer hn).isSubnormal (component_twoPerfect c)

/-- The full source module is a nonzero proper subgroup of the actual Q. -/
theorem fullModule_lt_core (c : SourceConfiguration T L)
    (hf : generalizedFitting c.K = pCore 2 c.K) : W c < Q c := by
  rw [core_eq_blockLayer]
  exact c.fullModule_lt_blockLayer hf

/-- The original core lies in the full Sylow intersection. -/
theorem core_le_sylow (c : SourceConfiguration T L) : Q c ≤ S c := by
  rw [core_eq_blockLayer]
  exact c.blockLayer_le_sylow

omit [Finite G] in
/-- H normalizes the original Q without a block assumption. -/
theorem core_normalized (c : SourceConfiguration T L) :
    c.H ≤ normalizer (Q c : Set G) := by
  rw [core_eq_blockLayer]
  exact c.blockLayer_normalized

/-- The crossed source core cannot absorb all its K-commutators. -/
theorem crossing_core_commutator_not_le (c : SourceConfiguration T L)
    (hf : generalizedFitting c.K = pCore 2 c.K) :
    ¬ ⁅K c,(Q c).map (MulAut.conj c.t⁻¹).toMonoidHom⁆ ≤ Q c := by
  apply c.crossing_commutator_not_le (core_le_sylow c) _ (core_normalized c)
  intro he
  exact c.c28.module_nontrivial (bot_unique ((fullModule_lt_core c hf).le.trans he.le))

/-- The crossing takes Q outside O₂(KS), also in the nonblock branch. -/
theorem crossing_core_not_le_join_core (c : SourceConfiguration T L)
    (hf : generalizedFitting c.K = pCore 2 c.K) :
    ¬ (Q c).map (MulAut.conj c.t⁻¹).toMonoidHom ≤ (K c ⊔ S c).pCoreIn 2 := by
  intro hh
  apply crossing_core_commutator_not_le c hf
  rw [commutator_comm]
  exact (commutator_mono hh le_rfl).trans_eq (sylow_join_commutator_eq c)

omit [Finite G] in
/-- The actual source crossing transports a full-module commutator identity
on Q without identifying the Chapter 12 chosen module with W. -/
theorem crossing_core_fullModule (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V) (hu : ⁅Q c,L⁆ = W c) :
    ⁅(Q c).map (MulAut.conj c.t⁻¹).toMonoidHom,L⁆ = W c := by
  rw [core_eq_blockLayer] at hu ⊢
  exact c.block_crossing_commutator_fullModule D hu
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
