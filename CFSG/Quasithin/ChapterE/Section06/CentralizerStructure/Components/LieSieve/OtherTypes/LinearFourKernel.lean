module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.Setup
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.BinaryAction

/-!
# The action kernel in the binary component extension

For a component L of C_G(U), put Q = C_T(V). The fixed subgroup
C_V(L) is central in LQ and is a two-group, so it lies in O₂(LQ).
Conversely the two-core centralizes the component, by the component
normal-subgroup dichotomy. Hence C_V(L) = V ∩ O₂(LQ), with the
core computed inside the actual generated subgroup and embedded in G.

The residual condition in Definition E.6.4 passes to C_V(L), and the
component restricts to its centralizer. For PSL₄(2) and PSL₅(2), the binary
action calculation makes this subgroup an obstruction hyperplane. The ambient
fixed-point constraint then makes C_V(T) an order-two direct complement.
The residual also identifies C_T(U) with C_T(V), without a dimension claim
about U.

These reductions do not identify the original U with that hyperplane.
Even when (LQ)/O₂(LQ) is S₈, the reverse containment
V ∩ O₂(LQ) ≤ U remains to be proved from the ambient hypotheses.
No maximality of U is assumed here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Definition
E.6.4 and E.6.8(3), printed pp.245, 247–248 (PDF pp.256, 258–259).
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.LinearFourKernel
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U Q L : Subgroup G}

private theorem core_centralizes_component {E : Subgroup G}
    (hL : ComponentIn E L) : E.pCoreIn 2 ≤ centralizer (L : Set G) := by
  rcases hL.2.normal_dichotomy (pCore 2 E) with hle | hc
  · let _ := hL.2.2
    let _ : IsSimpleGroup ((L.subgroupOf E) ⧸ center (L.subgroupOf E)) :=
      IsQuasisimple.simple
    let _ : Nontrivial (L.subgroupOf E) :=
      (QuotientGroup.mk'_surjective (center (L.subgroupOf E))).nontrivial
    let _ := (pCore_isPGroup.to_le hle).isNilpotent
    exact (Group.IsPerfect.not_isSolvable (L.subgroupOf E) inferInstance).elim
  · have hh := congrArg (Subgroup.map E.subtype) hc
    rw [map_commutator, map_subgroupOf_eq_of_le hL.1, commutator_comm,
      Subgroup.map_bot] at hh
    exact commutator_eq_bot_iff_le_centralizer.mp hh

/-- The full action kernel is precisely the part of V killed by the
two-core quotient. This retains the actual embedding of the core in G. -/
theorem fixedSpace_eq_inf_core (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V) :
    V ⊓ centralizer (L : Set G) = V ⊓ (L ⊔ Q).pCoreIn 2 := by
  let W := V ⊓ centralizer (L : Set G)
  have hVE : V ≤ L ⊔ Q := (hQ ▸ h.le_sylowCentralizer).trans le_sup_right
  have hE : L ⊔ Q ≤ centralizer (U : Set G) := by
    exact sup_le hL.1 ((show Q ≤ centralizer (V : Set G) from hQ ▸ inf_le_right).trans
      (Subgroup.centralizer_le hU.1))
  have hLE : ComponentIn (L ⊔ Q) L :=
    IsComponentIn.restrict hL le_sup_left hE
  have hEW : L ⊔ Q ≤ centralizer (W : Set G) := by
    apply sup_le
    · exact le_centralizer_iff.mp (show W ≤ centralizer (L : Set G) from inf_le_right)
    · exact (show Q ≤ centralizer (V : Set G) from hQ ▸ inf_le_right).trans
        (Subgroup.centralizer_le inf_le_left)
  have hWp : IsPGroup 2 W := by
    let _ := h.elementary
    exact (IsElementaryAbelian.isPGroup 2 V).to_le inf_le_left
  have hWcore : W ≤ (L ⊔ Q).pCoreIn 2 :=
    le_pCoreIn_of_normalizes hWp (inf_le_left.trans hVE)
      (hEW.trans (Subgroup.centralizer_le_normalizer _))
  exact le_antisymm (le_inf inf_le_left hWcore)
    (inf_le_inf_left V (core_centralizes_component hLE))

/-- Saturating U to the actual action kernel preserves all four clauses
of the obstruction family, including the odd-index residual condition. -/
theorem fixedSpace_mem_obstruction (h : HypothesisE61 K T M V)
    (earlier : EarlierLocalFacts T) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L) :
    V ⊓ centralizer (L : Set G) ∈ obstructionFamily M V := by
  have hUW := fixedSpace_contains hU.1 hL.1
  refine ⟨inf_le_left, ?_, ?_, ?_⟩
  · intro he
    exact hU.2.1 (le_bot_iff.mp (he ▸ hUW))
  · exact fun he => component_not_le h earlier hU hL
      ((le_centralizer_iff.mp inf_le_right).trans he)
  · exact InvariantSubspaces.oddCentralizerCondition_mono hUW hU.2.2.2

omit [Finite G] in
/-- The ordinary component remains a component of the kernel centralizer;
subnormality is restricted to this intermediate overgroup. -/
theorem component_in_fixedSpace (hU : U ≤ V)
    (hL : ComponentIn (centralizer (U : Set G)) L) :
    ComponentIn (centralizer (V ⊓ centralizer (L : Set G) : Set G)) L := by
  exact IsComponentIn.restrict hL (le_centralizer_iff.mp inf_le_right)
    (Subgroup.centralizer_le (fixedSpace_contains hU hL.1))

/-- The intersection with the actual two-core is an obstruction hyperplane
in both binary higher-linear models. This does not assert that it equals U. -/
theorem binary_kernel_hyperplane (h : HypothesisE61 K T M V)
    (earlier : EarlierLocalFacts T) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    {n : ℕ} (hn : n = 4 ∨ n = 5) (hm : ClassicalGroup.IsPSL L n 2)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V) :
    V ⊓ (L ⊔ Q).pCoreIn 2 ∈ obstructionFamily M V ∧
      subgroupCorank V (V ⊓ (L ⊔ Q).pCoreIn 2) = 1 ∧
      globalR V = 1 := by
  rw [← fixedSpace_eq_inf_core h hU hL hQ]
  exact ⟨fixedSpace_mem_obstruction h earlier hU hL,
    binary_component_rank_one h earlier hU hL hn hm⟩

/-- The odd-index residual condition already forces the pointwise stabilizer
of U in T to equal the pointwise stabilizer of all of V. -/
theorem obstruction_sylow_centralizer (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V) :
    (T : Subgroup G) ⊓ centralizer (U : Set G) =
      sylowCentralizer (T : Subgroup G) V := by
  apply le_antisymm
  · exact le_inf inf_le_left (hU.2.2.2.two_subgroup_centralizes
      (T.isPGroup'.to_le inf_le_left)
      (le_inf (inf_le_left.trans h.sylow_le) inf_le_right))
  · exact inf_le_inf_left _ (Subgroup.centralizer_le hU.1)

/-- The full component kernel has the Sylow-fixed involution as an internal
direct complement. This does not identify the original U with that kernel. -/
theorem fixed_decomposition_of_actionCorank_one (h : HypothesisE61 K T M V)
    (earlier : EarlierLocalFacts T) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hrank : actionCorank V L = 1) :
    Nat.card (sylowFixedSpace (T : Subgroup G) V) = 2 ∧
      V = (V ⊓ centralizer (L : Set G)) ⊔ sylowFixedSpace (T : Subgroup G) V ∧
      Disjoint (V ⊓ centralizer (L : Set G)) (sylowFixedSpace (T : Subgroup G) V) := by
  let _ := h.elementary
  let W := V ⊓ centralizer (L : Set G)
  let Z := sylowFixedSpace (T : Subgroup G) V
  have hWV : W ≤ V := inf_le_left
  have hZV : Z ≤ V := inf_le_left
  have hd : W ⊓ Z = ⊥ := component_fixedSpace_disjoint_sylowFixed h earlier hU hL
  have hi : W.relIndex V = 2 := by
    rw [V.relIndex_eq_two_pow_quotient_finrank,
      ← subgroupCorank_eq_quotient_finrank]
    change 2 ^ actionCorank V L = 2
    rw [hrank]
    rfl
  have hc : Nat.card Z ≤ 2 := by
    have hb := Subgroup.relIndex_le_of_le_right (H := W) hZV (hi ▸ by decide)
    rw [← inf_relIndex_right W Z, hd, relIndex_bot_left, hi] at hb
    exact hb
  have hz : Z ≠ ⊥ := by
    obtain ⟨z, hz, hne⟩ := exists_sylow_fixed h
    intro he
    exact hne (mem_bot.mp (he ▸ hz))
  have hcard : Nat.card Z = 2 := by
    have := (Subgroup.one_lt_card_iff_ne_bot Z).mpr hz
    omega
  have hdis : Disjoint W Z := disjoint_iff.mpr hd
  have hnz : Z ≤ normalizer (W : Set G) :=
    (hZV.trans (V.le_centralizer.trans (Subgroup.centralizer_le hWV))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hvcard : Nat.card W * 2 = Nat.card V := by
    simpa only [relIndex_bot_left, hi] using
      (relIndex_mul_relIndex (⊥ : Subgroup G) W V bot_le hWV)
  have he : W ⊔ Z = V := by
    apply eq_of_le_of_card_ge (sup_le hWV hZV)
    rw [card_sup_eq_mul_of_normalizes_of_disjoint W Z hnz hdis, hcard, hvcard]
  exact ⟨hcard, he.symm, hdis⟩

end CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.LinearFourKernel
