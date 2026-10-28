module

public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTwoQuotient
public import Theory.GroupTheory.CComponent.SimpleNormalCentralizer

/-!
# Simple normal subgroups with a two-group quotient

If a finite group has trivial two-core and a nonabelian simple normal subgroup
with two-group quotient, that subgroup is the generalized Fitting subgroup and
is contained in every nontrivial normal subgroup. Its centralizer embeds in the
two-group quotient, so is a normal two-subgroup and hence trivial. The simple
normal-subgroup dichotomy then proves the last assertion.

This supplies the faithful-section argument following Aschbacher–Smith,
*The Classification of Quasithin Groups*, Lemma 13.8.21, printed p.957
(combined manuscript, 1 March 2004). No classification of the simple subgroup
is used here.
-/

public section

namespace Theory.GroupTheory
open Subgroup
variable {G : Type*} [Group G] [Finite G]

private theorem simple_center_eq_bot {S : Type*} [Group S] [IsSimpleGroup S]
    (ha : ¬ IsMulCommutative S) : center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center S) inferInstance with h | h
  · exact h
  · exact (ha (center_eq_top_iff.mp h)).elim

omit [Finite G] in
/-- The centralizer embeds in the two-group quotient and is killed by the
trivial two-core. Normality is in the group `G` under consideration. -/
theorem centralizer_eq_bot_of_simple_two_quotient
    (K : Subgroup G) [K.Normal] [IsSimpleGroup K]
    (ha : ¬ IsMulCommutative K) (hquot : IsPGroup 2 (G ⧸ K))
    (hcore : pCore 2 G = ⊥) : centralizer (K : Set G) = ⊥ := by
  have hz : center K = ⊥ := simple_center_eq_bot ha
  let C := centralizer (K : Set G)
  let f : C →* G ⧸ K := (QuotientGroup.mk' K).comp C.subtype
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply le_bot_iff.mp
    intro x hx
    have hxK : (x : G) ∈ K := (QuotientGroup.eq_one_iff _).mp hx
    have hxZ : (⟨x, hxK⟩ : K) ∈ center K := by
      rw [mem_center_iff]
      intro k
      exact Subtype.ext ((mem_centralizer_iff.mp x.property) k k.property)
    rw [hz, mem_bot] at hxZ
    exact Subtype.ext (congrArg (fun k : K => (k : G)) hxZ)
  have hC : IsPGroup 2 C := hquot.of_injective f hf
  have hle : C ≤ pCore 2 G := le_sSup ⟨inferInstance, hC⟩
  exact le_bot_iff.mp (hle.trans hcore.le)

/-- The generalized Fitting subgroup and normal-subgroup consequence needed
for faithful actions on sections of a binary module. -/
theorem simple_two_quotient_structure
    (K : Subgroup G) [K.Normal] [IsSimpleGroup K]
    (ha : ¬ IsMulCommutative K) (hquot : IsPGroup 2 (G ⧸ K))
    (hcore : pCore 2 G = ⊥) :
    generalizedFitting G = K ∧ centralizer (K : Set G) = ⊥ ∧
      ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → K ≤ N := by
  have hz : center K = ⊥ := simple_center_eq_bot ha
  let : Group.IsPerfect K := ⟨
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (_root_.commutator K)
      inferInstance).resolve_left (fun h => ha ((commutator_eq_bot_iff K).mp h))⟩
  let : IsQuasisimple K := ⟨
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup⟩
  have hC := centralizer_eq_bot_of_simple_two_quotient K ha hquot hcore
  refine ⟨generalizedFitting_eq_of_quasisimple_two_quotient K hquot hcore, hC, ?_⟩
  intro N hN hn
  exact simple_normal_le_of_normal_ne_bot_of_centralizer_eq_bot K ha hC N hn

end Theory.GroupTheory
