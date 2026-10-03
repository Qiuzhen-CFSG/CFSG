module
public import Stellmacher.Recognition.OddCoreCompletion
public import Theory.ElementaryAbelian.Join
public import Theory.GroupTheory.ElementaryCommutingConnectivity
public import Theory.GroupTheory.ElementaryCommutingNormalFour

/-!
# Proper normalizers from elementary commuting components

In a finite N₂ group, the actual involution odd-core closure is constant
on each commuting component of the elementary binary subgroups of order
at least four. If such a component contains a subgroup A of order at least
eight with nontrivial closure, and the ambient group is nonsolvable and
simple, then the normalizer of this closure is proper. It contains the
normalizer of every subgroup in the component, and every ambient element
whose conjugation carries A into the component.

Commuting elementary subgroups have elementary join. The proved rank-two
restriction theorem identifies each of their closures with the closure of
that join. Induction along the actual commuting chain proves constancy;
naturality under conjugation gives normalizer and component-stabilizer
control. Genuine signalizer completion makes the closure solvable. If its
normalizer were the whole simple group, the nontrivial closure would be the
whole group, contradicting nonsolvability.

A rank-three actor is also connected to every four-group that it
normalizes: its action on the four-group has a kernel of order at least
four. Thus the four-group's full normalizer normalizes the actor's closure,
even when that four-group is not contained in the actor.

This is the elementary connectivity step of GLS2, Definition 10.18,
Proposition 21.8 (k=1), and Section 22, together with the proper-normalizer
argument motivating GLS1 Theorem 31.1. Every step is proved here under the
stated N₂ hypotheses; no K-proper or Z assumption is used. The theorem does
not assert that the given bad-core involution belongs to a rank-three
subgroup, or that the whole Sylow subgroup or weak two-generated core lies
in this component. Those are separate global fusion obligations.
-/

namespace Stellmacher.Recognition

private theorem closure_eq_of_commuting
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (A B : Subgroup G) [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hA : 4 ≤ Nat.card A) (hB : 4 ≤ Nat.card B)
    (hcomm : A ≤ Subgroup.centralizer (B : Set G)) :
    involutionOddCoreClosure A = involutionOddCoreClosure B := by
  let _ : IsElementaryAbelian 2 (A ⊔ B : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer (Subgroup.le_centralizer_iff.mp hcomm)
  exact (oddCoreClosure_eq_of_le hN (A ⊔ B) A le_sup_left hA).symm.trans
    (oddCoreClosure_eq_of_le hN (A ⊔ B) B le_sup_right hB)

private theorem normalizer_closure_lt_top
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hR : involutionOddCoreClosure A ≠ ⊥) :
    Subgroup.normalizer (involutionOddCoreClosure A : Set G) < ⊤ := by
  apply lt_top_iff_ne_top.mpr
  intro htop
  have hnormal := Subgroup.normalizer_eq_top_iff.mp htop
  rcases hnormal.eq_bot_or_eq_top with hbot | hfull
  · exact hR hbot
  · have hsolv := (involutionOddCoreClosure_complete hN A hA).2.1
    rw [hfull] at hsolv
    let _ := hsolv
    exact hns (Group.isSolvable_of_surjective
      (f := (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toMonoidHom)
      Subgroup.topEquiv.surjective)

/-- Actual involution odd-core closures agree throughout each elementary
binary commuting component. -/
public theorem oddCoreClosure_eq_of_connected
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    {A B : Subgroup G} (hAB : Subgroup.ElementaryCommutingConnected 2 A B) :
    involutionOddCoreClosure A = involutionOddCoreClosure B := by
  obtain ⟨_, _, hpath⟩ := hAB
  induction hpath with
  | refl => rfl
  | @tail B C _ hBC ih =>
    obtain ⟨hB, hBcard, hC, hCcard, hcomm⟩ := hBC
    let _ := hB
    let _ := hC
    exact ih.trans (closure_eq_of_commuting hN B C hBcard hCcard hcomm)

/-- A rank-three actor and any four-group that it normalizes have the same
odd-core closure. The four-group need not be contained in the actor. -/
public theorem oddCoreClosure_eq_of_normalizes_four
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (A E : Subgroup G) [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 E]
    (hA : 8 ≤ Nat.card A) (hE : Nat.card E = 4)
    (hAE : A ≤ Subgroup.normalizer (E : Set G)) :
    involutionOddCoreClosure A = involutionOddCoreClosure E :=
  oddCoreClosure_eq_of_connected hN
    (Subgroup.elementaryCommutingConnected_of_normalizes_four A E hA hE hAE)

/-- The normalizer of a four-group normalized by a rank-three actor
normalizes the actor's completed odd-core closure. In particular this
controls a Sylow subgroup once a normal four-group in it is supplied. -/
public theorem normalizer_four_le_normalizer_closure_of_normalizes
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (A E : Subgroup G) [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 E]
    (hA : 8 ≤ Nat.card A) (hE : Nat.card E = 4)
    (hAE : A ≤ Subgroup.normalizer (E : Set G)) :
    Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer (involutionOddCoreClosure A : Set G) := by
  rw [oddCoreClosure_eq_of_normalizes_four hN A E hA hE hAE]
  exact normalizer_le_normalizer_involutionOddCoreClosure E

/-- A nontrivial completed odd core has a proper normalizer that contains
all subgroup normalizers and conjugating elements preserving its component. -/
public theorem oddCore_component_normalizer
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hR : involutionOddCoreClosure A ≠ ⊥) :
    Subgroup.normalizer (involutionOddCoreClosure A : Set G) < ⊤ ∧
      (∀ B : Subgroup G, Subgroup.ElementaryCommutingConnected 2 A B →
        involutionOddCoreClosure A = involutionOddCoreClosure B ∧
        Subgroup.normalizer (B : Set G) ≤
          Subgroup.normalizer (involutionOddCoreClosure A : Set G)) ∧
      ∀ g : G, Subgroup.ElementaryCommutingConnected 2 A
        (A.map (MulAut.conj g).toMonoidHom) →
        g ∈ Subgroup.normalizer (involutionOddCoreClosure A : Set G) := by
  refine ⟨normalizer_closure_lt_top hns hN A hA hR, ?_, ?_⟩
  · intro B hAB
    have heq := oddCoreClosure_eq_of_connected hN hAB
    refine ⟨heq, ?_⟩
    rw [heq]
    exact normalizer_le_normalizer_involutionOddCoreClosure B
  · intro g hg
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    change (involutionOddCoreClosure A).map (MulAut.conj g).toMonoidHom = _
    rw [involutionOddCoreClosure_map]
    exact (oddCoreClosure_eq_of_connected hN hg).symm

end Stellmacher.Recognition
