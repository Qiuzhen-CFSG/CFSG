module

public import Theory.GroupAction.PTimesQ

/-!
# Odd commuting actors when a two-group has a fixed line

If a two-group actor has exactly two fixed elements on a finite elementary
abelian two-group, every commuting odd-order actor is trivial. Commutation
preserves the fixed subgroup, and every automorphism of a group of order
two is the identity. The `P × Q` lemma then extends this trivial action to
the whole module.

This is the odd-centralizer reduction used to justify the invariant
sixteen-element module in Stellmacher (1.6), journal p.18, following
`refs/latex/stellmacher-n-group.tex`.
-/

universe u

public theorem odd_commuting_subgroup_fixes_all_of_fixed_card_two
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (S C : Subgroup G) (hS : IsPGroup 2 S)
    (hC : Nat.Coprime 2 (Nat.card C)) (hSC : ⁅S, C⁆ = ⊥)
    (hfixed : Nat.card (FixedPoints.subgroup S V) = 2) :
    C ≤ fixingSubgroup G (Set.univ : Set V) := by
  apply p_times_q_lemma S C hS hC hSC
  let T := FixedPoints.subgroup S V
  obtain ⟨a, _hane, huniq⟩ := (Nat.card_eq_two_iff' (1 : T)).mp hfixed
  intro c hc
  rw [mem_fixingSubgroup_iff]
  intro v hv
  have hcv : c • v ∈ T := by
    intro s
    have hsc : c * (s : G) = (s : G) * c :=
      Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hSC s.property) c hc
    change (s : G) • (c • v) = c • v
    rw [← mul_smul, ← hsc, mul_smul, show (s : G) • v = v from hv s]
  by_cases hvone : v = 1
  · simp [hvone]
  · have hcvne : c • v ≠ 1 := by
      intro heq
      apply hvone
      have hh := congrArg (fun z : V => c⁻¹ • z) heq
      simpa using hh
    have heq := (huniq (⟨c • v, hcv⟩ : T) (fun h => hcvne (congrArg Subtype.val h))).trans
      (huniq (⟨v, hv⟩ : T) (fun h => hvone (congrArg Subtype.val h))).symm
    exact congrArg Subtype.val heq

