module
public import Theory.SpecificGroups.Alternating.SevenFiveRestriction

/-!
# Compatible two-point marking of a Sylow-normalized A₅ in A₇

The existing placement theorem identifies the actual A₅ as the pointwise
fixer of its two fixed letters. Normalization preserves that pair, and the
maximality of the join with a full Sylow two-subgroup identifies the join
with the setwise stabilizer of the same pair. Both markings use the same
seven-point action.

Source application: Aschbacher–Smith 5.2.11(1), printed pp.653–654
(`refs/quasithin.pdf`).
-/

public section
open Subgroup MulAction
open scoped Pointwise
namespace Theory.GroupTheory.QuasithinM23

/-- Both the five-subgroup and its Sylow extension in one seven-point marking. -/
theorem five_and_sylow_pair
    (B : Subgroup (alternatingGroup (Fin 7)))
    (e : B ≃* alternatingGroup (Fin 5)) (S : Sylow 2 (alternatingGroup (Fin 7)))
    (hSN : (S : Subgroup (alternatingGroup (Fin 7))) ≤ normalizer (B : Set _)) :
    ∃ i j : Fin 7, i ≠ j ∧
      B = fixingSubgroup (alternatingGroup (Fin 7)) ({i,j} : Set (Fin 7)) ∧
      B ⊔ (S : Subgroup (alternatingGroup (Fin 7))) =
        stabilizer (alternatingGroup (Fin 7)) ({i,j} : Set (Fin 7)) := by
  classical
  obtain ⟨i,j,hij,hB⟩ := SpecificGroups.Alternating.SevenFivePlacement.exists_fixed_pair B e S hSN
  have hfix : fixedPoints B (Fin 7) = {i,j} := by
    have hle : ({i,j} : Set (Fin 7)) ⊆ fixedPoints B (Fin 7) := by
      intro x hx b
      have hb : b.val ∈ fixingSubgroup (alternatingGroup (Fin 7)) ({i,j} : Set (Fin 7)) := hB ▸ b.property
      exact hb ⟨x,hx⟩
    exact (Set.eq_of_subset_of_ncard_le hle (by
      rw [SpecificGroups.Alternating.SevenFivePlacement.fixed_card_two B e S hSN,
        Set.ncard_pair hij])).symm
  have hn : normalizer (B : Set _) ≤
      stabilizer (alternatingGroup (Fin 7)) ({i,j} : Set (Fin 7)) := by
    intro g hg
    apply (mem_stabilizer_set' (Set.toFinite _)).mpr
    intro x hx
    rw [← hfix] at hx ⊢
    intro b
    have hb := (mem_normalizer_iff''.mp hg b.val).mp b.property
    have hbx := hx ⟨g⁻¹ * b.val * g,hb⟩
    change (g⁻¹ * b.val * g) • x = x at hbx
    have hh := congrArg (fun y : Fin 7 => g • y) hbx
    change b.val • (g • x) = g • x
    simpa only [smul_smul, mul_inv_cancel_left, mul_assoc] using hh
  have hle := sup_le (B.le_normalizer.trans hn) (hSN.trans hn)
  have hm := SpecificGroups.Alternating.SevenFivePlacement.sylow_sup_five_isCoatom B e S hSN
  have hproper : stabilizer (alternatingGroup (Fin 7)) ({i,j} : Set (Fin 7)) ≠ ⊤ := by
    apply (alternatingGroup.isCoatom_stabilizer_of_ncard_lt_ncard_compl ?_ ?_).1
    · exact ⟨i,by simp,j,by simp,hij⟩
    · have hc := Set.ncard_add_ncard_compl ({i,j} : Set (Fin 7))
      rw [Set.ncard_pair hij,Nat.card_fin] at hc
      rw [Set.ncard_pair hij]
      omega
  refine ⟨i,j,hij,hB,?_⟩
  exact (lt_or_eq_of_le hle).resolve_left (fun hlt => hproper (hm.2 _ hlt))

end Theory.GroupTheory.QuasithinM23
