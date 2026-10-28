module

public import Theory.Representation.IrreducibleTraceEquivalence
public import Theory.Representation.SubrepresentationLattice

/-!
# Constituent support from trace and dimension

Distinct simple characters are linearly independent, even in positive
characteristic. Equality with a multiplicity-free sum therefore forces each
specified simple to occur at least once: its coefficient in the field is one.
Choose one occurrence of each. Equal natural dimension sums and positivity of
every simple dimension force this injection of factor sets to be surjective.
Thus no additional factor, including a multiple of the characteristic, remains.

This argument compares composition factors; it does not assert that equality
of traces determines arbitrary representations or extension classes.

Source: Feit, *The Representation Theory of Finite Groups*, I.17 and the
simple-submodule step of VII.2.25, printed p.304.
-/

public section
noncomputable section
open scoped BigOperators Classical

universe u v
namespace Representation.CompositionSeriesTrace
variable {K : Type u} {G : Type v} [Field K] [IsAlgClosed K] [Group G]

private abbrev SimpleCharacter := {χ : G → K //
  ∃ M : FDRep K G, IsIrreducible M.ρ ∧ character M.ρ = χ}

private def simpleChar (M : FDRep K G) (h : IsIrreducible M.ρ) : SimpleCharacter (K := K) (G := G) :=
  ⟨character M.ρ, M, h, rfl⟩

private theorem simpleChar_independent :
    LinearIndependent K (fun c : SimpleCharacter (K := K) (G := G) => c.val) := by
  apply linearIndependent_iff_finset_linearIndependent.mpr
  intro s
  choose M hM hchar using fun c : s => c.val.property
  let (c : s) : IsIrreducible (M c).ρ := hM c
  have hne : Pairwise fun c d : s => IsEmpty (Equiv (M c).ρ (M d).ρ) := by
    intro c d hcd
    refine ⟨fun e => hcd ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact (hchar c).symm.trans ((char_iso e).trans (hchar d))
  have hi := linearIndependent_characters_of_pairwise_inequivalent
    (fun c : s => ↥(M c)) (fun c => (M c).ρ) hne
  change LinearIndependent K (fun c : s => c.val.val)
  simpa only [hchar] using hi

/-- If a sum of simple trace characters equals a multiplicity-free sum and the
natural dimension sums agree, every simple on the first side occurs on the
second. This holds in arbitrary characteristic. -/
theorem support_of_equal_sums {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : ι → FDRep K G) (N : κ → FDRep K G)
    (hM : ∀ i, IsIrreducible (M i).ρ) (hN : ∀ j, IsIrreducible (N j).ρ)
    (hne : Pairwise fun i j => IsEmpty (Equiv (N i).ρ (N j).ρ))
    (hc : ∑ i, character (M i).ρ = ∑ j, character (N j).ρ)
    (hd : ∑ i, Module.finrank K (M i) = ∑ j, Module.finrank K (N j)) :
    ∀ i, ∃ j, Nonempty (Equiv (M i).ρ (N j).ρ) := by
  let (i : ι) : IsIrreducible (M i).ρ := hM i
  let (j : κ) : IsIrreducible (N j).ρ := hN j
  let cm := fun i => simpleChar (M i) (hM i)
  let cn := fun j => simpleChar (N j) (hN j)
  have hn : Function.Injective cn := by
    intro i j hij
    by_contra hneij
    obtain ⟨e⟩ := (character_eq_iff_equiv_of_irreducible (N i).ρ (N j).ρ).mp
      (congrArg Subtype.val hij)
    exact (hne hneij).false e
  have hcoeff : (∑ i, Finsupp.single (cm i) (1 : K)) =
      ∑ j, Finsupp.single (cn j) (1 : K) := by
    apply simpleChar_independent.finsuppLinearCombination_injective
    simpa only [map_sum, Finsupp.linearCombination_single, one_smul, cm, cn, simpleChar] using hc
  have hocc (j : κ) : ∃ i, cm i = cn j := by
    by_contra! hnone
    have he := congrArg (fun f : SimpleCharacter (K := K) (G := G) →₀ K => f (cn j)) hcoeff
    have hleft : (∑ i, Finsupp.single (cm i) (1 : K)) (cn j) = 0 := by
      simp only [Finsupp.finsetSum_apply]
      exact Finset.sum_eq_zero fun i _ => Finsupp.single_eq_of_ne (hnone i).symm
    have hright : (∑ k, Finsupp.single (cn k) (1 : K)) (cn j) = 1 := by
      simp only [Finsupp.finsetSum_apply, Finsupp.single_apply, hn.eq_iff]
      simp
    rw [hleft, hright] at he
    exact zero_ne_one he
  choose f hf using hocc
  have hf_inj : Function.Injective f := by
    intro i j hij
    apply hn
    rw [← hf i, ← hf j, hij]
  have hequiv (j : κ) : Nonempty (Equiv (M (f j)).ρ (N j).ρ) :=
    (character_eq_iff_equiv_of_irreducible _ _).mp (congrArg Subtype.val (hf j))
  have hdim (j : κ) : Module.finrank K (M (f j)) = Module.finrank K (N j) :=
    (Classical.choice (hequiv j)).toLinearEquiv.finrank_eq
  have hsurj : Function.Surjective f := by
    intro i
    by_contra hi
    have him : i ∉ Finset.univ.image f := by simpa using hi
    have : Nontrivial (M i) := Subrepresentation.irreducible_module_nontrivial (M i).ρ
    have hlt := Finset.sum_lt_sum_of_subset (Finset.subset_univ (Finset.univ.image f))
      (Finset.mem_univ i) him (Module.finrank_pos (R := K) (M := M i))
      (fun j _ _ => Nat.zero_le (Module.finrank K (M j)))
    rw [Finset.sum_image (fun a _ b _ h => hf_inj h)] at hlt
    simp_rw [hdim] at hlt
    omega
  intro i
  obtain ⟨j, rfl⟩ := hsurj i
  exact ⟨j, hequiv j⟩
end Representation.CompositionSeriesTrace
