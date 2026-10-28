module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.FactorAlternatives.InternalRigidity.Transport
public import BenderSuzuki.ZD.ProductClosedCentralFactor.ModelGeometry.Fusion
public import BenderSuzuki.Converse.PSL2
public import Theory.SpecificGroups.SL2.SylowConsequences
public import Theory.GroupTheory.SylowCoprimeEquivalence

/-!
# Terminal-factor rigidity in the binary linear model

The defining-characteristic Sylow subgroup of SL₂ is the additive field.
The actual projective quotient has trivial kernel in characteristic two,
so every element of a Sylow two-subgroup of PSL₂ has square one. Strong
embedding gives a single involution class. Thus a strongly closed union
containing an involution covers the whole Sylow subgroup. A subgroup
contained in a union of two subgroups is contained in one of them, which
proves nesting of the factors.

This is the PSL₂ case needed in the terminal step of Aschbacher (1975),
Lemma 3.4, pp.94–96. It uses the concrete matrix model, the Sylow equivalence
in `Theory.SpecificGroups.SL2.SylowConsequences`, and the proved converse
to Peterfalvi's Hypothesis (A) for that model.
-/

@[expose] public section

open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1 BenderSuzuki.PFAppendixIII
open BenderSuzuki.MatrixGroups BenderSuzuki.Converse

namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75.InternalRigidity

/-- Commuting Sylow factors with strongly closed union nest in PSL₂(2ⁿ). -/
theorem linear_rigidity (n : ℕ) (hn : 2 ≤ n) :
    SylowFactorRigidity (PSL2BinaryMatrixGroup n) := by
  let K := BinaryGaloisField n
  let q := pi K
  have hker : Nat.Coprime 2 (Nat.card q.ker) := by
    rw [(MonoidHom.ker_eq_bot_iff q).mpr pi_injective, card_bot]
    exact Nat.coprime_one_right _
  have hsq : ∀ (P : Sylow 2 (PSL2BinaryMatrixGroup n)) (x : P), x ^ 2 = 1 := by
    intro P x
    let U := Matrix.SpecialLinearGroup.upperUnipotentSylow K 2
    let e : Multiplicative K ≃* P :=
      (Matrix.SpecialLinearGroup.sylowEquivAdditive K 2 U).trans
        (Sylow.equivOfSurjectiveCoprime q pi_surjective hker U P)
    apply e.symm.injective
    rw [map_pow, map_one, pow_two]
    apply Multiplicative.toAdd.injective
    change (e.symm x).toAdd + (e.symm x).toAdd = 0
    exact CharTwo.add_self_eq_zero _
  intro P B C hBP hCP _hBC hB _hC hc
  have hBne : B ≠ ⊥ := by
    obtain ⟨E, hE, _⟩ := hB
    have hh := card_le_card_group E
    rw [hE] at hh
    intro he
    rw [he] at hh
    simp at hh
  obtain ⟨a, hane⟩ := ne_bot_iff_exists_ne_one.mp hBne
  have ha : IsInvolution (a : PSL2BinaryMatrixGroup n) := by
    refine ⟨fun he => hane (Subtype.ext he), ?_⟩
    exact congrArg (fun t : P => (t : PSL2BinaryMatrixGroup n))
      (hsq P ⟨a, hBP a.property⟩)
  have hcover : (P : Set (PSL2BinaryMatrixGroup n)) ⊆ (B : Set _) ∪ C := by
    intro x hx
    by_cases he : x = 1
    · subst x; exact Or.inl B.one_mem
    have hi : IsInvolution x := ⟨he, congrArg (fun t : P => (t : PSL2BinaryMatrixGroup n))
      (hsq P ⟨x, hx⟩)⟩
    obtain ⟨g, hg⟩ := (hypothesisA_PSL2_binary n hn).A1.isStronglyEmbedded.involutions_conjugate ha hi
    change g⁻¹ * (a : PSL2BinaryMatrixGroup n) * g = x at hg
    have hh := hc.2 a (Or.inl a.property) g (mem_top _) (hg.symm ▸ hx)
    rwa [hg] at hh
  rcases (SubgroupClass.subset_union (H := (P : Subgroup _)) (K := B) (L := C)).mp
      hcover with hh | hh
  · exact Or.inr (hCP.trans hh)
  · exact Or.inl (hBP.trans hh)

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75.InternalRigidity

end
