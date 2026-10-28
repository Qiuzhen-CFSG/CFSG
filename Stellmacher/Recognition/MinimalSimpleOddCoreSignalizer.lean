module

public import Stellmacher.Recognition.MinimalSimpleOddCoreRankThree
public import Stellmacher.Recognition.OddCoreWeakSylow
public import Theory.GroupTheory.MaximalPPrimeSignalizer

/-!
# Signalizer absorption and maximal overgroups of the odd-core closure

A nonzero rank-three odd-core closure supplies a maximal solvable overgroup
with nontrivial odd core and the existing weak-core normalizer control.
Absorption of every invariant odd subgroup, together with an escaping
normalizer, then forces the closure to vanish. Absorption remains an explicit
hypothesis; solvability alone does not supply it.

Source: the Bender and signalizer arguments of GLS2, Chapter F, §§19,21–22,
and GLS4, Chapter 2, Lemmas19.3(c)–19.4. These are conditional applications
of the general conjugation/maximality result in MaximalPPrimeSignalizer.
-/

namespace Stellmacher.Recognition
open Theory.GroupTheory

/-- A nonzero closure supplies a maximal solvable overgroup with nontrivial
odd core, component-stabilizer control, and elementary weak-core control. -/
public theorem minimalSimple_oddCore_maximal_weak_core_obstruction
    {G : Type*} [Group G] [Finite G] (hG : IsMinimalSimple G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hR : involutionOddCoreClosure A ≠ ⊥) (S : Sylow 2 G) (hAS : A ≤ S) :
    ∃ M : Subgroup G, IsCoatom M ∧ Group.IsSolvable M ∧
      (S : Subgroup G) ≤ M ∧ pPrimeCore 2 M ≠ ⊥ ∧
      Subgroup.normalizer (involutionOddCoreClosure A : Set G) ≤ M ∧
      (∀ g : G, Subgroup.ElementaryCommutingConnected 2 A
        (A.map (MulAut.conj g).toMonoidHom) → g ∈ M) ∧
      ∀ E B : Subgroup G, IsElementaryAbelian 2 E → 4 ≤ Nat.card E → E ≤ S →
        IsElementaryAbelian 2 B → 8 ≤ Nat.card B →
        B ≤ (S : Subgroup G) ⊓ Subgroup.centralizer (E : Set G) →
        Subgroup.normalizer (E : Set G) ≤ M := by
  let _ := hG.isSimpleGroup
  obtain ⟨M, hM, hsolv, hNM, hRO, -⟩ :=
    minimalSimple_oddCore_maximal_overgroup hG A hA hR
  refine ⟨M, hM, hsolv,
    (sylow_le_normalizer_oddCoreClosure hG.isNTwoGroup S A hAS hA).trans hNM,
    ?_, hNM, ?_, ?_⟩
  · intro hbot
    rw [hbot, Subgroup.map_bot] at hRO
    exact hR (bot_unique hRO)
  · intro g hg
    exact hNM ((oddCore_component_normalizer
      hG.not_isSolvable hG.isNTwoGroup A hA hR).2.2 g hg)
  · intro E B hE hE4 hES hB hB8 hBC
    let : IsElementaryAbelian 2 E := hE
    let : IsElementaryAbelian 2 B := hB
    exact (normalizer_le_normalizer_oddCoreClosure_of_weak_rank
      hG.not_isSolvable hG.isNTwoGroup S A E E B hAS hA hES le_rfl hE4
      (hBC.trans le_sup_right) hB8).trans hNM

/-- Odd-core elimination for maximal solvable subgroups with component and
weak-core control suffices for closure vanishing. Elimination is an explicit input. -/
public theorem minimalSimple_oddCore_eq_bot_of_solvable_weak_core
    {G : Type*} [Group G] [Finite G] (hG : IsMinimalSimple G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hcore : ∀ (S : Sylow 2 G), A ≤ S → ∀ M : Subgroup G,
      IsCoatom M → Group.IsSolvable M → (S : Subgroup G) ≤ M →
      (∀ g : G, Subgroup.ElementaryCommutingConnected 2 A
        (A.map (MulAut.conj g).toMonoidHom) → g ∈ M) →
      (∀ E B : Subgroup G, IsElementaryAbelian 2 E → 4 ≤ Nat.card E → E ≤ S →
        IsElementaryAbelian 2 B → 8 ≤ Nat.card B →
        B ≤ (S : Subgroup G) ⊓ Subgroup.centralizer (E : Set G) →
        Subgroup.normalizer (E : Set G) ≤ M) → pPrimeCore 2 M = ⊥) :
    involutionOddCoreClosure A = ⊥ := by
  by_contra hR
  obtain ⟨S, hAS⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨M, hM, hsolv, hSM, hodd, -, hcomponent, hweak⟩ :=
    minimalSimple_oddCore_maximal_weak_core_obstruction hG A hA hR S hAS
  exact hodd (hcore S hAS M hM hsolv hSM hcomponent hweak)

/-- An escaping normalizer and absorption of its invariant odd subgroups
eliminate the closure. Minimal simplicity supplies solvability of the overgroup. -/
public theorem minimalSimple_oddCore_eq_bot_of_signalizer_absorption
    {G : Type*} [Group G] [Finite G] (hG : IsMinimalSimple G)
    (A M Q : Subgroup G) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hM : IsCoatom M)
    (hNM : Subgroup.normalizer (involutionOddCoreClosure A : Set G) ≤ M)
    (hQM : Q ≤ M) (hescape : ¬ Subgroup.normalizer (Q : Set G) ≤ M)
    (habs : ∀ Y : Subgroup G, Nat.Coprime 2 (Nat.card Y) →
      Q ≤ Subgroup.normalizer (Y : Set G) → Y ≤ (pPrimeCore 2 M).map M.subtype) :
    involutionOddCoreClosure A = ⊥ := by
  let _ := hG.isSimpleGroup
  have hcore := Subgroup.pPrimeCore_eq_bot_of_maximal_normalizer_escape
    2 M Q hM hQM hescape habs
  have hRO := (minimalSimple_oddCore_overgroup_sandwich hG A M hA hM.lt_top hNM).1
  rw [hcore, Subgroup.map_bot] at hRO
  exact bot_unique hRO

end Stellmacher.Recognition
