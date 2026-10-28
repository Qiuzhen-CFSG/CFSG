module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Conjugates
public import Theory.GroupTheory.CoprimeCentralizerDecomposition

/-!
# The coprime-action contradiction in the cubic branch

The literal P contains a nontrivial conjugate of B disjoint from V.
An order-three subgroup with C_P(A) = 1 generates P by commutators.
It therefore cannot centralize PV/V. The source application uses
P = O₂(L₂) to place P inside L and retains the actual flag plane V₂.
Constructing the cubic subgroup and its fixed-space and scalar properties
remains the separate Cartan calculation; these lemmas do not prove n odd.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
the paragraph beginning “Assume n is even”, printed p.774.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

omit [Finite G] in
theorem pairCore_not_le_seed {h : G}
    (hz : V ⊓ V.map (MulAut.conj h).toMonoidHom = ⊥)
    (hB : axis V H ≠ ⊥) : ¬ pairCore V H h ≤ V := by
  intro hp
  apply hB
  apply bot_unique
  intro b hb
  have hconj : (MulAut.conj h) b ∈ pairCore V H h :=
    (show (axis V H).map (MulAut.conj h).toMonoidHom ≤ pairCore V H h from le_sup_right)
      (mem_map_of_mem _ hb)
  have hbV : b ∈ V := hb.1
  have he : (MulAut.conj h) b = 1 :=
    mem_bot.mp (hz ▸ (show (MulAut.conj h) b ∈ V ⊓ V.map (MulAut.conj h).toMonoidHom from
      ⟨hp hconj, mem_map_of_mem _ hbV⟩))
  exact (MulAut.conj h).injective (he.trans (map_one _).symm)

/-- The final coprime-action contradiction of the cubic branch. -/
theorem pairCore_cubic_obstruction (s : Hypothesis1131At D S U₁ H)
    {h : G} (hh : h ∈ H)
    (hz : V ⊓ V.map (MulAut.conj h).toMonoidHom = ⊥)
    (hB : axis V H ≠ ⊥) (A : Subgroup G) (hA : Nat.card A = 3)
    (hn : A ≤ normalizer (pairCore V H h : Set G))
    (hfixed : pairCore V H h ⊓ centralizer (A : Set G) = ⊥)
    (hquotient : ⁅pairCore V H h, A⁆ ≤ V) : False := by
  let := pairCore_elementary s hh hz
  have hp : IsPGroup 2 (pairCore V H h) := IsElementaryAbelian.isPGroup 2 _
  have hcop : Nat.Coprime (Nat.card A) (Nat.card (pairCore V H h)) := by
    obtain ⟨k,hk⟩ := IsPGroup.iff_card.mp hp
    rw [hA,hk]
    exact (by decide : Nat.Coprime 3 2).pow_right k
  have he := eq_commutator_sup_centralizer_of_solvable_coprime
    (pairCore V H h) A hn inferInstance hcop
  rw [hfixed, sup_bot_eq] at he
  exact pairCore_not_le_seed hz hB (he.symm ▸ hquotient)

open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry in
/-- A cubic scalar on the original L/V cannot be fixed-point-free on P.
Here B is the actual flag plane, and P lies in the actual L₂. -/
theorem source_cubic_obstruction (s : Hypothesis1131At D S U₁ H)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    {h : G} (hh : h ∈ H)
    (hz : V ⊓ V.map (MulAut.conj h).toMonoidHom = ⊥)
    (hB : axis V H = f.Vi 1)
    (hcore : (f.Li 1).pCoreIn 2 = pairCore V H h)
    (A : Subgroup G) (hA : Nat.card A = 3)
    (hn : A ≤ normalizer (pairCore V H h : Set G))
    (hfixed : pairCore V H h ⊓ centralizer (A : Set G) = ⊥)
    (hscalar : ⁅L,A⁆ ≤ V) : False := by
  apply pairCore_cubic_obstruction s hh hz (hB.symm ▸ f.V_ne_bot 1) A hA hn hfixed
  have hPL : pairCore V H h ≤ L := by
    rw [← hcore]
    exact (pCoreIn_le 2 _).trans ((localResidual_le _).trans inf_le_left)
  exact (commutator_mono hPL le_rfl).trans hscalar

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
