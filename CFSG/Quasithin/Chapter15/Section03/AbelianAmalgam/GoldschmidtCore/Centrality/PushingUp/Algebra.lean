module

public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.ThreeSubgroups
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.CharacteristicNormalizerClosure
public import Theory.Quasithin

/-!
# Intrinsic endgame of the doubled-natural pushing-up argument

The relative three-subgroups lemma removes the second commutator with a
perfect component. An elementary subgroup with no fixed points embeds in
the genuine block quotient, giving the order obstruction. Finally a
nontrivial two-subgroup normalized by a maximal two-local has precisely
that normalizer.

Source: Aschbacher–Smith, C.1.7, C.1.30, C.1.37 (printed pp.123,135,141–143),
in the proposed repair of 15.3.68(2). These lemmas make no classification
or pushing-up assumption.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.PushingUp
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement

/-- Perfectness removes one iteration of the commutator, relative to U. -/
theorem commutator_le_of_core_commutator_le {G : Type*} [Group G] (N L U : Subgroup G) [Group.IsPerfect L]
    (hNL : ⁅N,L⁆ ≤ N ⊓ L)
    (hcore : ⁅N ⊓ L,L⁆ ≤ U)
    (hLU : L ≤ normalizer U) (hNU : N ≤ normalizer U) : ⁅N,L⁆ ≤ U := by
  have h₂ : ⁅⁅N,L⁆,L⁆ ≤ U := (commutator_mono hNL le_rfl).trans hcore
  have h₁ : ⁅⁅L,N⁆,L⁆ ≤ U := by rwa [commutator_comm L N]
  have h := commutator_commutator_le_of_rotate_of_le_normalizer hLU hLU hNU h₁ h₂
  rwa [Subgroup.isPerfect_iff.mp (inferInstance : Group.IsPerfect L),
    commutator_comm] at h

/-- The kernel of U → U(L)/C_U(L)(L) consists exactly of the fixed points. -/
theorem card_le_blockModule_of_fixed_eq_bot {L : Type*} [Group L] [Finite L] (U : Subgroup L)
    (hU : U ≤ CFSG.Quasithin.ChapterC.blockU L)
    (hfix : U ⊓ center L = ⊥) :
    Nat.card U ≤ Nat.card (CFSG.Quasithin.ChapterC.BlockModule L) := by
  let f := (QuotientGroup.mk' (CFSG.Quasithin.ChapterC.blockFixed L)).comp (inclusion hU)
  apply Nat.card_le_card_of_injective f
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro u hu
  apply Subtype.ext
  have huZ : (u : L) ∈ center L := by
    have hf : inclusion hU u ∈ CFSG.Quasithin.ChapterC.blockFixed L :=
      (QuotientGroup.eq_one_iff _).mp hu
    exact hf
  have huB : (u : L) ∈ (⊥ : Subgroup L) := hfix ▸ ⟨u.property, huZ⟩
  exact huB

/-- If [W,L] lies in an L-invariant U, then L normalizes UW. -/
theorem normalizes_sup_of_commutator_le {G : Type*} [Group G] (L U W : Subgroup G)
    (hLU : L ≤ normalizer U) (hWL : ⁅W,L⁆ ≤ U) :
    L ≤ normalizer (U ⊔ W : Subgroup G) := by
  apply le_normalizer_iff.mpr
  intro l hl a ha
  have hm : (U ⊔ W).map (MulAut.conj l).toMonoidHom ≤ U ⊔ W := by
    rw [Subgroup.map_sup]
    apply sup_le
    · rintro _ ⟨u,hu,rfl⟩
      exact (show U ≤ U ⊔ W from le_sup_left) (le_normalizer_iff.mp hLU l hl u hu)
    · rintro _ ⟨w,hw,rfl⟩
      have hc : ⁅l,w⁆ ∈ U := hWL (by
        rw [commutator_comm W L]
        exact commutator_mem_commutator hl hw)
      have hh := (U ⊔ W).mul_mem ((show U ≤ U ⊔ W from le_sup_left) hc) ((show W ≤ U ⊔ W from le_sup_right) hw)
      change l * w * l⁻¹ ∈ U ⊔ W
      simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one] using hh
  exact hm (mem_map_of_mem _ ha)

/-- A maximal two-local containing the normalizer action forces the contradiction. -/
theorem false_of_normalizes_elementary_join {G : Type*} [Group G] (M A X : Subgroup G)
    (hM : IsMaximalTwoLocal M) (hA : A ≠ ⊥) (hp : IsPGroup 2 A)
    (hMA : M ≤ normalizer A) (hXA : X ≤ normalizer A) (hXM : ¬ X ≤ M) : False := by
  exact hXM (hXA.trans (hM.2 ⟨A,hA,hp,rfl⟩ hMA))

/-- A fixed-point-free subgroup of order 64 cannot lie in an L₃(2) block layer. -/
theorem not_linearTwoBlock_of_card {L : Type*} [Group L] [Finite L]
    (U : Subgroup L) (hU : U ≤ ChapterC.blockU L)
    (hfix : U ⊓ center L = ⊥) (hcard : Nat.card U = 64) :
    ¬ ChapterC.IsLinearTwoBlock L 3 := by
  intro hblock
  have h := card_le_blockModule_of_fixed_eq_bot U hU hfix
  rw [hcard, hblock.module_card] at h
  norm_num at h

/-- The same obstruction applies to the field-parameter version of an SL₃(2) block. -/
theorem not_sl3EvenBlock_of_card {L : Type*} [Group L] [Finite L]
    (U : Subgroup L) (hU : U ≤ ChapterC.blockU L)
    (hfix : U ⊓ center L = ⊥) (hcard : Nat.card U = 64) :
    ¬ ChapterC.IsSL3EvenBlock L 1 := by
  intro hblock
  have h := card_le_blockModule_of_fixed_eq_bot U hU hfix
  rw [hcard, hblock.module_card] at h
  norm_num at h

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.PushingUp
