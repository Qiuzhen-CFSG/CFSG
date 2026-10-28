module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.TripleCore
public import Theory.GroupTheory.PResidual.CommutatorImage
public import Theory.SpecificGroups.SymmetricTwoResidual

/-!
# The residual commutator step in 14.7.70

A nontrivial two-subgroup of S₃ inverts its cubic residual. The existing
prime-kernel commutator lifting theorem therefore gives O²(X) = [O²(X),A]
for any full S₃ action with two-group kernel and any nontrivially acting
two-subgroup A. Only the six permutations are used in the finite check.

For the literal YT, relative normality of Y_E supplies the full action on E,
and its kernel is a two-group because C_G(E) is one. The residual/Sylow
supplement identifies O²(YT) with the original embedded O²(Y_E) = Y.
Thus a nontrivial action of T ∩ L gives Y = [Y,T ∩ L]. Under Y ≤ N_G(L),
this puts Y in L. Its actual point span E then lies in V, contradicting
Z_alpha ≰ V. Consequently the contrary normalizer containment forces
T ∩ L to centralize E. This is a reduction, not the completed escape:
the independent normalizer projection must rule out that central action.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
Lemma 14.7.70, printed p.1074 (PDF p.1091).
-/

@[expose] public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.ThompsonWitness.ProjectionEscape

private theorem perm_three_residual_commutator
    (B : Subgroup (Equiv.Perm (Fin 3))) (hB : IsPGroup 2 B) (hne : B ≠ ⊥) :
    pResidual 2 (Equiv.Perm (Fin 3)) = ⁅pResidual 2 (Equiv.Perm (Fin 3)), B⁆ := by
  classical
  have hnle : ¬ B ≤ ⊥ := fun he => hne (bot_unique he)
  obtain ⟨b, hb, hb1⟩ := SetLike.not_le_iff_exists.mp hnle
  have hb1 : b ≠ 1 := by simpa only [mem_bot] using hb1
  have hs : b ^ 2 = 1 := by
    have hc : ∀ b : Equiv.Perm (Fin 3), b ^ 2 = 1 ∨ b ^ 3 = 1 := by decide +kernel
    rcases hc b with h | h
    · exact h
    · obtain ⟨n, hn⟩ := hB ⟨b, hb⟩
      have hn' : b ^ (2 ^ n) = 1 := congrArg Subtype.val hn
      have ho : orderOf b = 1 := Nat.eq_one_of_dvd_coprimes
        ((by decide : Nat.Coprime 2 3).pow_left n)
        (orderOf_dvd_of_pow_eq_one hn') (orderOf_dvd_of_pow_eq_one h)
      exact (hb1 (orderOf_eq_one_iff.mp ho)).elim
  apply le_antisymm ?_ (commutator_le_left _ _)
  intro a ha
  have ha' : a ∈ alternatingGroup (Fin 3) := by
    simpa only [Equiv.Perm.twoResidual_eq_alternating] using ha
  have hc : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    rfl
  have ha3 : a ^ 3 = 1 := congrArg Subtype.val
    (hc ▸ pow_card_eq_one' (x := (⟨a, ha'⟩ : alternatingGroup (Fin 3))))
  have he : ⁅a⁻¹,b⁆ = a := (by
    decide +kernel : ∀ a b : Equiv.Perm (Fin 3), a ^ 3 = 1 →
      b ^ 2 = 1 → b ≠ 1 → ⁅a⁻¹,b⁆ = a) a b ha3 hs hb1
  exact he ▸ commutator_mem_commutator (inv_mem ha) hb

private theorem residual_eq_commutator_of_symmetricThree_action
    {X : Type*} [Group X] [Finite X]
    (f : X →* Equiv.Perm (Fin 3)) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (A : Subgroup X) (hA : IsPGroup 2 A)
    (hne : ¬ A ≤ f.ker) : pResidual 2 X = ⁅pResidual 2 X, A⁆ := by
  apply eq_commutator_of_isPPerfect_of_map_eq (pResidual 2 X) A
    (isPPerfect_pResidual 2) le_normalizer_of_normal f hk
  rw [map_pResidual_of_surjective 2 f hf]
  exact perm_three_residual_commutator (A.map f) (hA.map f)
    (fun he => hne ((map_eq_bot_iff A).mp he))

open Representation Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  {d : Data T L V F W} {c : CriticalPath (L := L) F}

/-- Nontrivial two-group action on E generates the literal Y by commutators. -/
theorem Y_eq_commutator_of_noncentral_action (h : Geometry d c)
    (A : Subgroup G) (hAT : A ≤ (T : Subgroup G))
    (hne : ¬ A ≤ centralizer (E c : Set G)) : Y c = ⁅Y c, A⁆ := by
  let := h.E_isKleinFour
  let e := IsKleinFour.autEquivPermThree (E c)
  let f := e.toMonoidHom.comp h.rightAction
  have hk : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
    exact h.rightAction_ker_two
  have hAI : A ≤ YT c := hAT.trans le_sup_right
  have hn : ¬ A.subgroupOf (YT c) ≤ f.ker := by
    intro hh
    apply hne
    intro a ha
    have hh' := hh (show (⟨a, hAI ha⟩ : YT c) ∈ A.subgroupOf (YT c) from ha)
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, h.rightAction_ker] at hh'
    exact hh'
  have hr := residual_eq_commutator_of_symmetricThree_action f
    (e.surjective.comp h.rightAction_surjective) hk (A.subgroupOf (YT c))
    (T.isPGroup'.to_le hAT).comap_subtype hn
  have hm := congrArg (Subgroup.map (YT c).subtype) hr
  have hy : (pResidual 2 (YT c)).map (YT c).subtype = Y c :=
    embedded_pResidual_join_pGroup (Y c) (T : Subgroup G)
      (isPPerfect_embedded_pResidual 2 (YE c)) T.isPGroup' h.T_normalizes_Y
  rwa [map_commutator, hy, map_subgroupOf_eq_of_le hAI] at hm

/-- The commutator lies in L when Y normalizes L and the actor lies in T ∩ L. -/
theorem Y_le_L_of_normalizer_and_noncentral_action (h : Geometry d c)
    (hYM : Y c ≤ normalizer (L : Set G))
    (ha : ¬ (T : Subgroup G) ⊓ L ≤ centralizer (E c : Set G)) : Y c ≤ L := by
  rw [Y_eq_commutator_of_noncentral_action h ((T : Subgroup G) ⊓ L) inf_le_left ha]
  exact (commutator_mono le_rfl inf_le_right).trans
    (le_normalizer_iff_commutator_le_right.mp hYM)

/-- The actual conjugate span forces T ∩ L to centralize E under the contrary
normalizer containment. The projection calculation must contradict this. -/
theorem normalizer_containment_forces_central_action (h : Geometry d c)
    (hYM : Y c ≤ normalizer (L : Set G)) :
    (T : Subgroup G) ⊓ L ≤ centralizer (E c : Set G) := by
  by_contra ha
  have hYL := Y_le_L_of_normalizer_and_noncentral_action h hYM ha
  apply h.Zα_not_le
  apply (le_sup_right : c.Zα ≤ E c).trans
  change E c ≤ V
  rw [h.span]
  exact conjugateSpanBy_le (F.le_seed 1) (hYL.trans d.natural.chosen.normalizes)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.ThompsonWitness.ProjectionEscape
