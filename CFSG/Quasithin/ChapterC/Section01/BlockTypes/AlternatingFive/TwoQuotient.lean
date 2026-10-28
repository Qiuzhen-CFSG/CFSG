module
public import CFSG.Quasithin.ChapterC.Section01.BlockCentralQuotient
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Centralizer
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.AlternatingFive.NaturalAction.FixedKernel
public import Theory.GroupTheory.PCoreCentralQuotient
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# Natural A₅ blocks through two-group quotients

Irreducibility of the five-point module makes the kernel either contain its
whole moved layer or meet that layer trivially. In the latter case, its
commutator with the block is trivial, so the kernel is central. A central
two-group quotient preserves all short-group clauses and the actual natural
module, including the original quotient action.

This supplies the surviving-layer reduction in Aschbacher–Smith 10.2.1,
printed p.743. It does not classify the containing component.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC
variable {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]

omit [Finite A] [Finite B] in
/-- A two-group kernel either kills the whole moved layer or is central and disjoint from it. -/
theorem IsAlternatingBlock.layer_le_ker_or_ker_central (h : IsAlternatingBlock A 5) (f : A →* B)
    (hp : IsPGroup 2 f.ker) :
    blockU A ≤ f.ker ∨ (f.ker ⊓ blockU A = ⊥ ∧ f.ker ≤ center A) := by
  have hz : blockU A ⊓ center A = ⊥ := by
    rw [←blockFixed_map,h.blockFixed_eq_bot,Subgroup.map_bot]
  rcases h.2.1.irreducible.2 (f.ker ⊓ blockU A) inferInstance
    (by rw [hz]; exact bot_le) inf_le_right with hi | hi
  · right
    have hi' := hi.trans hz
    refine ⟨hi',?_⟩
    have hk : f.ker ≤ pCore 2 A := le_sSup ⟨inferInstance,hp⟩
    have hc : ⁅f.ker,(⊤ : Subgroup A)⁆ ≤ f.ker ⊓ blockU A :=
      le_inf (commutator_le_left _ _) (commutator_mono hk le_rfl)
    exact commutator_top_right_eq_bot_iff_le_center.mp (bot_unique (hc.trans hi'.le))
  · exact Or.inl (hi.symm.le.trans inf_le_left)

private theorem map_core (f : A →* B) (hf : Function.Surjective f)
    (hp : IsPGroup 2 f.ker) : (pCore 2 A).map f = pCore 2 B := by
  rw [← f.comap_pCore_of_ker_isPGroup hf hp, map_comap_eq_self_of_surjective hf]

private theorem map_u (f : A →* B) (hf : Function.Surjective f)
    (hp : IsPGroup 2 f.ker) : (blockU A).map f = blockU B := by
  rw [blockU,map_commutator,map_core f hf hp,map_top_of_surjective _ hf]
  rfl

private theorem five_fixed (h : IsAlternatingBlock A 5) (f : A →* B)
    (hf : Function.Surjective f) (hp : IsPGroup 2 f.ker)
    (hc : f.ker ≤ center A) : blockU B ⊓ center B = ⊥ := by
  have hz : blockU A ⊓ center A = ⊥ := by
    rw [←blockFixed_map,h.blockFixed_eq_bot,Subgroup.map_bot]
  have hu : f.ker ⊓ blockU A = ⊥ := bot_unique
    ((le_inf inf_le_right (inf_le_left.trans hc)).trans hz.le)
  apply bot_unique
  rintro b ⟨hb,hbc⟩
  rw [←map_u f hf hp] at hb
  obtain ⟨a,ha,rfl⟩ := hb
  have hac : a ∈ center A := by
    apply mem_center_iff.mpr
    intro x
    have hcomm : ⁅a,x⁆ ∈ f.ker ⊓ blockU A := by
      constructor
      · change f ⁅a,x⁆ = 1
        rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.mpr
          ((mem_center_iff.mp hbc) (f x)).symm
      · exact commutator_le_left _ _ (commutator_mem_commutator ha (mem_top x))
    exact (commutatorElement_eq_one_iff_mul_comm.mp (mem_bot.mp (hu ▸ hcomm))).symm
  have ha1 : a = 1 := mem_bot.mp (hz ▸ (show a ∈ blockU A ⊓ center A from ⟨ha,hac⟩))
  rw [ha1,map_one]
  exact one_mem _

/-- A central two-group quotient retains the actual A₅ block model. -/
theorem IsAlternatingBlock.of_surjective_central_two_kernel (h : IsAlternatingBlock A 5) (f : A →* B)
    (hf : Function.Surjective f) (hp : IsPGroup 2 f.ker)
    (hc : f.ker ≤ center A) : IsAlternatingBlock B 5 := by
  have hm : IsLinearBlockModel B ((BinaryPermutation.naturalRepresentation (Fin 5)).comp
      (alternatingGroup (Fin 5)).subtype) := by
    obtain ⟨ρ,⟨m⟩,hρ⟩ := h.2.2
    exact ⟨ρ,m.exists_of_central_two_quotient f hf h.2.1.twoPerfect hp hc ρ,hρ⟩
  have hz : blockU A ⊓ center A = ⊥ := by
    rw [←blockFixed_map,h.blockFixed_eq_bot,Subgroup.map_bot]
  have hzB := five_fixed h f hf hp hc
  refine ⟨h.1,?_,hm⟩
  refine {
    finite := inferInstance
    twoPerfect := h.2.1.twoPerfect.of_surjective f hf
    fitting := ?_
    elementary := ?_
    central := ?_
    quotient := ?_
    irreducible := ?_ }
  · apply generalizedFitting_eq_pCore_of_selfCentralizing 2
    exact f.centralizer_pCore_le_of_surjective_centralKernel hf hc
      ((centralizer_le blockU_le_core).trans_eq h.2.1.centralizer_blockU)
  · let := h.2.1.elementary
    rw [←map_u f hf hp]
    exact IsElementaryAbelian.map f
  · rw [←map_u f hf hp,←map_core f hf hp]
    rintro _ ⟨u,hu,rfl⟩ _ ⟨a,ha,rfl⟩
    exact (map_mul f a u).symm.trans
      ((congrArg f (h.2.1.central hu a ha)).trans (map_mul f u a))
  · rcases h.2.1.quotient with hq | hq
    · let := hq
      exact Or.inl (IsQuasisimple.of_mulEquiv (f.pCoreQuotientEquiv hf hp))
    · exact Or.inr ((Nat.card_congr (f.pCoreQuotientEquiv hf hp).toEquiv).symm.trans hq)
  · constructor
    · rw [hzB,bot_lt_iff_ne_bot]
      intro he
      have hU : blockU A ≤ f.ker := (Subgroup.map_eq_bot_iff _).mp ((map_u f hf hp).trans he)
      exact h.2.1.blockU_ne_bot (bot_unique ((le_inf le_rfl (hU.trans hc)).trans hz.le))
    · intro N hN hlo hNU
      let K := N.comap f ⊓ blockU A
      let : N.Normal := hN
      have hmap : K.map f = N := by
        apply le_antisymm
        · rintro _ ⟨a,ha,rfl⟩
          exact ha.1
        · intro b hb
          have huB := hNU hb
          rw [←map_u f hf hp] at huB
          obtain ⟨a,ha,rfl⟩ := huB
          exact ⟨a,⟨hb,ha⟩,rfl⟩
      rcases h.2.1.irreducible.2 K inferInstance (by rw [hz]; exact bot_le)
        inf_le_right with hk | hk
      · left
        rw [hz] at hk
        rw [←hmap,hk,Subgroup.map_bot,hzB]
      · right
        rw [←hmap,hk,map_u f hf hp]

end CFSG.Quasithin.ChapterC
