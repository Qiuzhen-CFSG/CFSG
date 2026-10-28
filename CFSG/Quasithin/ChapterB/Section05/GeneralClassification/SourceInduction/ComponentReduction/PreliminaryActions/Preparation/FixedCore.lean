module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.LocalContracts
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTwoQuotient

/-!
# Passing from the fixed two-core space to the B.5.9 seed

The kernel of L on [W,L] has exponent two on a faithful binary L-module W.
Thus O₂(L)=1 makes L faithful on U=[C_V(O₂(LA)),L]. The local representation
kernel then centralizes L. Combining this with B.5.5(1ii)'s equality on the
fixed-core space gives C_A(U)=C_A(L), and [L,A]=L gives nontrivial A-action.
All kernel normality in the local argument is relative to LA.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.5(1ii), printed p.104, and B.5.9, printed p.107.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions.Preparation
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

private theorem binary_add_self (v : V) : v + v = 0 := by
  have h := congrArg (fun c : ZMod 2 => c • v) (show (1 : ZMod 2) + 1 = 0 from rfl)
  simpa only [add_smul, one_smul, zero_smul] using h

theorem normal_twoCore_eq_bot {L : Subgroup G} [L.Normal]
    (hcore : pCore 2 G = ⊥) : pCore 2 L = ⊥ := by
  have hle : (pCore 2 L).map L.subtype ≤ pCore 2 G :=
    le_sSup ⟨inferInstance, pCore_isPGroup.map L.subtype⟩
  have hm : (pCore 2 L).map L.subtype = ⊥ := le_bot_iff.mp (hle.trans_eq hcore)
  apply Subgroup.map_injective L.subtype_injective
  simpa only [Subgroup.map_bot] using hm

theorem fixedCore_stable (L A : Subgroup G) :
    L ⊔ A ≤ subspaceStabilizer ρ (fixedSpace ρ (localTwoCore L A)) := by
  apply fixedSpace_invariant_normalizer
  simpa only [localTwoCore, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
    (pCore 2 ↥(L ⊔ A)).le_normalizer_map (L ⊔ A).subtype

theorem seed_le_fixedCore (L A : Subgroup G) :
    naturalSeedSpace ρ L A ≤ fixedSpace ρ (localTwoCore L A) :=
  subspaceCommutator_le_of_invariant ρ (le_sup_left.trans (fixedCore_stable ρ L A))

/-- The kernel on [W,L] has exponent two on W. With O₂(L)=1, a faithful
L-action on W therefore remains faithful on [W,L]. -/
theorem seedComponent_faithful {L A : Subgroup G} (hLA : ⁅L,A⁆ = L)
    (hcore : pCore 2 L = ⊥)
    (hW : ∀ l ∈ L, (∀ w ∈ fixedSpace ρ (localTwoCore L A), ρ l w = w) → l = 1) :
    Function.Injective (seedComponentAction ρ hLA) := by
  let τ := seedComponentAction ρ hLA
  have hp : IsPGroup 2 τ.ker := by
    intro x
    refine ⟨1, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply hW _ (L.pow_mem x.val.property _)
    intro w hw
    have hd := LinearMap.congr_fun (MonoidHom.mem_ker.mp x.property)
      (⟨ρ x.val w - w, Submodule.subset_span
        ⟨x.val, x.val.property, w, hw, rfl⟩⟩ : naturalSeedSpace ρ L A)
    have hd' := congrArg Subtype.val hd
    change ρ x.val (ρ x.val w - w) = ρ x.val w - w at hd'
    rw [map_sub] at hd'
    have he : ρ x.val (ρ x.val w) = w := by
      apply add_right_cancel (b := w)
      exact (sub_eq_sub_iff_add_eq_add.mp hd').trans
        ((binary_add_self _).trans (binary_add_self w).symm)
    simpa only [pow_one, pow_two, map_mul, Module.End.mul_apply,
      OneMemClass.coe_one] using he
  apply (MonoidHom.ker_eq_bot_iff _).mp
  exact le_bot_iff.mp ((show τ.ker ≤ pCore 2 L from le_sSup ⟨inferInstance, hp⟩).trans_eq hcore)

/-- Faithfulness on the original component forces the local kernel to
centralize that component, with normality only inside LA. -/
theorem seedKernel_le_centralizer {L A : Subgroup G} (hLA : ⁅L,A⁆ = L)
    (hL : IsComponent G L) (hf : Function.Injective (seedComponentAction ρ hLA)) :
    (seedSubrepresentation ρ hLA).toRepresentation.ker.map (L ⊔ A).subtype ≤
      centralizer (L : Set G) := by
  let H := L ⊔ A
  let L₀ := L.subgroupOf H
  let τ := (seedSubrepresentation ρ hLA).toRepresentation
  have hc : IsComponent H L₀ := hL.subgroupOf le_sup_left
  have hnot : ¬ L₀ ≤ τ.ker := by
    intro h
    have hbot : L = ⊥ := by
      apply (Subgroup.eq_bot_iff_forall L).mpr
      intro l hl
      have he : (⟨l,hl⟩ : L) = 1 := hf (by
        change τ ⟨l, (le_sup_left : L ≤ L ⊔ A) hl⟩ = τ 1
        simpa only [map_one] using MonoidHom.mem_ker.mp
          (h (show (⟨l, (le_sup_left : L ≤ L ⊔ A) hl⟩ : H) ∈ L₀ from hl)))
      exact congrArg Subtype.val he
    let : IsQuasisimple L := hL.2
    let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
    have : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot L).mp this hbot
  have hcent : τ.ker ≤ centralizer (L₀ : Set H) := by
    rcases hc.normal_dichotomy τ.ker with h | h
    · exact (hnot h).elim
    · exact commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm _ _).trans h)
  rintro g ⟨x,hx,rfl⟩
  intro l hl
  exact congrArg Subtype.val (hcent hx ⟨l,(le_sup_left : L ≤ L ⊔ A) hl⟩ hl)

theorem seed_centralizer_eq {L A : Subgroup G} (hLA : ⁅L,A⁆ = L)
    (hL : IsComponent G L) (hf : Function.Injective (seedComponentAction ρ hLA))
    (hW : subspaceKernel ρ (fixedSpace ρ (localTwoCore L A)) A =
      A ⊓ centralizer (L : Set G)) :
    subspaceKernel ρ (naturalSeedSpace ρ L A) A = A ⊓ centralizer (L : Set G) := by
  apply le_antisymm
  · intro a ha
    refine ⟨ha.1, seedKernel_le_centralizer ρ hLA hL hf ?_⟩
    refine ⟨⟨a,(le_sup_right : A ≤ L ⊔ A) ha.1⟩, ?_, rfl⟩
    apply LinearMap.ext
    intro u
    exact Subtype.ext (ha.2 u u.property)
  · intro a ha
    have h := (hW.symm ▸ ha).2
    exact ⟨ha.1, fun u hu => h u (seed_le_fixedCore ρ L A hu)⟩

theorem seed_noncentral {L A : Subgroup G} (hLA : ⁅L,A⁆ = L)
    (hL : IsComponent G L)
    (hc : subspaceKernel ρ (naturalSeedSpace ρ L A) A = A ⊓ centralizer (L : Set G)) :
    subspaceCommutator ρ (naturalSeedSpace ρ L A) A ≠ ⊥ := by
  intro hz
  have hfix := (subspaceCommutator_eq_bot_iff ρ _ A).mp hz
  have hAC : A ≤ centralizer (L : Set G) := by
    intro a ha
    have hmem : a ∈ subspaceKernel ρ (naturalSeedSpace ρ L A) A :=
      ⟨ha, fun u hu => hfix hu ⟨a,ha⟩⟩
    exact (hc ▸ hmem).2
  have hbot : L = ⊥ := hLA.symm.trans
    ((commutator_comm _ _).trans (commutator_eq_bot_iff_le_centralizer.mpr hAC))
  let : IsQuasisimple L := hL.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  have : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  exact (Subgroup.nontrivial_iff_ne_bot L).mp this hbot
end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions.Preparation
