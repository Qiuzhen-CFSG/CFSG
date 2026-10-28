module
public import Theory.Representation.BinaryOffender.PermutedSupports
public import Theory.Representation.BinaryOffender.MovedSpaceTransport
public import Theory.Representation.GoldschmidtONan.Basic
public import Theory.GroupTheory.PResidual.Quotient
/-!
# Pointwise stabilizers of Sylow-fixed binary spaces

An odd subgroup normalized by a two-group has trivial pointwise kernel on
the latter's fixed space. That kernel Q has an invariant moved space [V,Q].
If nonzero, that space has a nonzero two-group-fixed vector, contradicting
the coprime fixed/moved splitting for Q. Faithfulness therefore gives Q = 1.

In a group with a normal odd subgroup and two-group quotient, the pointwise
stabilizer of a Sylow-fixed space consequently embeds in the quotient.
It contains the Sylow subgroup, hence equals it and has trivial two-residual.

Source: the coprime-action argument in Aschbacher–Smith 15.1.6, printed p.1087.
The application retains the literal faithful action and its fixed subspace.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

/-- An odd actor normalized by a two-group has trivial pointwise kernel on its fixed space. -/
theorem odd_kernel_on_two_fixed_eq_bot (hf : Function.Injective ρ)
    (P S : Subgroup G) (hodd : Odd (Nat.card P))
    (hSP : S ≤ normalizer (P : Set G)) (hS : IsPGroup 2 S) :
    subspaceKernel ρ (fixedSpace ρ S) P = ⊥ := by
  let Q := subspaceKernel ρ (fixedSpace ρ S) P
  have hSQ : S ≤ normalizer (Q : Set G) := by
    apply le_normalizer_iff.mpr
    intro s hs q hq
    refine ⟨le_normalizer_iff.mp hSP s hs q hq.1, ?_⟩
    intro v hv
    have hsi : ρ s⁻¹ v = v := hv ⟨s⁻¹,S.inv_mem hs⟩
    have hsf : ρ s v = v := hv ⟨s,hs⟩
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hsi, hq.2 v hv, hsf]
  have hW : subspaceCommutator ρ ⊤ Q = ⊥ := by
    by_contra hne
    have hWS : S ≤ subspaceStabilizer ρ (subspaceCommutator ρ ⊤ Q) :=
      subspaceCommutator_invariant_normalizer ρ
        (le_subspaceStabilizer ρ ⊤ (by intros; trivial)) hSQ
    obtain ⟨v,hv,hv0,hvf⟩ := PermutedSupports.exists_nonzero_fixed ρ S hS _ hne hWS
    have hoddQ : Odd (Nat.card Q) := hodd.of_dvd_nat (card_dvd_of_le (subspaceKernel_le ρ _ P))
    have hc : IsCompl (fixedSpace ρ Q) (subspaceCommutator ρ ⊤ Q) := by
      simpa only [RegularCyclicNormalClosure.displacementSpan, subspaceCommutator, eq_comm] using
        (GoldschmidtONan.isCompl_fixed_moved_of_odd (ρ := ρ) hoddQ)
    exact hv0 (Submodule.disjoint_def.mp hc.disjoint v
      (le_fixedSpace_subspaceKernel ρ _ P hvf) hv)
  have hfix := (subspaceCommutator_eq_bot_iff ρ ⊤ Q).mp hW
  apply bot_unique
  intro q hq
  apply mem_bot.mpr
  apply hf
  apply LinearMap.ext
  intro v
  exact (hfix Submodule.mem_top ⟨q,hq⟩).trans (by simp)

/-- In an odd-by-two group, the pointwise Sylow-fixed-space stabilizer is the Sylow subgroup. -/
theorem sylow_fixed_kernel_eq (hf : Function.Injective ρ) (S : Sylow 2 G)
    (P : Subgroup G) [P.Normal] (hodd : Odd (Nat.card P))
    (hquot : IsPGroup 2 (G ⧸ P)) :
    subspaceKernel ρ (fixedSpace ρ (S : Subgroup G)) ⊤ = (S : Subgroup G) := by
  let C := subspaceKernel ρ (fixedSpace ρ (S : Subgroup G)) ⊤
  have hQ := odd_kernel_on_two_fixed_eq_bot ρ hf P S hodd le_normalizer_of_normal S.isPGroup'
  let f := (QuotientGroup.mk' P).comp C.subtype
  have hfC : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro c hc
    apply mem_bot.mpr
    apply Subtype.ext
    change (c : G) = 1
    have hcp : (c : G) ∈ P := (QuotientGroup.eq_one_iff _).mp hc
    have hmem : (c : G) ∈ subspaceKernel ρ (fixedSpace ρ (S : Subgroup G)) P :=
      ⟨hcp,c.property.2⟩
    simpa only [hQ,mem_bot] using hmem
  have hC : IsPGroup 2 C := hquot.of_injective f hfC
  have hSC : (S : Subgroup G) ≤ C := fun s hs => ⟨mem_top _,fun v hv => hv ⟨s,hs⟩⟩
  exact S.is_maximal' hC hSC

/-- The literal pointwise stabilizer is a two-group. -/
theorem sylow_fixed_kernel_twoGroup (hf : Function.Injective ρ) (S : Sylow 2 G)
    (P : Subgroup G) [P.Normal] (hodd : Odd (Nat.card P))
    (hquot : IsPGroup 2 (G ⧸ P)) :
    IsPGroup 2 (subspaceKernel ρ (fixedSpace ρ (S : Subgroup G)) ⊤) := by
  rw [sylow_fixed_kernel_eq ρ hf S P hodd hquot]
  exact S.isPGroup'

/-- The pointwise stabilizer has trivial two-residual. -/
theorem sylow_fixed_kernel_residual_eq_bot (hf : Function.Injective ρ) (S : Sylow 2 G)
    (P : Subgroup G) [P.Normal] (hodd : Odd (Nat.card P))
    (hquot : IsPGroup 2 (G ⧸ P)) :
    pResidual 2 (subspaceKernel ρ (fixedSpace ρ (S : Subgroup G)) ⊤) = ⊥ := by
  have hh := pResidual_le_ker_of_isPGroup 2
    (MonoidHom.id (subspaceKernel ρ (fixedSpace ρ (S : Subgroup G)) ⊤))
    (sylow_fixed_kernel_twoGroup ρ hf S P hodd hquot)
  simpa only [MonoidHom.ker_id] using bot_unique hh
end Representation.BinaryOffender
