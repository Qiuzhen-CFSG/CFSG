module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.OtherModels.AlternatingSeven.FixedModel
public import Theory.Alternating.Aut
public import Theory.ElementaryAbelian.Basic
import Mathlib.Tactic
/-!
# The A₇ four-group fixed-action obstruction

Every automorphism of A₇ is induced by a unique permutation of seven letters.
The permutations fixing a standard Sylow two-subgroup pointwise lie in a set
of four elements. A faithful actor group of order four fills this set, so it
contains conjugation by `(0 1)`. Its actual fixed subgroup is S₅ and has trivial
two-core. Conjugacy of Sylow subgroups transports this model to arbitrary Sylows.

The final theorem excludes the component A₇ in both the A₇ and S₇ alternatives
of Aschbacher–Smith F.6.18(7),(9), printed pp.309–310, as required in 15.4.18,
printed pp.1162–1163. The triple covers are handled separately in `Covers`.
-/

open Equiv Equiv.Perm Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.OtherModels.AlternatingSeven

private noncomputable def automorphismEquiv : Perm (Fin 7) ≃* MulAut K :=
  MulEquiv.ofBijective _
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by decide) (by decide))

private theorem exists_transposition_actor {A : Type*} [Group A] [Finite A]
    (hA : Nat.card A = 4) (ρ : A →* MulAut K) (hρ : Function.Injective ρ)
    (hfix : ∀ a x, x ∈ (standardSylow : Subgroup K) → ρ a x = x) :
    ∃ a : A, a ≠ 1 ∧ ρ a = MulAut.conjNormal t := by
  let σ : A →* Perm (Fin 7) := automorphismEquiv.symm.toMonoidHom.comp ρ
  have hσ : Function.Injective σ := automorphismEquiv.symm.injective.comp hρ
  have hconj (a : A) : (MulAut.conjNormal (σ a) : MulAut K) = ρ a :=
    automorphismEquiv.apply_symm_apply (ρ a)
  have hmem (a : A) : σ a ∈ centralizerElements := by
    have hcomm (x : K) (hx : x ∈ (standardSylow : Subgroup K)) :
        σ a * (x : Perm (Fin 7)) = (x : Perm (Fin 7)) * σ a := by
      have h := congrArg Subtype.val (show (MulAut.conjNormal (σ a)) x = x by
        rw [hconj a]; exact hfix a x hx)
      change σ a * (x : Perm (Fin 7)) * (σ a)⁻¹ = (x : Perm (Fin 7)) at h
      exact (mul_inv_eq_iff_eq_mul).mp h
    simpa only [centralizerElements, Finset.mem_insert, Finset.mem_singleton] using
      centralizer_calculation (σ a) (hcomm r r_mem_standardSylow) (hcomm s s_mem_standardSylow)
  let f : A → (centralizerElements : Set (Perm (Fin 7))) := fun a => ⟨σ a, hmem a⟩
  have hf : Function.Bijective f := (Nat.bijective_iff_injective_and_card _).mpr
    ⟨fun a b hab => hσ (congrArg Subtype.val hab), hA.trans centralizerElements_card.symm⟩
  obtain ⟨a, ha⟩ := hf.surjective ⟨t, t_mem_centralizerElements⟩
  have hat : σ a = t := congrArg Subtype.val ha
  refine ⟨a, ?_, ?_⟩
  · intro ha1
    have : t = 1 := by rw [← hat, ha1, map_one]
    exact t_ne_one this
  · rw [← hconj a, hat]

/-- A faithful order-four action centralizing a Sylow two-subgroup of A₇ has
an actual S₅ fixed subgroup for some nonidentity actor. -/
public theorem exists_symmetricFive_fixedSubgroup {A : Type*} [Group A] [Finite A]
    (P : Sylow 2 K) (hA : Nat.card A = 4) (ρ : A →* MulAut K)
    (hρ : Function.Injective ρ)
    (hfix : ∀ a x, x ∈ (P : Subgroup K) → ρ a x = x) :
    ∃ a : A, a ≠ 1 ∧ Nonempty ((ρ a).fixedSubgroup ≃* S5) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K standardSylow P
  let e : K ≃* K := MulAut.conj g
  let β : A →* MulAut K := (MulAut.congr e).symm.toMonoidHom.comp ρ
  have hβ : Function.Injective β := (MulAut.congr e).symm.injective.comp hρ
  have hβfix (a : A) (x : K) (hx : x ∈ (standardSylow : Subgroup K)) : β a x = x := by
    have hxP : e x ∈ (P : Subgroup K) := by
      rw [← hg]
      change e x ∈ (standardSylow : Subgroup K).map e.toMonoidHom
      exact Subgroup.mem_map_of_mem e.toMonoidHom hx
    change e.symm (ρ a (e x)) = x
    rw [hfix a (e x) hxP, e.symm_apply_apply]
  obtain ⟨a, ha, hact⟩ := exists_transposition_actor hA β hβ hβfix
  have htransport : MulAut.congr e (β a) = ρ a :=
    (MulAut.congr e).apply_symm_apply (ρ a)
  let E : (β a).fixedSubgroup ≃* (ρ a).fixedSubgroup :=
    (MulAut.fixedSubgroupCongr e (β a)).trans
      (MulEquiv.subgroupCongr (congrArg MulAut.fixedSubgroup htransport))
  exact ⟨a, ha, ⟨E.symm.trans
    ((MulEquiv.subgroupCongr (congrArg MulAut.fixedSubgroup hact)).trans
      transpositionFixedEquiv.symm)⟩⟩

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.OtherModels.AlternatingSeven

namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.OtherModels
open AlternatingSeven
/-- The A₇ component cannot have self-centralizing two-core in every
nonidentity fixed subgroup of the source four-group action. -/
public theorem alternating_seven_fixed_action_obstruction
    {A : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
    (P : Sylow 2 (alternatingGroup (Fin 7))) (hA : Nat.card A = 4)
    (ρ : A →* MulAut (alternatingGroup (Fin 7))) (hρ : Function.Injective ρ)
    (hfix : ∀ a x, x ∈ (P : Subgroup (alternatingGroup (Fin 7))) → ρ a x = x) :
    ∃ a : A, a ≠ 1 ∧
      ¬ centralizer (pCore 2 (ρ a).fixedSubgroup : Set (ρ a).fixedSubgroup) ≤
        pCore 2 (ρ a).fixedSubgroup := by
  obtain ⟨a, ha, ⟨e⟩⟩ := exists_symmetricFive_fixedSubgroup P hA ρ hρ hfix
  refine ⟨a, ha, ?_⟩
  have hc : pCore 2 (ρ a).fixedSubgroup = ⊥ := by
    rw [← pCore_map_iso 2 e.symm, s5_twoCore_eq_bot, Subgroup.map_bot]
  rw [hc]
  intro h
  have htop : (⊤ : Subgroup (ρ a).fixedSubgroup) ≤ ⊥ := by
    intro x _
    exact h (by simp [Subgroup.mem_centralizer_iff])
  have hcard := Subgroup.card_le_of_le htop
  rw [Subgroup.card_top, Subgroup.card_bot, Nat.card_congr e.toEquiv] at hcard
  norm_num [S5, Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] at hcard
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.OtherModels
