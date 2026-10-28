module

public import Theory.GroupTheory.MinimalParabolicKernelReduction
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# The normal kernel in a PSL2(4) pushing-up configuration

The exceptional isomorphism PSL2(4) = A5 makes the original quotient simple
and excludes a two-group quotient. Thus the unique Sylow maximal hypothesis
identifies the Sylow intersection with O2(H), and the arbitrary original
kernel has odd nilpotent Frattini image modulo O2(H). Supplements of the
original kernel also supplement O2(H).

This is the normal-kernel reduction in Niles, *Pushing-up in finite groups*
(1979), Lemma 2.2, applied to the original hypotheses of Theorem B at q=4.
The later module recognition and central-chief reduction are separate.
-/

public section
open Subgroup
namespace Theory.SpecificGroups.SL2

/-- Niles 2.2 for the literal original quotient H/K ≃ PSL2(4). -/
theorem original_kernel_reduction_of_psl2_four
    {H F : Type*} [Group H] [Finite H] [Field F] [Finite F]
    (hF : Nat.card F = 4) (S : Sylow 2 H)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal]
    (e : (H ⧸ K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :
    (S : Subgroup H) ⊓ K = pCore 2 H ∧
    K.map (QuotientGroup.mk' (pCore 2 H)) ≤ frattini (H ⧸ pCore 2 H) ∧
    Group.IsNilpotent (K.map (QuotientGroup.mk' (pCore 2 H))) ∧
    (¬ 2 ∣ Nat.card (K.map (QuotientGroup.mk' (pCore 2 H)))) ∧
    ∀ L : Subgroup H, L ⊔ K = ⊤ → L ⊔ pCore 2 H = ⊤ := by
  obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  let b := e.trans a
  let : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (H ⧸ K) := b.isSimpleGroup
  have hn : ¬ IsPGroup 2 (H ⧸ K) := by
    intro hp
    obtain ⟨n, hn⟩ := hp.exists_card_dvd_pow
    have hc : Nat.card (H ⧸ K) = 60 := by
      rw [Nat.card_congr b.toEquiv, nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    rw [hc] at hn
    have hd : 3 ∣ 2 ^ n := dvd_trans (by norm_num : 3 ∣ 60) hn
    have : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by decide) hd
    norm_num at this
  exact GroupTheory.MinimalParabolicKernel.quotient_kernel_reduction S hu K hn

end Theory.SpecificGroups.SL2
