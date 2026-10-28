module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.SectionFive.Seeds
public import BenderSuzuki.SE.Permutation
public import Theory.GroupAction.SmallFixedSets

/-!
# The exact-two branch of the distinguished action theorem

For an odd prime p, a p-subgroup with exactly two fixed points can be
extended to an ambient Sylow without changing its fixed set: both fixed
cardinalities agree modulo p and lie between zero and two. Sylow conjugacy
then gives the same fixed cardinality for every ambient Sylow.

A saturated distinguished seed lies in a Sylow of its fixed point stabilizer.
That Sylow is ambient and has just one further fixed point. Section 3.8
supplies an invariant Sylow of this pair stabilizer from the seed's full
prime-share equality. It too is ambient, so its two-point fixed set is
invariant under an involution fixing exactly one point, a contradiction.
The seed does not have to be Sylow in any pair stabilizer.

Source: GLS, Volume 4, Chapter 2, Lemma 5.8 and the final proof of Theorem 2,
printed pp.41–42. This uses only the first assertion of Corollary 5.7 and
keeps its witness separate from the second assertion.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

private theorem fixed_card_eq_of_le {p : ℕ} [Fact p.Prime]
    {P Q : Subgroup G} (hP : IsPGroup p P) (hQ : IsPGroup p Q)
    (hPQ : P ≤ Q) (hcard : Nat.card (theorem4bFixedPoints M P) < p) :
    Nat.card (theorem4bFixedPoints M Q) = Nat.card (theorem4bFixedPoints M P) := by
  have hc (R : Subgroup G) : Nat.card (theorem4bFixedPoints M R) =
      Nat.card (MulAction.fixedPoints R (G ⧸ M)) :=
    Nat.card_congr (fixedPointsOfSubgroupEquivFixedPoints R)
  rw [hc, hc]
  exact hP.fixedPoints_card_eq_of_le_of_card_lt hQ hPQ ((hc P) ▸ hcard)

private theorem all_sylow_fixed_card_two {p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (hexact : ∃ E : Subgroup G, IsPGroup p E ∧ Nat.card (theorem4bFixedPoints M E) = 2) :
    ∀ S : Sylow p G, Nat.card (theorem4bFixedPoints M (S : Subgroup G)) = 2 := by
  let : Fact p.Prime := ⟨hp⟩
  have hptwo : 2 < p := by
    have := hp.two_le
    have : p ≠ 2 := by
      intro he
      subst p
      exact hpodd.not_two_dvd_nat (dvd_refl 2)
    omega
  obtain ⟨E, hEp, hEc⟩ := hexact
  obtain ⟨S, hES⟩ := hEp.exists_le_sylow
  have hSc : Nat.card (theorem4bFixedPoints M (S : Subgroup G)) = 2 :=
    (fixed_card_eq_of_le hEp S.isPGroup' hES (hEc ▸ hptwo)).trans hEc
  intro T
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S T
  have hTc : (T : Subgroup G) = (S : Subgroup G).conjBy g := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  rw [hTc, sectionFive_fixedPoints_card_conj]
  exact hSc

private theorem sylow_in_base_of_fixed_sylow {p : ℕ} [Fact p.Prime]
    (hall : ∀ S : Sylow p G, Nat.card (theorem4bFixedPoints M (S : Subgroup G)) = 2)
    (R : Sylow p M) :
    ∃ S : Sylow p G, (S : Subgroup G) = (R : Subgroup M).map M.subtype := by
  let T : Sylow p G := default
  have hpos : 0 < Nat.card (theorem4bFixedPoints M (T : Subgroup G)) := by rw [hall]; omega
  let : Nonempty (theorem4bFixedPoints M (T : Subgroup G)) := (Nat.card_pos_iff.mp hpos).1
  let b : theorem4bFixedPoints M (T : Subgroup G) := Classical.choice inferInstance
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G b.val (QuotientGroup.mk 1 : G ⧸ M)
  let U : Sylow p G := g • T
  have hUM : (U : Subgroup G) ≤ M := by
    intro x hx
    change x ∈ (T : Subgroup G).map (MulAut.conj g).toMonoidHom at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hf : (g * y * g⁻¹) • (QuotientGroup.mk 1 : G ⧸ M) = QuotientGroup.mk 1 := by
      rw [← hg]
      simpa [mul_smul] using congrArg (fun z : G ⧸ M => g • z) (b.property y hy)
    change g * y * g⁻¹ ∈ M
    simpa only [baseCoset_stabilizer] using MulAction.mem_stabilizer_iff.mpr hf
  let Rg : Subgroup G := (R : Subgroup M).map M.subtype
  have hc : Nat.card Rg = p ^ (Nat.card G).factorization p := by
    calc
      Nat.card Rg = Nat.card (R : Subgroup M) := Subgroup.card_map_of_injective M.subtype_injective
      _ = p ^ (Nat.card M).factorization p := R.card_eq_multiplicity
      _ = Nat.card ((U.subtype hUM : Sylow p M) : Subgroup M) := (U.subtype hUM).card_eq_multiplicity.symm
      _ = Nat.card (U : Subgroup G) := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv
      _ = p ^ (Nat.card G).factorization p := U.card_eq_multiplicity
  exact ⟨Sylow.ofCard Rg hc, rfl⟩

/-- A saturated distinguished seed is incompatible with an odd-prime
subgroup having exactly two fixed points. The seed need not be a pair Sylow. -/
public theorem sectionFive_no_exact_two_of_seed
    (h : IsProductDisconnected Z M) (h3 : ActionSectionThree Z M)
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    {z : G} (hzZ : z ∈ Z) (hzM : z ∈ M)
    {Q : Subgroup G} (hQp : IsPGroup p Q) (hQM : Q ≤ M)
    (hzQ : z ∈ Subgroup.normalizer (Q : Set G))
    (hshare : theorem4bInvertedCard z Q = theorem4bPrimeShare M z p) :
    ¬ ∃ E : Subgroup G, IsPGroup p E ∧ Nat.card (theorem4bFixedPoints M E) = 2 := by
  intro hexact
  let : Fact p.Prime := ⟨hp⟩
  have hall := all_sylow_fixed_card_two hp hpodd hexact
  obtain ⟨R, hQR⟩ := (hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQM).symm).exists_le_sylow
  let Rg : Subgroup G := (R : Subgroup M).map M.subtype
  have hQRg : Q ≤ Rg := by
    intro x hx
    exact ⟨⟨x, hQM hx⟩, hQR hx, rfl⟩
  have hRM : Rg ≤ M := by simpa [Rg] using Subgroup.map_le_range M.subtype (R : Subgroup M)
  obtain ⟨S, hS⟩ := sylow_in_base_of_fixed_sylow hall R
  have hRc : Nat.card (theorem4bFixedPoints M Rg) = 2 := by
    simpa only [hS, Rg] using hall S
  let base : theorem4bFixedPoints M Rg :=
    ⟨QuotientGroup.mk 1, theorem4b_baseCoset_mem_fixedPoints hRM⟩
  obtain ⟨delta, hdelta, _⟩ := (Nat.card_eq_two_iff' base).mp hRc
  have hd : delta.val ≠ (QuotientGroup.mk 1 : G ⧸ M) := fun he => hdelta (Subtype.ext he)
  have hRd : Rg ≤ MulAction.stabilizer G delta.val := fun x hx =>
    MulAction.mem_stabilizer_iff.mpr (delta.property x hx)
  let D : Subgroup G := M ⊓ MulAction.stabilizer G delta.val
  have hSD : (S : Subgroup G) ≤ D := hS ▸ le_inf hRM hRd
  obtain ⟨V, hVD, hzV⟩ := (h3.invariant_sylow z hzZ hzM p hp hpodd delta.val hd).mpr
    ⟨Q, hQp, le_inf hQM (hQRg.trans hRd), hzQ, hshare⟩
  obtain ⟨VD, hV⟩ := hVD
  have hVc : Nat.card V = p ^ (Nat.card G).factorization p := by
    calc
      Nat.card V = Nat.card (VD : Subgroup D) := by rw [hV, Subgroup.card_map_of_injective D.subtype_injective]
      _ = p ^ (Nat.card D).factorization p := VD.card_eq_multiplicity
      _ = Nat.card ((S.subtype hSD : Sylow p D) : Subgroup D) := (S.subtype hSD).card_eq_multiplicity.symm
      _ = Nat.card (S : Subgroup G) := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSD).toEquiv
      _ = p ^ (Nat.card G).factorization p := S.card_eq_multiplicity
  let T : Sylow p G := Sylow.ofCard V hVc
  have hVT : (T : Subgroup G) = V := rfl
  have hVc2 : Nat.card (theorem4bFixedPoints M V) = 2 := hVT ▸ hall T
  have hVle : V ≤ D := by rw [hV]; exact (Subgroup.map_le_range D.subtype VD).trans (by simp)
  let a : theorem4bFixedPoints M V :=
    ⟨QuotientGroup.mk 1, theorem4b_baseCoset_mem_fixedPoints (hVle.trans inf_le_left)⟩
  let b : theorem4bFixedPoints M V :=
    ⟨delta.val, fun x hx => MulAction.mem_stabilizer_iff.mp (hVle hx).2⟩
  let c : theorem4bFixedPoints M V :=
    ⟨z • delta.val, fixedPoints_smul_of_mem_normalizer hzV b.property⟩
  have hca : c ≠ a := by
    intro he
    have hzfix : z • (QuotientGroup.mk 1 : G ⧸ M) = QuotientGroup.mk 1 :=
      MulAction.mem_stabilizer_iff.mp (by simpa only [baseCoset_stabilizer] using hzM)
    exact hd (MulAction.injective z ((congrArg Subtype.val he).trans hzfix.symm))
  have hcb : c ≠ b := by
    intro he
    exact hd (action_fixedPoint_eq_base h hzZ hzM (congrArg Subtype.val he))
  obtain ⟨other, _, hother⟩ := (Nat.card_eq_two_iff' a).mp hVc2
  exact hcb ((hother c hca).trans (hother b (fun he => hd (congrArg Subtype.val he))).symm)

end BenderSuzuki.ZD
