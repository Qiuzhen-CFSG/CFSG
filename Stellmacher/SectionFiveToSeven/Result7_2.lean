module

public import Stellmacher.SectionFiveToSeven.Defs

/-!
# Faithfulness of the Section 7 coset action

This module proves Stellmacher's result (7.2): the ambient group acts faithfully
on its bipartite coset graph.  The action kernel fixes the base coset and hence
lies in `P1`.  Its 2-core maps to a normal 2-subgroup of `G`, so the hypothesis
`O₂(G) = 1` makes that 2-core trivial.  The characteristic-2 condition on `P1`
then forces the kernel itself to be trivial.

The source is `refs/latex/stellmacher-n-group.tex`, (7.2), lines 1403--1411.
-/

open scoped Pointwise

namespace Stellmacher.SectionsFiveToSeven

universe u v

private theorem normal_eq_bot_of_characteristicTwo_of_pCore_eq_bot
    {P : Type u} [Group P] [Finite P]
    (hchar : Subgroup.centralizer (pCore 2 P : Set P) ≤ pCore 2 P)
    (N : Subgroup P) [N.Normal]
    (hcore : pCore 2 N = ⊥) :
    N = ⊥ := by
  let Q : Subgroup P := pCore 2 P
  have hI_normal : ((N ⊓ Q).subgroupOf N).Normal := by
    exact (inferInstance : (N ⊓ Q).Normal).subgroupOf N
  have hI_two : IsPGroup 2 ((N ⊓ Q).subgroupOf N) := by
    intro x
    let xQ : Q := ⟨x.1.1, x.2.2⟩
    rcases (pCore_isPGroup (p := 2) (G := P)) xQ with ⟨n, hn⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    simpa [xQ] using congrArg Subtype.val hn
  have hI_le : (N ⊓ Q).subgroupOf N ≤ pCore 2 N :=
    le_sSup ⟨hI_normal, hI_two⟩
  have hI_sub_bot : (N ⊓ Q).subgroupOf N = ⊥ := by
    apply le_antisymm
    · simpa [hcore] using hI_le
    · exact bot_le
  have hI_bot : N ⊓ Q = ⊥ := by
    rw [← Subgroup.map_subgroupOf_eq_of_le (show N ⊓ Q ≤ N from inf_le_left)]
    rw [hI_sub_bot, Subgroup.map_bot]
  have hcomm : ⁅N, Q⁆ = ⊥ := by
    apply le_antisymm
    · exact (Subgroup.commutator_le_inf N Q).trans (le_of_eq hI_bot)
    · exact bot_le
  have hN_le_Q : N ≤ Q := by
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm).trans hchar
  have hN_two : IsPGroup 2 N := by
    intro x
    let xQ : Q := ⟨x.1, hN_le_Q x.2⟩
    rcases (pCore_isPGroup (p := 2) (G := P)) xQ with ⟨n, hn⟩
    refine ⟨n, Subtype.ext ?_⟩
    simpa [xQ] using congrArg Subtype.val hn
  have htop_le : (⊤ : Subgroup N) ≤ pCore 2 N :=
    le_sSup ⟨inferInstance, hN_two.to_subgroup (⊤ : Subgroup N)⟩
  apply le_antisymm
  · intro x hx
    have hx_top : (⟨x, hx⟩ : N) ∈ (⊤ : Subgroup N) := trivial
    have hx_bot : (⟨x, hx⟩ : N) ∈ (⊥ : Subgroup N) := by
      rw [← hcore]
      exact htop_le hx_top
    change x = 1
    exact congrArg Subtype.val (show (⟨x, hx⟩ : N) = 1 by simpa using hx_bot)
  · exact bot_le

/-- **Stellmacher (7.2).**  The action of the ambient group on its coset
graph is faithful. -/
public theorem lemma_seven_two
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2) :
    Γ.actionKernel = ⊥ := by
  let K : Subgroup G := Γ.actionKernel
  have hKnormal : K.Normal := by
    constructor
    intro n hn g
    rw [Γ.actionKernel_def] at hn ⊢
    intro d
    calc
      Γ.act (g * n * g⁻¹) d = Γ.act g⁻¹ (Γ.act n (Γ.act g d)) := by
        rw [Γ.act_mul, Γ.act_mul]
      _ = Γ.act g⁻¹ (Γ.act g d) := by rw [hn (Γ.act g d)]
      _ = Γ.act (g * g⁻¹) d := (Γ.act_mul g g⁻¹ d).symm
      _ = d := by rw [mul_inv_cancel, Γ.act_one]
  have hstab1 : Γ.vertexStabilizer (Γ.coset₁ 1) = P1 := by
    ext g
    have hmem : g ∈ Γ.vertexStabilizer (Γ.coset₁ 1) ↔
        Γ.act g (Γ.coset₁ 1) = Γ.coset₁ 1 := by
      have hdef : (Γ.vertexStabilizer (Γ.coset₁ 1) : Set G) =
          {x | Γ.act x (Γ.coset₁ 1) = Γ.coset₁ 1} :=
        Γ.stabilizer_def (Γ.coset₁ 1)
      exact Set.ext_iff.mp hdef g
    rw [hmem]
    simp only [Γ.act_coset₁, one_mul, Γ.coset₁_eq_iff,
      MulOpposite.op_one, one_smul]
    constructor
    · intro hset
      have hg_trans : g ∈ MulOpposite.op g • (P1 : Set G) :=
        Set.mem_smul_set.mpr ⟨1, P1.one_mem, by simp⟩
      rwa [hset] at hg_trans
    · intro hg
      exact op_smul_coe_set hg
  have hK_le_P1 : K ≤ P1 := by
    intro g hg
    rw [← hstab1]
    have hgfix : Γ.act g (Γ.coset₁ 1) = Γ.coset₁ 1 :=
      (Γ.actionKernel_def g).mp hg (Γ.coset₁ 1)
    have hdef : (Γ.vertexStabilizer (Γ.coset₁ 1) : Set G) =
        {x | Γ.act x (Γ.coset₁ 1) = Γ.coset₁ 1} :=
      Γ.stabilizer_def (Γ.coset₁ 1)
    exact (Set.ext_iff.mp hdef g).mpr hgfix
  let _ : K.Normal := hKnormal
  let R : Subgroup G := (pCore 2 K).map K.subtype
  have hR_normal : R.Normal := by
    dsimp [R]
    infer_instance
  have hR_two : IsPGroup 2 R := by
    dsimp [R]
    exact (pCore_isPGroup (p := 2) (G := K)).map K.subtype
  have hR_le : R ≤ pCore 2 G := le_sSup ⟨hR_normal, hR_two⟩
  have hR_bot : R = ⊥ := by
    apply le_antisymm
    · simpa [h.twoCore_eq_bot] using hR_le
    · exact bot_le
  have hK_core_bot : pCore 2 K = ⊥ := by
    apply (Subgroup.map_eq_bot_iff_of_injective (pCore 2 K) K.subtype_injective).mp
    simpa [R] using hR_bot
  let N : Subgroup P1 := K.subgroupOf P1
  have hN_normal : N.Normal := by
    dsimp [N]
    exact hKnormal.subgroupOf P1
  let _ : N.Normal := hN_normal
  have hN_core_bot : pCore 2 N = ⊥ := by
    let eKN : N ≃* K := Subgroup.subgroupOfEquivOfLe hK_le_P1
    have hmap : (pCore 2 N).map eKN.toMonoidHom = pCore 2 K :=
      pCore_map_iso 2 eKN
    rw [hK_core_bot] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective (pCore 2 N) eKN.injective).mp hmap
  have hN_bot : N = ⊥ :=
    normal_eq_bot_of_characteristicTwo_of_pCore_eq_bot
      h.P1_characteristicTwo N hN_core_bot
  have hK_bot : K = ⊥ := by
    have hmapN : N.map P1.subtype = K := by
      dsimp [N]
      exact Subgroup.map_subgroupOf_eq_of_le hK_le_P1
    rw [hN_bot, Subgroup.map_bot] at hmapN
    exact hmapN.symm
  exact hK_bot

end Stellmacher.SectionsFiveToSeven
