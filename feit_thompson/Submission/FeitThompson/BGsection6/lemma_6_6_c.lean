/-
Authors: OpenAI, Yusen Tang
-/

module

public import Submission.FeitThompson.BGsection6.lemma_6_6_b

open scoped MatrixGroups Pointwise TensorProduct

/-! # Lemma 6.6(c) from BG Section 6 -/

public theorem lemma_6_6_c
    {G : Type*} [Group G] [Finite G] [IsSolvable G]
    {p : ℕ} [Fact p.Prime] (hpl : HasPLengthOne (p := p) G) {S : Sylow p G}
    {Y : Set G} [Nonempty Y] (hY : Y ⊆ S) {x : G} (hx : ∀ y ∈ Y, x * y * x⁻¹ ∈ S) :
    ∃ c ∈ Subgroup.centralizer Y, ∃ g ∈ Subgroup.normalizer S, g * c = x := by
  classical
  let M : Subgroup G := pPrimeCore p G
  let U : Subgroup G := Subgroup.normalizer (G := G) S
  let H : Subgroup G := Subgroup.closure Y
  have hMU_top : M ⊔ U = ⊤ := by
    simpa [M, U, sup_comm] using (lemma_6_6_a (G := G) (p := p) hpl (S := S)).2.2
  have hHS : H ≤ S := by
    exact (Subgroup.closure_le (K := (S : Subgroup G))).2 hY
  have hHU : H ≤ U := by
    exact hHS.trans Subgroup.le_normalizer
  have hcopHM : Nat.Coprime (Nat.card H) (Nat.card M) := by
    have hHp : IsPGroup p H := IsPGroup.to_le (H := H) (K := (S : Subgroup G)) S.isPGroup' hHS
    rcases (IsPGroup.iff_card.mp hHp) with ⟨n, hn⟩
    rw [hn]
    exact Nat.Coprime.pow_left n (pPrimeCore_coprime_card (p := p) (G := G))
  have hx_conj : H.conjBy x ≤ U := by
    refine Subgroup.map_le_iff_le_comap.2 ?_
    refine (Subgroup.closure_le (K := Subgroup.comap (MulAut.conj x).toMonoidHom U)).2 ?_
    intro y hyY
    change x * y * x⁻¹ ∈ U
    exact Subgroup.le_normalizer (hx y hyY)
  obtain ⟨c, hcM, g, hgU, hx_eq⟩ :=
    lemma_6_5_c (K := M) (U := U) (H := H) hMU_top hHU hcopHM x hx_conj
  have hcY : c ∈ Subgroup.centralizer Y := by
    simpa [H, Subgroup.centralizer_closure] using hcM.2
  have hgN : g ∈ Subgroup.normalizer S := by
    simpa [U] using hgU
  exact ⟨c, hcY, g, hgN, hx_eq.symm⟩

