/-
Authors: OpenAI, Yusen Tang
-/

module

public import FeitThompson.BGsection6.lemma_6_6_c

open scoped MatrixGroups Pointwise TensorProduct

/-! # Lemma 6.6(d) from BG Section 6 -/

public theorem lemma_6_6_d
    {G : Type*} [Group G] [Finite G] [IsSolvable G]
    {p : ℕ} [Fact p.Prime] (hpl : HasPLengthOne (p := p) G) (S : Sylow p G)
    {Q : Subgroup G} (hQ : IsPGroup p Q) :
    ∃ x ∈ Subgroup.centralizer (Q ⊓ S), Q.conjBy x ≤ S := by
  classical
  have hQ_conj_into_S : ∃ x : G, Q.conjBy x ≤ S := by
    obtain ⟨T, hQT⟩ := IsPGroup.exists_le_sylow (G := G) (p := p) hQ
    obtain ⟨x, hxTS⟩ := MulAction.exists_smul_eq G T S
    have hT_conj : MulAut.conj x • (T : Subgroup G) = S := by
      simpa using congrArg (fun P : Sylow p G => (P : Subgroup G)) hxTS
    have hQ_conj : Q.conjBy x ≤ S := by
      calc
        Q.conjBy x ≤ (T : Subgroup G).conjBy x := by
          simpa [Subgroup.conjBy] using
            (Subgroup.map_mono (f := (MulAut.conj x).toMonoidHom) hQT)
        _ = S := by
          simpa [Subgroup.conjBy] using hT_conj
    exact ⟨x, hQ_conj⟩
  obtain ⟨x, hxS⟩ := hQ_conj_into_S
  have hQS : (Q ⊓ S : Subgroup G).carrier.Nonempty := by
    exact ⟨1, by simp⟩
  let Y : Set G := (Q ⊓ S : Subgroup G)
  have hY : Y ⊆ S := by
    intro y hy
    exact hy.2
  have hxY : ∀ y ∈ Y, x * y * x⁻¹ ∈ S := by
    intro y hyY
    exact hxS (by
      refine Subgroup.mem_map.mpr ?_
      exact ⟨y, hyY.1, rfl⟩)
  obtain ⟨c, hcC, g, hgN, hgcx⟩ :=
    lemma_6_6_c (G := G) (p := p) hpl (S := S) (Y := Y) hY hxY
  have hQc_le : Q.conjBy c ≤ S := by
    have hgInvN : g⁻¹ ∈ Subgroup.normalizer (S : Subgroup G) :=
      (Subgroup.normalizer (S : Set G)).inv_mem hgN
    have hS_conj_inv : (S : Subgroup G).conjBy g⁻¹ = S := by
      simpa using lemma_6_5_conjBy_eq_of_mem_normalizer (H := (S : Subgroup G)) hgInvN
    have hc_eq : c = g⁻¹ * x := by
      rw [← hgcx]
      group
    calc
      Q.conjBy c = (Q.conjBy x).conjBy g⁻¹ := by
        rw [hc_eq]
        simpa using (lemma_6_5_conjBy_mul Q g⁻¹ x)
      _ ≤ S.conjBy g⁻¹ := Subgroup.map_mono hxS
      _ = S := hS_conj_inv
  exact ⟨c, by simpa [Y] using hcC, hQc_le⟩

