module

public import Stellmacher.SectionThree.LemmaThreeFour

/-!
# Faithfulness of the distinguished reflection

In the core-free primitive quotient attached to the unique maximal subgroup,
the odd elementary abelian complement has centralizer contained in itself.
An element of the Sylow `2`-subgroup which centralizes that complement is
therefore trivial. Applying Lemma (3.3) shows that the chosen element outside
`O₂(P)` cannot centralize the quotient residual. This supplies the faithful
action input for Stellmacher's reflected-line construction in Lemma (3.6),
Journal of Algebra 190 (1997), pp. 22--23.
-/

open scoped Pointwise

universe u

@[expose] public section

private theorem centralizer_le_normal_complement_of_corefree
    {Q : Type u} [Group Q]
    (K T B : Subgroup Q)
    (hKnormal : K.Normal) (hKcomm : IsMulCommutative K)
    (hKT : K ⊔ T = ⊤) (hTB : T ≤ B) (hBcore : B.normalCore = ⊥) :
    Subgroup.centralizer (K : Set Q) ≤ K := by
  let _ : K.Normal := hKnormal
  let _ : IsMulCommutative K := hKcomm
  let C : Subgroup Q := Subgroup.centralizer (K : Set Q)
  have hCnormal : C.Normal := by
    infer_instance
  let _ : C.Normal := hCnormal
  let D : Subgroup Q := T ⊓ C
  have hDnormal : D.Normal := by
    have hnormK : K ≤ Subgroup.normalizer (D : Set Q) := by
      intro k hk
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor <;> intro hx
      · have hxC : x ∈ C := hx.2
        have hkcomm : k * x = x * k :=
          Subgroup.mem_centralizer_iff.mp hxC k hk
        simpa [hkcomm] using hx
      · have hxC : k * x * k⁻¹ ∈ C := hx.2
        have hkC : k ∈ C := by
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          exact congrArg Subtype.val
            ((IsMulCommutative.is_comm (M := K)).comm
              (⟨y, hy⟩ : K) ⟨k, hk⟩)
        have hxC' : x ∈ C := by
          have := hCnormal.conj_mem (k * x * k⁻¹) hxC k⁻¹
          simpa [mul_assoc] using this
        have hkcomm : k * x = x * k :=
          Subgroup.mem_centralizer_iff.mp hxC' k hk
        exact ⟨by simpa [hkcomm] using hx.1, hxC'⟩
    have hnormT : T ≤ Subgroup.normalizer (D : Set Q) := by
      intro t ht
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor <;> intro hx
      · exact ⟨T.mul_mem (T.mul_mem ht hx.1) (T.inv_mem ht),
          hCnormal.conj_mem x hx.2 t⟩
      · have htinv : t⁻¹ ∈ T := T.inv_mem ht
        have hback := hCnormal.conj_mem (t * x * t⁻¹) hx.2 t⁻¹
        have hbackT : x ∈ T := by
          have := T.mul_mem (T.mul_mem htinv hx.1) (T.inv_mem htinv)
          simpa [mul_assoc] using this
        exact ⟨hbackT, by simpa [mul_assoc] using hback⟩
    apply Subgroup.normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hKT]
    exact sup_le hnormK hnormT
  have hDleB : D ≤ B := inf_le_left.trans hTB
  have hDbot : D = ⊥ := by
    apply le_bot_iff.mp
    have hDcore : D ≤ B.normalCore :=
      @Subgroup.normal_le_normalCore Q _ B D hDnormal |>.mpr hDleB
    simpa [hBcore] using hDcore
  intro c hc
  have hctop : c ∈ K ⊔ T := by rw [hKT]; trivial
  have hcoe : (↑(K ⊔ T) : Set Q) = (K : Set Q) * (T : Set Q) :=
    Subgroup.coe_mul_of_right_le_normalizer_left K T
      (Subgroup.le_normalizer_of_normal : T ≤ Subgroup.normalizer K)
  change c ∈ (↑(K ⊔ T) : Set Q) at hctop
  rw [hcoe] at hctop
  rcases hctop with ⟨k, hk, t, ht, hkt⟩
  have htC : t ∈ C := by
    have hkC : k ∈ C := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val
        ((IsMulCommutative.is_comm (M := K)).comm
          (⟨y, hy⟩ : K) ⟨k, hk⟩)
    have : t = k⁻¹ * c := by rw [← hkt]; simp
    rw [this]
    exact C.mul_mem (C.inv_mem hkC) hc
  have htD : t ∈ D := ⟨ht, htC⟩
  have ht1 : t = 1 := by simpa [hDbot] using htD
  subst t
  change k * 1 = c at hkt
  have hkc : k = c := by simpa using hkt
  exact hkc ▸ hk

private theorem sylow_element_eq_one_of_centralizes_corefree_complement
    {Q : Type u} [Group Q]
    (K T B : Subgroup Q)
    (hKnormal : K.Normal) (hKcomm : IsMulCommutative K)
    (hKT : K ⊔ T = ⊤) (hTB : T ≤ B) (hBcore : B.normalCore = ⊥)
    (hKinfB : K ⊓ B = ⊥)
    (t : Q) (htT : t ∈ T)
    (htcentral : t ∈ Subgroup.centralizer (K : Set Q)) :
    t = 1 := by
  have htK : t ∈ K :=
    centralizer_le_normal_complement_of_corefree K T B hKnormal hKcomm
      hKT hTB hBcore htcentral
  have htB : t ∈ B := hTB htT
  have htbot : t ∈ (⊥ : Subgroup Q) := by
    have htinf : t ∈ K ⊓ B := ⟨htK, htB⟩
    rw [← hKinfB]
    exact htinf
  simpa using htbot

theorem quotient_reflection_not_centralizes_residual
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) (h : Stellmacher.SectionThree.Hypotheses G S)
    (P : Subgroup G)
    (hP : P ∈ Stellmacher.SectionThree.PSet (⊤ : Subgroup G) S)
    (B P₀ : Subgroup P)
    (hB : IsCoatom B ∧ S.subgroupOf P ≤ B ∧
      ∀ B' : Subgroup P, IsCoatom B' → S.subgroupOf P ≤ B' → B' = B)
    (hP₀ : P₀ ≤ B ∧ P₀.Normal ∧
      ∀ N : Subgroup P, N.Normal → N ≤ B → N ≤ P₀)
    (A : Subgroup G) (hAS : A ≤ S) (hSP : S ≤ P)
    (a : G) (haA : a ∈ A)
    (haCore : a ∉ Stellmacher.twoCoreAmbient P)
    (hsolv : Group.IsSolvable P) :
    let _ : P₀.Normal := hP₀.2.1
    let q₀ : P →* P ⧸ P₀ := QuotientGroup.mk' P₀
    q₀ ⟨a, hSP (hAS haA)⟩ ∉
      Subgroup.centralizer
        (Stellmacher.twoResidualAmbient
          (⊤ : Subgroup (P ⧸ P₀)) : Set (P ⧸ P₀)) := by
  classical
  dsimp only
  let _ : P₀.Normal := hP₀.2.1
  have hP₀eq : P₀ = B.normalCore := by
    apply le_antisymm
    · exact Subgroup.normal_le_normalCore.mpr hP₀.1
    · exact hP₀.2.2 B.normalCore inferInstance B.normalCore_le
  subst P₀
  let _ : B.normalCore.Normal := hP₀.2.1
  let q₀ : P →* P ⧸ B.normalCore := QuotientGroup.mk' B.normalCore
  let SP : Subgroup P := S.subgroupOf P
  have h33 := Stellmacher.SectionThree.lemma_three_three S h P hP B B.normalCore hB hP₀ hsolv
  obtain ⟨p, hp, hpodd, hRp⟩ := h33.part_a
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₂, hS₂map⟩ := hP.1.2.1
  have hSPmap : SP.map P.subtype = S :=
    Subgroup.map_subgroupOf_eq_of_le hSP
  have hS₂eq : (S₂ : Subgroup P) = SP := by
    apply Subgroup.map_injective_of_ker_le P.subtype (by simp) (by simp)
    rw [hS₂map, hSPmap]
  obtain ⟨pK, K, hpK, hpKodd, hKnormal, hKelem, hKinfB,
      hKsup, _hKirred⟩ :=
    Stellmacher.SectionThree.quotientCoreFree_data SP B S₂ hS₂eq
      hB.1 hB.2.1 hB.2.2 hsolv
  let Tbar : Subgroup (P ⧸ B.normalCore) := SP.map q₀
  let Bbar : Subgroup (P ⧸ B.normalCore) := B.map q₀
  have hq₀surj : Function.Surjective q₀ := QuotientGroup.mk'_surjective B.normalCore
  have hP₀leB : B.normalCore ≤ B := hP₀.1
  have hcomapBbar : Bbar.comap q₀ = B := by
    simpa [Bbar, q₀, QuotientGroup.ker_mk', sup_eq_left.2 hP₀leB] using
      (Subgroup.comap_map_eq q₀ B)
  have hBbarcore : Bbar.normalCore = ⊥ := by
    apply le_antisymm
    · intro x hx
      obtain ⟨y, rfl⟩ := hq₀surj x
      have hycore : y ∈ Bbar.normalCore.comap q₀ := hx
      have hcomapNormal : (Bbar.normalCore.comap q₀).Normal :=
        (inferInstance : Bbar.normalCore.Normal).comap q₀
      have hcomap_le_B : Bbar.normalCore.comap q₀ ≤ B := by
        exact (Subgroup.comap_mono Bbar.normalCore_le).trans_eq hcomapBbar
      have hcomap_le_P₀ : Bbar.normalCore.comap q₀ ≤ B.normalCore :=
        hP₀.2.2 (Bbar.normalCore.comap q₀) hcomapNormal hcomap_le_B
      exact (QuotientGroup.eq_one_iff y).2 (hcomap_le_P₀ hycore)
    · exact bot_le
  have hTBbar : Tbar ≤ Bbar := Subgroup.map_mono hB.2.1
  have hKcomm : IsMulCommutative K := hKelem.toIsMulCommutative
  have hKinfBbar : K ⊓ Bbar = ⊥ := by
    simpa [Bbar, q₀] using hKinfB
  have hKsupTbar : K ⊔ Tbar = ⊤ := by
    simpa [Tbar, q₀] using hKsup
  let Tbar₂ : Sylow 2 (P ⧸ B.normalCore) :=
    S₂.mapSurjective hq₀surj
  have hTbar₂ : (Tbar₂ : Subgroup (P ⧸ B.normalCore)) = Tbar := by
    change (S₂ : Subgroup P).map q₀ = SP.map q₀
    rw [hS₂eq]
  have hpKne : pK ≠ 2 := by
    rintro rfl
    obtain ⟨k, hk⟩ := hpKodd
    omega
  have hKp : IsPGroup pK K := by
    let _ : IsElementaryAbelian pK K := hKelem
    exact IsElementaryAbelian.isPGroup pK K
  have hresK :
      Stellmacher.twoResidualAmbient
          (⊤ : Subgroup (P ⧸ B.normalCore)) = K :=
    Stellmacher.SectionThree.twoResidualAmbient_top_eq_of_normal_complement_sylow_two
      hpK hpKne K Tbar Tbar₂ hTbar₂ hKnormal hKp hKsupTbar
  let aP : P := ⟨a, hSP (hAS haA)⟩
  have hqaTbar : q₀ aP ∈ Tbar := by
    exact Subgroup.mem_map_of_mem q₀ (show aP ∈ SP from hAS haA)
  intro hcentral
  have hcentralK : q₀ aP ∈ Subgroup.centralizer (K : Set _) := by
    rw [← hresK]
    exact hcentral
  have hqaone : q₀ aP = 1 :=
    sylow_element_eq_one_of_centralizes_corefree_complement
      K Tbar Bbar hKnormal hKcomm hKsupTbar hTBbar hBbarcore
      hKinfBbar (q₀ aP) hqaTbar hcentralK
  have haP₀ : aP ∈ B.normalCore :=
    (QuotientGroup.eq_one_iff (N := B.normalCore) aP).1 hqaone
  let O : Subgroup P := pCore 2 P
  let qO : P →* P ⧸ O := QuotientGroup.mk' O
  let R : Subgroup (P ⧸ O) :=
    Stellmacher.twoResidualAmbient
      (⊤ : Subgroup (P ⧸ O))
  let TbarO : Subgroup (P ⧸ O) := SP.map qO
  have hqaPhi : qO aP ∈ Stellmacher.frattiniAmbient R := by
    rw [← h33.part_c]
    exact Subgroup.mem_map_of_mem qO haP₀
  have hqaR : qO aP ∈ R := by
    rcases hqaPhi with ⟨r, hr, hre⟩
    exact hre ▸ r.property
  have hSPtwo : IsPGroup 2 SP := by
    rw [← hS₂eq]
    exact S₂.isPGroup'
  have hTbarOtwo : IsPGroup 2 TbarO := IsPGroup.map hSPtwo qO
  have hqaTbarO : qO aP ∈ TbarO :=
    Subgroup.mem_map_of_mem qO (show aP ∈ SP from hAS haA)
  have hpne : p ≠ 2 := by
    rintro rfl
    obtain ⟨k, hk⟩ := hpodd
    omega
  have hdisj : Disjoint TbarO R :=
    IsPGroup.disjoint_of_ne 2 p hpne.symm TbarO R hTbarOtwo hRp
  have hqaOone : qO aP = 1 := by
    have : qO aP ∈ TbarO ⊓ R := ⟨hqaTbarO, hqaR⟩
    have : qO aP ∈ (⊥ : Subgroup (P ⧸ O)) := by
      rw [← hdisj.eq_bot]
      exact this
    simpa using this
  apply haCore
  exact Subgroup.mem_map_of_mem P.subtype
    ((QuotientGroup.eq_one_iff (N := O) aP).1 hqaOone)

end
