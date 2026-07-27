module
public import Submission.FeitThompson.BGsection3.Defs

public import Submission.FeitThompson.BGsection4.proposition_4_4_a

section Main

public theorem proposition_4_4_b {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (A : Subgroup P)
    (hA : A ∈ selfCentralizingAbelianSubgroups P) :
    ∃ H : Subgroup G, Nat.Coprime p (Nat.card H) ∧
      Subgroup.centralizer ((A.map (P : Subgroup G).subtype : Subgroup G) : Set G) =
        (A.map (P : Subgroup G).subtype) ⊔ H ∧
      Disjoint (A.map (P : Subgroup G).subtype) H ∧
      ⁅A.map (P : Subgroup G).subtype, H⁆ = ⊥ := by
  classical
  let A' : Subgroup G := A.map (P : Subgroup G).subtype
  let C : Subgroup G := Subgroup.centralizer A'
  let N : Subgroup G := Subgroup.normalizer A'
  have hA_norm : A.Normal := hA.1
  have hAcomm : IsMulCommutative A := by
    exact (Subgroup.le_centralizer_iff_isMulCommutative (K := A)).1 <|
      by simp [hA.2]
  letI : IsMulCommutative A := hAcomm
  letI : IsMulCommutative A' := Subgroup.map_isMulCommutative A (P : Subgroup G).subtype
  have hA'leP : A' ≤ (P : Subgroup G) := Subgroup.map_subtype_le A
  have hA'_sub_eq : A'.subgroupOf (P : Subgroup G) = A := by
    apply (Subgroup.map_injective (f := (P : Subgroup G).subtype) Subtype.coe_injective)
    simpa [A'] using
      (Subgroup.map_subgroupOf_eq_of_le (H := A') (K := (P : Subgroup G)) hA'leP)
  have hA'_sub_norm : (A'.subgroupOf (P : Subgroup G)).Normal := by
    simpa [hA'_sub_eq] using hA_norm
  have hP_le_N : (P : Subgroup G) ≤ N := by
    letI : (A'.subgroupOf (P : Subgroup G)).Normal := hA'_sub_norm
    simpa [N] using
      (Subgroup.le_normalizer_of_normal_subgroupOf (H := A') (K := (P : Subgroup G)) hA'leP)
  have hA'leN : A' ≤ N := by
    simpa [N] using (Subgroup.le_normalizer : A' ≤ Subgroup.normalizer A')
  have hA'leC : A' ≤ C :=
    (Subgroup.le_centralizer_iff_isMulCommutative (K := A')).2 inferInstance
  have hC_le_N : C ≤ N := by
    intro g hg
    change g ∈ Subgroup.normalizer A'
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      have hcomm : a * g = g * a := (Subgroup.mem_centralizer_iff.mp hg) a ha
      have : g * a * g⁻¹ = a := by
        calc
          g * a * g⁻¹ = a * g * g⁻¹ := by rw [← hcomm, mul_assoc]
          _ = a := by simp
      exact this.symm ▸ ha
    · intro hconj
      have hcomm :
          (g * a * g⁻¹) * g = g * (g * a * g⁻¹) :=
        (Subgroup.mem_centralizer_iff.mp hg) (g * a * g⁻¹) hconj
      have : a = g * a * g⁻¹ := by
        calc
          a = g⁻¹ * (g * a * g⁻¹) * g := by simp [mul_assoc]
          _ = g * a * g⁻¹ := by
            simpa [mul_assoc] using congrArg (fun t : G => g⁻¹ * t) hcomm
      exact this ▸ hconj
  have hCsub_eq_A : C.subgroupOf (P : Subgroup G) = A := by
    ext x
    constructor
    · intro hx
      have hxcent : (x : G) ∈ C := hx
      have hxPcent : x ∈ Subgroup.centralizer (A : Set P) := by
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        apply Subtype.ext
        exact (Subgroup.mem_centralizer_iff.mp hxcent) (a : P)
          (show ((a : P) : G) ∈ A' from Subgroup.mem_map_of_mem (P : Subgroup G).subtype ha)
      simpa [hA.2] using hxPcent
    · intro hx
      have hxcent : x ∈ Subgroup.centralizer (A : Set P) := by simpa [hA.2] using hx
      change ((x : P) : G) ∈ C
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rcases hy with ⟨y', hy', rfl⟩
      exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp hxcent) y' hy')
  have hPC_eq_A' : C ⊓ (P : Subgroup G) = A' := by
    calc
      C ⊓ (P : Subgroup G) = (C.subgroupOf (P : Subgroup G)).map (P : Subgroup G).subtype := by
        symm
        exact Subgroup.subgroupOf_map_subtype C (P : Subgroup G)
      _ = A' := by simpa [A'] using congrArg (fun K => K.map (P : Subgroup G).subtype) hCsub_eq_A
  let A0N : Subgroup N := A'.subgroupOf N
  have hA0N_norm : A0N.Normal := by
    simpa [A0N, N] using
      (inferInstance : (A'.subgroupOf (Subgroup.normalizer A')).Normal)
  letI : A0N.Normal := hA0N_norm
  letI : IsMulCommutative A0N := inferInstance
  let Cn : Subgroup N := Subgroup.centralizer A0N
  have hCn_eq : Cn = C.subgroupOf N := by
    ext x
    constructor
    · intro hx
      change ((x : N) : G) ∈ C
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact congrArg Subtype.val <|
        (Subgroup.mem_centralizer_iff.mp hx) ⟨a, hA'leN ha⟩ (by
          change (a : G) ∈ A'
          exact ha)
    · intro hx
      have hxC : ((x : N) : G) ∈ C := hx
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp hxC) (a : N) (by
        change ((a : N) : G) ∈ A' at ha
        exact ha)
  have hCn_set_eq : (Cn : Set N) = (C.subgroupOf N : Set N) :=
    congrArg (fun K : Subgroup N => (K : Set N)) hCn_eq
  have hCn_normal : Cn.Normal := by
    exact inferInstance
  letI : Cn.Normal := hCn_normal
  have hA0N_le_Cn : A0N ≤ Cn :=
    (Subgroup.le_centralizer_iff_isMulCommutative (K := A0N)).2 inferInstance
  let A0 : Subgroup Cn := A0N.subgroupOf Cn
  have hA0_map : A0.map Cn.subtype = A0N := by
    simpa [A0] using
      (Subgroup.map_subgroupOf_eq_of_le (H := A0N) (K := Cn) hA0N_le_Cn)
  have hA0N_map : A0N.map N.subtype = A' := by
    simpa [A0N] using (Subgroup.map_subgroupOf_eq_of_le (H := A') (K := N) hA'leN)
  have hA0N_p : IsPGroup p A0N := by
    have hAp : IsPGroup p A := P.2.to_subgroup A
    have hA'p : IsPGroup p A' := hAp.map (P : Subgroup G).subtype
    change IsPGroup p (A'.comap N.subtype)
    exact hA'p.comap_subtype (K := N)
  have hA0_p : IsPGroup p A0 := by
    change IsPGroup p (A0N.comap Cn.subtype)
    exact hA0N_p.comap_subtype (K := Cn)
  have hA0_norm : A0.Normal := by
    simpa [A0] using hA0N_norm.subgroupOf Cn
  letI : A0.Normal := hA0_norm
  let Pn : Sylow p N := P.subtype hP_le_N
  have hPCN_eq_A0N : (Pn : Subgroup N) ⊓ Cn = A0N := by
    ext x
    constructor
    · intro hx
      have hxG : (x : G) ∈ C ⊓ (P : Subgroup G) := by
        refine ⟨?_, hx.1⟩
        have hxC : x ∈ Cn := hx.2
        rw [hCn_eq] at hxC
        change (x : G) ∈ C at hxC
        exact hxC
      change (x : G) ∈ A'
      rw [← hPC_eq_A']
      exact hxG
    · intro hx
      have hxG : (x : G) ∈ A' := by
        change (x : G) ∈ A' at hx
        exact hx
      have hxPC : (x : G) ∈ C ⊓ (P : Subgroup G) := by simpa [hPC_eq_A'] using hxG
      refine ⟨hxPC.2, ?_⟩
      rw [hCn_eq]
      exact hxPC.1
  obtain ⟨SA, hA0_le_SA⟩ := IsPGroup.exists_le_sylow (G := Cn) (p := p) hA0_p
  obtain ⟨Q, hQeq⟩ := SA.exists_comap_subtype_eq
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq N Q Pn
  let e : Cn ≃* Cn := MulAut.conjNormal (H := Cn) (n : N)
  have hQmap : (Q : Subgroup N).map (MulAut.conj (n : N)).toMonoidHom = (Pn : Subgroup N) := by
    have hhom :
        (MulAut.conj (n : N)).toMonoidHom =
          MulDistribMulAction.toMonoidEnd (MulAut N) N (MulAut.conj (n : N)) := by
      ext x
      rfl
    rw [hhom]
    rw [← Subgroup.pointwise_smul_def]
    exact congrArg (fun S : Sylow p N => (S : Subgroup N)) hn
  have hA0_map_fix : A0.map e.toMonoidHom = A0 := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hyA0N : (y : N) ∈ A0N := by
        change (y : N) ∈ A0N at hy
        exact hy
      change ((e y : Cn) : N) ∈ A0N
      change ((n : N) : G) * (y : N) * ((n : N) : G)⁻¹ ∈ A'
      exact ((Subgroup.mem_normalizer_iff.mp n.2) (y : N)).1 hyA0N
    · intro hx
      have hyCn : (n : N)⁻¹ * (x : N) * (n : N) ∈ Cn := by
        exact hCn_normal.conj_mem' (n := (x : N)) x.2 (g := (n : N))
      have hxA0N : (x : N) ∈ A0N := by
        change (x : N) ∈ A0N at hx
        exact hx
      have hyA0N : (n : N)⁻¹ * (x : N) * (n : N) ∈ A0N := by
        change ((n : N) : G)⁻¹ * (x : N) * (n : N) ∈ A'
        change ((x : N) : G) ∈ A' at hxA0N
        exact ((Subgroup.mem_normalizer_iff.mp n.2) ((n : N)⁻¹ * (x : N) * (n : N))).2 <|
          by simpa [mul_assoc] using hxA0N
      refine Subgroup.mem_map.mpr ?_
      refine ⟨⟨(n : N)⁻¹ * (x : N) * (n : N), hyCn⟩, ?_, ?_⟩
      · change (n : N)⁻¹ * (x : N) * (n : N) ∈ A0N at hyA0N
        exact hyA0N
      · apply Subtype.ext
        simp [e, mul_assoc]
  have hSA_map_eq_A0 : (SA : Subgroup Cn).map e.toMonoidHom = A0 := by
    ext x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hyS, hyx⟩
      have hyQ : (y : N) ∈ (Q : Subgroup N) := by
        have hyS' : y ∈ (SA : Subgroup Cn) := hyS
        rw [← hQeq] at hyS'
        exact hyS'
      have hxPn : (x : N) ∈ (Pn : Subgroup N) := by
        rw [← hQmap]
        refine Subgroup.mem_map.mpr ?_
        refine ⟨(y : N), hyQ, ?_⟩
        simpa [e] using congrArg (fun t : Cn => (t : N)) hyx
      have hxPCN : (x : N) ∈ (Pn : Subgroup N) ⊓ Cn := ⟨hxPn, x.2⟩
      have hxA0N : (x : N) ∈ A0N := by
        simpa [hPCN_eq_A0N] using hxPCN
      change x ∈ A0N.subgroupOf Cn
      exact hxA0N
    · intro hx
      have hxA0N : (x : N) ∈ A0N := by
        change (x : N) ∈ A0N at hx
        exact hx
      have hxPCN : (x : N) ∈ (Pn : Subgroup N) ⊓ Cn := by simpa [hPCN_eq_A0N] using hxA0N
      have hxQconj : (x : N) ∈ (Q : Subgroup N).map (MulAut.conj (n : N)).toMonoidHom := by
        rw [hQmap]
        exact hxPCN.1
      rcases Subgroup.mem_map.mp hxQconj with ⟨y, hyQ, hyx⟩
      have hyCn : y ∈ Cn := by
        have hyCn' : (n : N)⁻¹ * (x : N) * (n : N) ∈ Cn := by
          exact hCn_normal.conj_mem' (n := (x : N)) hxPCN.2 (g := (n : N))
        have hy_eq : y = (n : N)⁻¹ * (x : N) * (n : N) := by
          simpa [MulAut.conj_apply, mul_assoc] using
            congrArg (fun t : N => (n : N)⁻¹ * t * (n : N)) hyx
        simpa [hy_eq] using hyCn'
      have hyS : ⟨y, hyCn⟩ ∈ SA := by
        have hyS' : ⟨y, hyCn⟩ ∈ (Q : Subgroup N).comap Cn.subtype := hyQ
        change ⟨y, hyCn⟩ ∈ (SA : Subgroup Cn)
        rw [← hQeq]
        exact hyS'
      refine Subgroup.mem_map.mpr ?_
      refine ⟨⟨y, hyCn⟩, hyS, ?_⟩
      apply Subtype.ext
      simpa [e, MulAut.conj_apply] using hyx
  have hSA_eq_A0 : (SA : Subgroup Cn) = A0 := by
    have hmap_eq : (SA : Subgroup Cn).map e.toMonoidHom = A0.map e.toMonoidHom := by
      calc
        (SA : Subgroup Cn).map e.toMonoidHom = A0 := hSA_map_eq_A0
        _ = A0.map e.toMonoidHom := hA0_map_fix.symm
    exact (Subgroup.map_injective (f := e.toMonoidHom) e.injective) hmap_eq
  have hnot_dvd_index_A0 : ¬ p ∣ A0.index := by
    simpa [hSA_eq_A0] using SA.not_dvd_index
  have hcop_index : Nat.Coprime p A0.index :=
    (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).2 hnot_dvd_index_A0
  have hcop_card_index : Nat.Coprime (Nat.card A0) A0.index := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hA0_p
    rw [hm]
    exact Nat.Coprime.pow_left m hcop_index
  obtain ⟨H0, hcompl⟩ := Subgroup.exists_right_complement'_of_coprime (N := A0) hcop_card_index
  let iC : Cn →* G := N.subtype.comp Cn.subtype
  let H : Subgroup G := H0.map iC
  have hA0_map_iC : A0.map iC = A' := by
    calc
      A0.map iC = (A0.map Cn.subtype).map N.subtype := by rw [Subgroup.map_map]
      _ = A0N.map N.subtype := by rw [hA0_map]
      _ = A' := hA0N_map
  have htop_map_iC : (⊤ : Subgroup Cn).map iC = C := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      have hyCsub : (y : N) ∈ (C.subgroupOf N : Set N) := by
        rw [← hCn_set_eq]
        exact y.2
      change ((y : N) : G) ∈ C at hyCsub
      change ((y : N) : G) ∈ C
      exact hyCsub
    · intro hx
      refine ⟨⟨⟨x, hC_le_N hx⟩, ?_⟩, by simp, rfl⟩
      rw [hCn_eq]
      exact hx
  have hiC_injective : Function.Injective iC :=
    by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact hxy
  have hH_card : Nat.card H = Nat.card H0 := Subgroup.card_map_of_injective (f := iC) hiC_injective
  have hH_coprime : Nat.Coprime p (Nat.card H) := by
    rw [hH_card]
    exact hcompl.card_right.symm ▸ hcop_index
  have hcent_eq : C = A' ⊔ H := by
    calc
      C = (⊤ : Subgroup Cn).map iC := by symm; exact htop_map_iC
      _ = (A0 ⊔ H0).map iC := by simp [hcompl.sup_eq_top]
      _ = A0.map iC ⊔ H0.map iC := by rw [Subgroup.map_sup]
      _ = A' ⊔ H := by simp [H, hA0_map_iC]
  have hdis : Disjoint A' H := by
    have : Disjoint (A0.map iC) (H0.map iC) := Subgroup.disjoint_map hiC_injective hcompl.disjoint
    simpa [H, hA0_map_iC] using this
  have hH_le_C : H ≤ C := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    have hyCsub : (y : N) ∈ (C.subgroupOf N : Set N) := by
      rw [← hCn_set_eq]
      exact y.2
    change ((y : N) : G) ∈ C at hyCsub
    change ((y : N) : G) ∈ C
    exact hyCsub
  refine ⟨H, hH_coprime, ?_, hdis, ?_⟩
  · simpa [A', C] using hcent_eq
  · exact
      (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := A') (H₂ := H)).2 <|
        (Subgroup.le_centralizer_iff).mp hH_le_C


end Main
