module

public import FeitThompson.BGsection1.Defs
public import Theory.GroupTheory.CoprimeQuotientNormalizer
import FeitThompson.Fitting.Centralizer


open scoped Pointwise commutatorElement

public lemma centralizer_le_normalizer {G : Type*} [Group G] (R : Subgroup G) :
    Subgroup.centralizer (R : Set G) ≤ Subgroup.normalizer R := by
  intro x hxC
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have hxy : y * x = x * y := (Subgroup.mem_centralizer_iff.mp hxC) y hy
    have hconj : x * y * x⁻¹ = y := by
      calc
        x * y * x⁻¹ = (x * y) * x⁻¹ := by simp [mul_assoc]
        _ = (y * x) * x⁻¹ := by rw [hxy.symm]
        _ = y := by simp [mul_assoc]
    simpa [hconj] using hy
  · intro hy
    have hxinvC : x⁻¹ ∈ Subgroup.centralizer (R : Set G) :=
      (Subgroup.inv_mem_iff (H := Subgroup.centralizer (R : Set G))).2 hxC
    have hy' : x⁻¹ * (x * y * x⁻¹) * x ∈ R := by
      have hyc : x * y * x⁻¹ ∈ R := hy
      have hxy : (x * y * x⁻¹) * x⁻¹ = x⁻¹ * (x * y * x⁻¹) :=
        (Subgroup.mem_centralizer_iff.mp hxinvC) (x * y * x⁻¹) hyc
      have hconj : x⁻¹ * (x * y * x⁻¹) * x = x * y * x⁻¹ := by
        calc
          x⁻¹ * (x * y * x⁻¹) * x = (x⁻¹ * (x * y * x⁻¹)) * x := by simp [mul_assoc]
          _ = ((x * y * x⁻¹) * x⁻¹) * x := by rw [hxy]
          _ = x * y * x⁻¹ := by simp [mul_assoc]
      simpa [hconj] using hyc
    simpa [mul_assoc] using hy'

public lemma centralizer_subgroupOf_normalizer_eq {G : Type*} [Group G] (R : Subgroup G) :
    Subgroup.centralizer ((R.subgroupOf (Subgroup.normalizer R)) : Set (Subgroup.normalizer (R : Set G))) =
      (Subgroup.centralizer (R : Set G)).subgroupOf (Subgroup.normalizer (R : Set G)) := by
  let N : Subgroup G := Subgroup.normalizer R
  ext x
  constructor
  · intro hx
    change (x : G) ∈ Subgroup.centralizer (R : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    let yN : N := ⟨y, (Subgroup.le_normalizer (H := R)) hy⟩
    have hyN : yN ∈ R.subgroupOf N := hy
    have hcomm := (Subgroup.mem_centralizer_iff.mp hx) yN hyN
    exact congrArg Subtype.val hcomm
  · intro hx
    change (x : G) ∈ Subgroup.centralizer (R : Set G) at hx
    rw [Subgroup.mem_centralizer_iff] at hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    apply Subtype.ext
    exact hx (y : G) hy

public theorem Subgroup.le_centralizer_sup_of_le_centralizers
    {G : Type*} [Group G] {R A B : Subgroup G}
    (hRA : R ≤ Subgroup.centralizer (A : Set G))
    (hRB : R ≤ Subgroup.centralizer (B : Set G)) :
    R ≤ Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) := by
  intro r hr
  rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  intro x hx
  rcases hx with hxA | hxB
  · exact Subgroup.mem_centralizer_iff.mp (hRA hr) x hxA
  · exact Subgroup.mem_centralizer_iff.mp (hRB hr) x hxB

public theorem Subgroup.le_normalizer_inf
    {G : Type*} [Group G] {A H K : Subgroup G}
    (hAH : A ≤ Subgroup.normalizer (H : Set G))
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) :
    A ≤ Subgroup.normalizer (H ⊓ K : Set G) := by
  intro a ha
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hAH ha, hAK ha⟩

public lemma pPrimeCore_le_centralizer_of_normal_pgroup {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (R : Subgroup G) [R.Normal] (hRp : IsPGroup p (↥R)) :
    pPrimeCore p G ≤ Subgroup.centralizer (R : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff_commutator_eq_one]
  intro r hr
  have hcomm : ⁅r, x⁆ ∈ ⁅R, pPrimeCore p G⁆ :=
    Subgroup.commutator_mem_commutator hr hx
  have hle : ⁅R, pPrimeCore p G⁆ ≤ R ⊓ pPrimeCore p G :=
    Subgroup.commutator_le_inf (H₁ := R) (H₂ := pPrimeCore p G)
  have hcomm_inf : ⁅r, x⁆ ∈ R ⊓ pPrimeCore p G := hle hcomm
  have hcopR : Nat.Coprime (Nat.card R) (Nat.card (pPrimeCore p G)) := by
    rcases hRp.exists_card_eq with ⟨n, hn⟩
    rw [hn]
    exact (pPrimeCore_coprime_card (G := G) (p := p)).pow_left n
  have hinf_bot : R ⊓ pPrimeCore p G = ⊥ :=
    disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcopR)
  have hcomm_bot : ⁅r, x⁆ ∈ (⊥ : Subgroup G) := by
    simpa [hinf_bot] using hcomm_inf
  simpa using hcomm_bot

public theorem le_pPrimeCore_of_le_Op_p'p_of_coprime {G : Type*} [Group G] (p : ℕ) [Fact p.Prime]
    {H : Subgroup G} (hHle : H ≤ Op_p'p p G) (hcop : Nat.Coprime p (Nat.card H)) :
    H ≤ pPrimeCore p G := by
  let M : Subgroup G := pPrimeCore p G
  let q : G →* G ⧸ M := QuotientGroup.mk' M
  have hmap_op : (Op_p'p p G).map q = pCore p (G ⧸ M) := by
    dsimp [Op_p'p, q, M]
    simpa using
      (Subgroup.map_comap_eq_self_of_surjective
        (f := QuotientGroup.mk' (pPrimeCore p G))
        (h := QuotientGroup.mk'_surjective (pPrimeCore p G))
        (H := pCore p (G ⧸ pPrimeCore p G)))
  have hHmap_le : H.map q ≤ pCore p (G ⧸ M) :=
    (Subgroup.map_mono hHle).trans hmap_op.le
  have hHmap_p : IsPGroup p (H.map q) :=
    IsPGroup.to_le (hK := pCore_isPGroup (p := p) (G := (G ⧸ M))) hHmap_le
  have hHmap_coprime : Nat.Coprime p (Nat.card (H.map q)) := by
    exact Nat.Coprime.of_dvd_right (Subgroup.card_map_dvd (H := H) q) hcop
  have hHmap_card_eq_one : Nat.card (H.map q) = 1 := by
    rcases hHmap_p.card_eq_or_dvd with h1 | hpdvd
    · exact h1
    · exfalso
      exact ((Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).1 hHmap_coprime) hpdvd
  have hHmap_bot : H.map q = ⊥ := Subgroup.card_eq_one.mp hHmap_card_eq_one
  have hHle_ker : H ≤ q.ker := by
    intro x hx
    have hxmap : q x ∈ H.map q := Subgroup.mem_map_of_mem q hx
    have hx1 : q x = 1 := by
      have hxbot : q x ∈ (⊥ : Subgroup (G ⧸ M)) := by simpa [hHmap_bot] using hxmap
      simpa using hxbot
    simpa [MonoidHom.mem_ker] using hx1
  simpa [q, M] using hHle_ker

/-
**Kind**: Theorem
**Note**: Lemma 1.14
**Stmt**:
Let $p$ be a prime.
Let $T$ be a $p$-subgroup of a finite group $G$.
Let $M$ be a normal $p'$-subgroup of $G$.
Let $C = C_G(T)$ and $N = N_G(T)$.
Then
\[ C_{G/M}(TM/M) = CM/M \]
and
\[ N_{G/M}(TM/M) = NM/M. \]
-/

-- Lemma 1.14 (centralizer statement)
public theorem centralizer_map_quotient_eq_map_centralizer
    {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (T M : Subgroup G)
    [Fact (IsPGroup p (↥T))] (hM : M.Normal) (hcop : Nat.Coprime p (Nat.card M)) :
    let q : G →* G ⧸ M := QuotientGroup.mk' M
    Subgroup.centralizer ((T.map q : Subgroup (G ⧸ M)) : Set (G ⧸ M)) =
      (Subgroup.centralizer (T : Set G)).map q := by
  intro q
  let _ : M.Normal := hM
  have hnormq : Subgroup.normalizer (T.map q) = (Subgroup.normalizer T).map q := by
    simpa [q] using (normalizer_map_quotient_eq_map_normalizer (G := G) (p := p) T M hM hcop)
  have hinf_bot : M ⊓ T = ⊥ := by
    rcases (Fact.out : IsPGroup p (↥T)).exists_card_eq with ⟨n, hn⟩
    have hcopMT : Nat.Coprime (Nat.card M) (Nat.card T) := by
      rw [hn]
      exact hcop.symm.pow_right n
    exact disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcopMT)
  refine le_antisymm ?_ ?_
  · intro x hxC
    have hconj_mem {g y : G ⧸ M}
        (hg : g ∈ Subgroup.centralizer ((T.map q : Subgroup (G ⧸ M)) : Set (G ⧸ M)))
        (hy : y ∈ T.map q) :
        g * y * g⁻¹ ∈ T.map q := by
      have hcomm := (Subgroup.mem_centralizer_iff (g := g)
        (s := ((T.map q : Subgroup (G ⧸ M)) : Set (G ⧸ M)))).1 hg y hy
      have hxy : g * y * g⁻¹ = y := by
        calc
          g * y * g⁻¹ = (g * y) * g⁻¹ := by simp [mul_assoc]
          _ = (y * g) * g⁻¹ := by rw [hcomm]
          _ = y := by simp [mul_assoc]
      simpa [hxy] using hy
    have hxN : x ∈ Subgroup.normalizer (T.map q) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        exact hconj_mem hxC hy
      · intro hy
        have hxinvC : x⁻¹ ∈ Subgroup.centralizer ((T.map q : Subgroup (G ⧸ M)) : Set (G ⧸ M)) :=
          (Subgroup.inv_mem_iff (H := Subgroup.centralizer ((T.map q : Subgroup (G ⧸ M)) : Set (G ⧸ M)))).2 hxC
        have : x⁻¹ * (x * y * x⁻¹) * x ∈ T.map q := by
          simpa using hconj_mem hxinvC hy
        simpa [mul_assoc] using this
    rw [hnormq] at hxN
    rcases Subgroup.mem_map.mp hxN with ⟨n, hnN, rfl⟩
    have hqnC : q n ∈ Subgroup.centralizer ((T.map q : Subgroup (G ⧸ M)) : Set (G ⧸ M)) := hxC
    have hn_cent : n ∈ Subgroup.centralizer (T : Set G) := by
      rw [Subgroup.mem_centralizer_iff_commutator_eq_one]
      intro t ht
      have htmap : q t ∈ (T.map q : Subgroup (G ⧸ M)) := by
        exact ⟨t, ht, rfl⟩
      have hcomm_q : q t * q n = q n * q t :=
        (Subgroup.mem_centralizer_iff (g := q n)
          (s := ((T.map q : Subgroup (G ⧸ M)) : Set (G ⧸ M)))).1 hqnC (q t) htmap
      have hq_comm_elem : q (n * t * n⁻¹ * t⁻¹) = 1 := by
        calc
          q (n * t * n⁻¹ * t⁻¹) = q n * q t * (q n)⁻¹ * (q t)⁻¹ := by simp [mul_assoc]
          _ = q t * q n * (q n)⁻¹ * (q t)⁻¹ := by rw [hcomm_q]
          _ = 1 := by simp [mul_assoc]
      have hm_comm : n * t * n⁻¹ * t⁻¹ ∈ M := (QuotientGroup.eq_one_iff (N := M) _).1 hq_comm_elem
      have ht_norm : n * t * n⁻¹ ∈ T := ((Subgroup.mem_normalizer_iff).1 hnN t).1 ht
      have ht_comm : n * t * n⁻¹ * t⁻¹ ∈ T := T.mul_mem ht_norm (T.inv_mem ht)
      have hbot : n * t * n⁻¹ * t⁻¹ ∈ (⊥ : Subgroup G) := by
        rw [← hinf_bot]
        exact ⟨hm_comm, ht_comm⟩
      have hcomm_elem : n * t * n⁻¹ * t⁻¹ = 1 := by simpa using hbot
      have hcomm_elem' := congrArg Inv.inv hcomm_elem
      simpa [commutatorElement_def, mul_assoc] using hcomm_elem'
    exact ⟨n, hn_cent, rfl⟩
  · simpa using
      (Subgroup.map_centralizer_le_centralizer_image (s := (T : Set G)) q)

/-
**Kind**: Theorem
**Note**: Proposition 1.15
**Stmt**:
Let $G$ be a finite solvable group.
Let $p$ be a prime.
(a) If $T$ is a Sylow $p$-subgroup of $\mathcal{O}_{p',p}(G)$. Then $C_G(T) \subset \mathcal{O}_{p',p}(G)$.
(b) If $R$ is a $p$-subgroup of $G$. Then $\mathcal{O}_{p'}(C_G(R)) \subset \mathcal{O}_{p'}(G)$.
-/

-- Proposition 1.15(a)
public theorem centralizer_sylow_subgroup_le_op_p_prime_p_of_solvable
    {G : Type*} [Group G] [Finite G] (hsolv : Group.IsSolvable G) (p : ℕ) [Fact p.Prime] :
    ∀ T : Sylow p (↥(Op_p'p p G)),
      Subgroup.centralizer ((T.1.map (Op_p'p p G).subtype : Subgroup G) : Set G) ≤ Op_p'p p G := by
  intro T
  let M : Subgroup G := pPrimeCore p G
  let q : G →* G ⧸ M := QuotientGroup.mk' M
  let TG : Subgroup G := T.1.map (Op_p'p p G).subtype
  let Tbar : Subgroup (G ⧸ M) := TG.map q
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective M
  have hMnormal : M.Normal := by infer_instance
  have hMcop : Nat.Coprime p (Nat.card M) := by
    simpa [M] using (pPrimeCore_coprime_card (G := G) (p := p))
  have hTG_p : IsPGroup p (↥TG) := by
    simpa [TG] using
      (IsPGroup.map (p := p) (H := (T : Subgroup (Op_p'p p G))) T.isPGroup' (Op_p'p p G).subtype)
  have hTG_le_op : TG ≤ Op_p'p p G := by
    simpa [TG] using
      (Subgroup.map_subtype_le (H := Op_p'p p G) (K := (T : Subgroup (Op_p'p p G))))
  have hmap_op : (Op_p'p p G).map q = pCore p (G ⧸ M) := by
    dsimp [Op_p'p, q, M]
    simpa using
      (Subgroup.map_comap_eq_self_of_surjective
        (f := QuotientGroup.mk' (pPrimeCore p G))
        (h := QuotientGroup.mk'_surjective (pPrimeCore p G))
        (H := pCore p (G ⧸ pPrimeCore p G)))
  have hTbar_le_pcore : Tbar ≤ pCore p (G ⧸ M) := by
    exact (Subgroup.map_mono hTG_le_op).trans hmap_op.le
  let f : Op_p'p p G →* pCore p (G ⧸ M) :=
    ((q.comp (Op_p'p p G).subtype)).codRestrict (pCore p (G ⧸ M)) (by
      intro x
      have hxmap : (q (x : G) : G ⧸ M) ∈ (Op_p'p p G).map q :=
        Subgroup.mem_map.mpr ⟨(x : G), x.property, rfl⟩
      exact hmap_op ▸ hxmap)
  have hf_surj : Function.Surjective f := by
    intro y
    rcases hqsurj y.1 with ⟨x, hx⟩
    refine ⟨⟨x, ?_⟩, ?_⟩
    · have hxmem : (q x : G ⧸ M) ∈ pCore p (G ⧸ M) := by simp [hx]
      simpa [Op_p'p, q, M] using hxmem
    · apply Subtype.ext
      simpa [f] using hx
  have hmapf_eq :
      (Subgroup.map f (T : Subgroup (Op_p'p p G))).map (pCore p (G ⧸ M)).subtype = Tbar := by
    ext z
    constructor
    · intro hz
      rcases Subgroup.mem_map.mp hz with ⟨x, hx, hxz⟩
      rcases Subgroup.mem_map.mp hx with ⟨t, ht, htx⟩
      refine Subgroup.mem_map.mpr ?_
      refine ⟨(t : Op_p'p p G), ?_, ?_⟩
      · exact Subgroup.mem_map.mpr ⟨t, ht, rfl⟩
      · rw [← hxz]
        exact congrArg Subtype.val htx
    · intro hz
      rcases Subgroup.mem_map.mp hz with ⟨x, hx, hxz⟩
      rcases Subgroup.mem_map.mp hx with ⟨t, ht, htx⟩
      refine Subgroup.mem_map.mpr ?_
      refine ⟨f t, ?_, ?_⟩
      · exact Subgroup.mem_map.mpr ⟨t, ht, rfl⟩
      · rw [← hxz]
        simpa [f] using congrArg q htx
  have hT_not_dvd : ¬ p ∣ (T : Subgroup (Op_p'p p G)).index := T.not_dvd_index
  have hidx_dvd :
      (Subgroup.map f (T : Subgroup (Op_p'p p G))).index ∣ (T : Subgroup (Op_p'p p G)).index :=
    Subgroup.index_map_dvd (H := (T : Subgroup (Op_p'p p G))) (f := f) hf_surj
  have hmapf_not_dvd : ¬ p ∣ (Subgroup.map f (T : Subgroup (Op_p'p p G))).index := by
    intro hp_dvd
    exact hT_not_dvd (hp_dvd.trans hidx_dvd)
  have hpcore_p : IsPGroup p (↥(pCore p (G ⧸ M))) := pCore_isPGroup (p := p) (G := (G ⧸ M))
  have hpow_idx :
      ∃ n, (Subgroup.map f (T : Subgroup (Op_p'p p G))).index = p ^ n := by
    exact IsPGroup.index (hG := hpcore_p) (H := Subgroup.map f (T : Subgroup (Op_p'p p G)))
  rcases hpow_idx with ⟨n, hn⟩
  have hnzero : n = 0 := by
    cases n with
    | zero =>
        rfl
    | succ n =>
        exfalso
        apply hmapf_not_dvd
        refine ⟨p ^ n, ?_⟩
        rw [hn]
        simp [Nat.pow_succ, Nat.mul_comm]
  have hidx_one : (Subgroup.map f (T : Subgroup (Op_p'p p G))).index = 1 := by
    rw [hn, hnzero]
    simp
  have hmapf_top : Subgroup.map f (T : Subgroup (Op_p'p p G)) = ⊤ :=
    (Subgroup.index_eq_one).1 hidx_one
  have hTbar_eq_pcore : Tbar = pCore p (G ⧸ M) := by
    have htop_map :
        (⊤ : Subgroup (pCore p (G ⧸ M))).map (pCore p (G ⧸ M)).subtype = pCore p (G ⧸ M) := by
      let K : Subgroup (G ⧸ M) := pCore p (G ⧸ M)
      have hsubtop : K.subgroupOf K = ⊤ := (Subgroup.subgroupOf_eq_top).2 le_rfl
      calc
        (⊤ : Subgroup K).map K.subtype = (K.subgroupOf K).map K.subtype := by rw [hsubtop]
        _ = K ⊓ K := Subgroup.subgroupOf_map_subtype (H := K) (K := K)
        _ = K := inf_eq_right.mpr le_rfl
    have hEq :
        Tbar = (⊤ : Subgroup (pCore p (G ⧸ M))).map (pCore p (G ⧸ M)).subtype := by
      calc
        Tbar = (Subgroup.map f (T : Subgroup (Op_p'p p G))).map (pCore p (G ⧸ M)).subtype := by
          exact hmapf_eq.symm
        _ = (⊤ : Subgroup (pCore p (G ⧸ M))).map (pCore p (G ⧸ M)).subtype := by
          rw [hmapf_top]
    exact hEq.trans htop_map
  have hcoreQ : pPrimeCore p (G ⧸ M) = ⊥ := by
    simpa [M] using (pPrimeCore_quotient_pPrimeCore_eq_bot (G := G) (p := p))
  let _ : Group.IsSolvable G := hsolv
  have hsolvQ : Group.IsSolvable (G ⧸ M) := by infer_instance
  have hfit_eq : fittingSubgroup (G ⧸ M) = pCore p (G ⧸ M) := Fitting_eq_pcore (G ⧸ M) p hcoreQ
  have hcent_fit :
      Subgroup.centralizer (fittingSubgroup (G ⧸ M) : Set (G ⧸ M)) ≤ fittingSubgroup (G ⧸ M) :=
    centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable (G := (G ⧸ M)) hsolvQ
  have hcent_pcore :
      Subgroup.centralizer (pCore p (G ⧸ M) : Set (G ⧸ M)) ≤ pCore p (G ⧸ M) := by
    simpa [hfit_eq] using hcent_fit
  have hcent_tbar : Subgroup.centralizer (Tbar : Set (G ⧸ M)) ≤ pCore p (G ⧸ M) := by
    simpa [hTbar_eq_pcore] using hcent_pcore
  let _ : Fact (IsPGroup p (↥TG)) := ⟨hTG_p⟩
  have hcent_map :
      Subgroup.centralizer ((TG.map q : Subgroup (G ⧸ M)) : Set (G ⧸ M)) =
        (Subgroup.centralizer (TG : Set G)).map q := by
    simpa [q] using
      (centralizer_map_quotient_eq_map_centralizer (G := G) (p := p) (T := TG) (M := M) hMnormal hMcop)
  have hmap_cent_le : (Subgroup.centralizer (TG : Set G)).map q ≤ pCore p (G ⧸ M) := by
    rw [← hcent_map]
    simpa [Tbar] using hcent_tbar
  have hcent_le_comap :
      Subgroup.centralizer (TG : Set G) ≤ Subgroup.comap q (pCore p (G ⧸ M)) :=
    (Subgroup.map_le_iff_le_comap).1 hmap_cent_le
  simpa [TG, Op_p'p, q, M] using hcent_le_comap
