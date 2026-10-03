module

public import Theory.GroupTheory.PPrimeCoreSurjection

/-!
# Normalizers modulo a normal subgroup of coprime order

The normalizer of a p-subgroup lifts through a normal p′-subgroup. Apply
Frattini's argument inside the normalizer of the product of the two subgroups;
the p-subgroup is a Sylow subgroup of this product. We also record that
quotienting by the p′-core leaves trivial p′-core.

The normalizer proof is promoted from Bender–Glauberman, Lemma 1.14, in
`FeitThompson/BGsection1/CentralizerLemmas.lean`, preserving its public name.
-/

open scoped Pointwise commutatorElement

/-- The quotient by the p′-core has trivial p′-core. -/
public theorem pPrimeCore_quotient_pPrimeCore_eq_bot {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] :
    pPrimeCore p (G ⧸ pPrimeCore p G) = ⊥ := by
  let M := pPrimeCore p G
  let q := QuotientGroup.mk' M
  apply Subgroup.comap_injective (QuotientGroup.mk'_surjective M)
  change (pPrimeCore p (G ⧸ M)).comap q = q.ker
  exact (pPrimeCore_comap_eq_of_surjective_coprime p q
    (QuotientGroup.mk'_surjective M) (by
      simpa [q] using (pPrimeCore_coprime_card (p := p) (G := G)))).trans
    (QuotientGroup.ker_mk' M).symm

-- Lemma 1.14 (normalizer statement)
set_option backward.isDefEq.respectTransparency false in
public theorem normalizer_map_quotient_eq_map_normalizer
    {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (T M : Subgroup G)
    [Fact (IsPGroup p (↥T))] (hM : M.Normal) (hcop : Nat.Coprime p (Nat.card M)) :
    let q : G →* G ⧸ M := QuotientGroup.mk' M
    Subgroup.normalizer (T.map q) = (Subgroup.normalizer T).map q := by
  intro q
  let _ : M.Normal := hM
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective M
  apply (Subgroup.comap_injective hqsurj)
  rw [Subgroup.comap_normalizer_eq_of_surjective (H := T.map q) hqsurj]
  rw [QuotientGroup.comap_map_mk' (N := M) (H := T)]
  rw [QuotientGroup.comap_map_mk' (N := M) (H := Subgroup.normalizer T)]
  set K : Subgroup G := M ⊔ T
  have hM_le : M ≤ Subgroup.normalizer K := by
    exact le_trans (show M ≤ K by exact le_sup_left) Subgroup.le_normalizer
  have hnormT_le : Subgroup.normalizer T ≤ Subgroup.normalizer (K : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff] at hx ⊢
    intro y
    constructor
    · intro hyK
      have hyTK : y ∈ T ⊔ M := by simpa [K, sup_comm] using hyK
      rcases (Subgroup.mem_sup_of_normal_right (s := T) (t := M)).1 hyTK with ⟨t, ht, m, hm, htm⟩
      have ht' : x * t * x⁻¹ ∈ T := (hx t).1 ht
      have hm' : x * m * x⁻¹ ∈ M := hM.conj_mem m hm x
      have hxy : x * y * x⁻¹ = (x * t * x⁻¹) * (x * m * x⁻¹) := by
        calc
          x * y * x⁻¹ = x * (t * m) * x⁻¹ := by simp [htm]
          _ = (x * t * x⁻¹) * (x * m * x⁻¹) := by simp [mul_assoc]
      have hmemTM : x * y * x⁻¹ ∈ T ⊔ M := by
        rw [hxy]
        exact Subgroup.mul_mem_sup ht' hm'
      simpa [K, sup_comm] using hmemTM
    · intro hyK
      have hxinv : x⁻¹ ∈ Subgroup.normalizer T := by
        simpa using (Subgroup.inv_mem_iff (H := Subgroup.normalizer (T : Set G))).2 hx
      have hy' : x⁻¹ * (x * y * x⁻¹) * x ∈ K := by
        have hy'' : x⁻¹ * (x * y * x⁻¹) * x ∈ T ⊔ M := by
          have hyTK : x * y * x⁻¹ ∈ T ⊔ M := by simpa [K, sup_comm] using hyK
          rcases (Subgroup.mem_sup_of_normal_right (s := T) (t := M)).1 hyTK with ⟨t, ht, m, hm, htm⟩
          have ht' : x⁻¹ * t * x ∈ T := by
            simpa using ((Subgroup.mem_normalizer_iff).1 hxinv t).1 ht
          have hm' : x⁻¹ * m * x ∈ M := by
            simpa using hM.conj_mem m hm x⁻¹
          have hxy : x⁻¹ * (x * y * x⁻¹) * x = (x⁻¹ * t * x) * (x⁻¹ * m * x) := by
            calc
              x⁻¹ * (x * y * x⁻¹) * x = x⁻¹ * (t * m) * x := by simp [htm, mul_assoc]
              _ = (x⁻¹ * t * x) * (x⁻¹ * m * x) := by simp [mul_assoc]
          rw [hxy]
          exact Subgroup.mul_mem_sup ht' hm'
        simpa [K, sup_comm] using hy''
      simpa [mul_assoc] using hy'
  have hsup_le : M ⊔ Subgroup.normalizer T ≤ Subgroup.normalizer (K : Set G) := sup_le hM_le hnormT_le
  let T' : Subgroup K := T.subgroupOf K
  have hTp : IsPGroup p T' := by
    simpa [T'] using
      (Fact.out : IsPGroup p (↥T)).of_equiv
        ((Subgroup.subgroupOfEquivOfLe (H := T) (K := K) le_sup_right).symm)
  have hnotdvd : ¬ p ∣ T'.index := by
    let M' : Subgroup K := M.subgroupOf K
    have hM'_normal : M'.Normal := by infer_instance
    have hinf_bot : M ⊓ T = ⊥ := by
      rcases (Fact.out : IsPGroup p (↥T)).exists_card_eq with ⟨n, hn⟩
      have hcopMT : Nat.Coprime (Nat.card M) (Nat.card T) := by
        rw [hn]
        exact hcop.symm.pow_right n
      exact disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcopMT)
    have hdisj' : Disjoint M' T' := by
      rw [Subgroup.disjoint_def]
      intro x hxM hxT
      apply Subtype.ext
      have hxM' : (x : G) ∈ M := hxM
      have hxT' : (x : G) ∈ T := hxT
      have hxbot : (x : G) ∈ (⊥ : Subgroup G) := by
        rw [← hinf_bot]
        exact ⟨hxM', hxT'⟩
      simpa using hxbot
    have hsup' : M' ⊔ T' = ⊤ := by
      simpa [K, M', T'] using
        (Subgroup.subgroupOf_sup (A := M) (A' := T) (B := K) le_sup_left le_sup_right).symm
    have hmul' : ((M' : Set K) * (T' : Set K)) = Set.univ := by
      calc
        ((M' : Set K) * (T' : Set K)) = (↑(M' ⊔ T') : Set K) := by
          simpa using (Subgroup.normal_mul M' T').symm
        _ = Set.univ := by simp [hsup']
    have hcompl : Subgroup.IsComplement' M' T' :=
      Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj' hmul'
    have hindex : T'.index = Nat.card M' := hcompl.index_eq_card
    have hcardM' : Nat.card M' = Nat.card M := by
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := M) (K := K) le_sup_left).toEquiv
    have hcopM' : Nat.Coprime p (Nat.card M') := by
      simpa [hcardM'] using hcop
    rw [hindex]
    exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).1 hcopM'
  let Pk : Sylow p K := IsPGroup.toSylow (p := p) hTp hnotdvd
  have hPk : (Pk : Subgroup K) = T' := by
    simp [Pk]
  let KN : Subgroup (Subgroup.normalizer (K : Set G)) := K.subgroupOf (Subgroup.normalizer (K : Set G))
  have hKN_normal : KN.Normal := by
    simpa [KN] using
      (Subgroup.normal_subgroupOf_iff_le_normalizer (H := K) (K := (Subgroup.normalizer (K : Set G)))
        (h := Subgroup.le_normalizer)).2 (le_rfl : (Subgroup.normalizer (K : Set G)) ≤ (Subgroup.normalizer (K : Set G)))
  let _ : KN.Normal := hKN_normal
  let eKN : K ≃* KN :=
    (Subgroup.subgroupOfEquivOfLe (H := K) (K := (Subgroup.normalizer (K : Set G))) Subgroup.le_normalizer).symm
  let PN : Sylow p KN := (Pk.mapSurjective (f := eKN.toMonoidHom) eKN.surjective)
  have hPmap : PN.map KN.subtype = T.subgroupOf (Subgroup.normalizer (K : Set G)) := by
    ext x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      have hy' : y ∈ (Pk : Subgroup K).map eKN.toMonoidHom := by
        change y ∈ (PN : Subgroup KN) at hy
        simpa [PN] using hy
      rcases Subgroup.mem_map.mp hy' with ⟨z, hz, rfl⟩
      have hzT' : z ∈ T' := by
        simpa [hPk] using hz
      change (z : G) ∈ T
      exact hzT'
    · intro hx
      have hxT : (x : G) ∈ T := hx
      have hxK : x ∈ K.subgroupOf (Subgroup.normalizer (K : Set G)) := by
        show (x : G) ∈ K
        exact Subgroup.mem_sup_right hxT
      let y : KN := ⟨x, hxK⟩
      let z : K := ⟨x.1, by exact Subgroup.mem_sup_right hxT⟩
      have hzT' : z ∈ T' := by
        change (z : G) ∈ T
        exact hxT
      have hzPk : z ∈ (Pk : Subgroup K) := by
        simpa [hPk] using hzT'
      have hyMap : y ∈ (Pk : Subgroup K).map eKN.toMonoidHom := by
        refine ⟨z, hzPk, ?_⟩
        ext
        rfl
      have hyPN : y ∈ PN := by
        change y ∈ (PN : Subgroup KN)
        simpa [PN] using hyMap
      exact ⟨y, hyPN, by ext; rfl⟩
  have hFr : Subgroup.normalizer (PN.map KN.subtype) ⊔ KN = ⊤ := by
    simpa using (Sylow.normalizer_sup_eq_top (p := p) (N := KN) PN)
  have hKN_le : (Subgroup.normalizer (K : Set G)) ≤ M ⊔ Subgroup.normalizer T := by
    intro x hxK
    have hFr' : Subgroup.normalizer (T.subgroupOf (Subgroup.normalizer (K : Set G))) ⊔ KN = ⊤ := by
      simpa [hPmap] using hFr
    have hxTop : (⟨x, hxK⟩ : (Subgroup.normalizer (K : Set G))) ∈ Subgroup.normalizer (T.subgroupOf (Subgroup.normalizer (K : Set G))) ⊔ KN := by
      rw [hFr']
      exact Subgroup.mem_top _
    rcases
      (Subgroup.mem_sup_of_normal_right (s := Subgroup.normalizer (T.subgroupOf (Subgroup.normalizer (K : Set G))))
        (t := KN)).1 (by exact hxTop) with ⟨a, ha, b, hb, hab⟩
    have hnorm_eq :
        Subgroup.normalizer (T.subgroupOf (Subgroup.normalizer (K : Set G))) = (Subgroup.normalizer T).subgroupOf (Subgroup.normalizer (K : Set G)) := by
      exact (Subgroup.subgroupOf_normalizer_eq (H := T) (N := (Subgroup.normalizer (K : Set G)))
        (h := le_trans le_sup_right Subgroup.le_normalizer)).symm
    have haNorm : (a : (Subgroup.normalizer (K : Set G))) ∈ (Subgroup.normalizer T).subgroupOf (Subgroup.normalizer (K : Set G)) := by
      simpa [hnorm_eq] using ha
    have haG : (a : G) ∈ M ⊔ Subgroup.normalizer T := by
      exact Subgroup.mem_sup_right (show (a : G) ∈ Subgroup.normalizer T from haNorm)
    have hT_le_target : T ≤ M ⊔ Subgroup.normalizer T := by
      exact le_trans Subgroup.le_normalizer le_sup_right
    have hK_le_target : K ≤ M ⊔ Subgroup.normalizer T := by
      exact sup_le le_sup_left hT_le_target
    have hbK : (b : G) ∈ K := hb
    have hbG : (b : G) ∈ M ⊔ Subgroup.normalizer T := hK_le_target hbK
    have hxmul : (a : G) * (b : G) = x := by
      simpa using congrArg Subtype.val hab
    rw [← hxmul]
    exact (M ⊔ Subgroup.normalizer T).mul_mem haG hbG
  exact le_antisymm hKN_le hsup_le

