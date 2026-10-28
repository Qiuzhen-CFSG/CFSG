module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion.MaximalNormalizer.Basic
public import Theory.GroupTheory.OddKernelInvolutionFibers

/-!
# Distinguished normalizers and Lemma 7.10

The two invariant Sylow constructions force a p-subgroup larger than `P₁`
to fix a distinguished triple, contradicting the supplied triple bound.
Only the distinguished elements of the normalizer enter the Z-star assumption.
No ambient strong embedding or oddness of the triple stabilizer is used.

Source: GLS, Volume 4, Chapter 2, Lemma 7.10. The elementary Sylow and
factorization arguments are adapted from `BenderSuzuki.SE.Section7Final`.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1
open scoped Pointwise commutatorElement
universe u

private theorem theorem4bIsSylowSubgroupOf_isPGroup_final
    {X : Type u} [Group X] [Finite X] {p : ℕ}
    {P E : Subgroup X}
    (hP : theorem4bIsSylowSubgroupOf p P E) : IsPGroup p P := by
  rcases hP with ⟨PE, rfl⟩
  exact PE.isPGroup'.map E.subtype

private theorem theorem4bIsSylowSubgroupOf_le_final
    {X : Type u} [Group X] {p : ℕ} {P E : Subgroup X}
    (hP : theorem4bIsSylowSubgroupOf p P E) : P ≤ E := by
  rcases hP with ⟨PE, rfl⟩
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
  exact y.property

private theorem theorem4b_mem_normalizer_oddCore_sup_of_factorization
    {G : Type*} [Group G] [Finite G]
    {u : G} (hu : IsInvolution u) (B : Subgroup G)
    (hfactor : pPrimeCore 2 G ⊔
      Subgroup.centralizer ({u} : Set G) = ⊤) :
    u ∈ Subgroup.normalizer
      ((pPrimeCore 2 G ⊔ B : Subgroup G) : Set G) := by
  classical
  let O : Subgroup G := pPrimeCore 2 G
  let H : Subgroup G := O ⊔ B
  have hOnormal : O.Normal := by
    dsimp [O]
    exact pPrimeCore_normal
  let : O.Normal := hOnormal
  have hforward : ∀ x : G, x ∈ H → u * x * u⁻¹ ∈ H := by
    intro x hx
    rcases Subgroup.mem_sup_of_normal_left.mp hx with
      ⟨o, hoO, b, hbB, hob⟩
    have hbFactor : b ∈ O ⊔ Subgroup.centralizer ({u} : Set G) := by
      rw [hfactor]
      trivial
    rcases Subgroup.mem_sup_of_normal_left.mp hbFactor with
      ⟨o', ho'O, c, hcC, hoc⟩
    have hcH : c ∈ H := by
      have hcEq : c = o'⁻¹ * b := by
        calc
          c = o'⁻¹ * (o' * c) := by group
          _ = o'⁻¹ * b := by rw [hoc]
      rw [hcEq]
      exact H.mul_mem
        (H.inv_mem ((le_sup_left : O ≤ O ⊔ B) ho'O))
        ((le_sup_right : B ≤ O ⊔ B) hbB)
    have hconjO : u * o * u⁻¹ ∈ O := hOnormal.conj_mem o hoO u
    have hconjO' : u * o' * u⁻¹ ∈ O := hOnormal.conj_mem o' ho'O u
    have hcu : Commute c u := by
      exact (commute_iff_eq c u).mpr
        (Subgroup.mem_centralizer_singleton_iff.mp hcC)
    have hconjB : u * b * u⁻¹ ∈ H := by
      have hEq : u * b * u⁻¹ = (u * o' * u⁻¹) * c := by
        calc
          u * b * u⁻¹ = u * (o' * c) * u⁻¹ := by rw [hoc]
          _ = u * o' * (c * u⁻¹) := by simp only [mul_assoc]
          _ = u * o' * (u⁻¹ * c) := by rw [hcu.inv_right.eq]
          _ = (u * o' * u⁻¹) * c := by simp only [mul_assoc]
      rw [hEq]
      exact H.mul_mem ((le_sup_left : O ≤ O ⊔ B) hconjO') hcH
    have hEq : u * x * u⁻¹ =
        (u * o * u⁻¹) * (u * b * u⁻¹) := by
      rw [← hob]
      group
    rw [hEq]
    exact H.mul_mem ((le_sup_left : O ≤ O ⊔ B) hconjO) hconjB
  change u ∈ Subgroup.normalizer (H : Set G)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hforward x
  · intro hx
    have htwice := hforward (u * x * u⁻¹) hx
    have huInv : u⁻¹ = u := by
      apply mul_left_cancel (a := u)
      simp [← pow_two, hu.sq_eq_one]
    rw [huInv] at htwice
    have huu : u * u = 1 := by simpa [pow_two] using hu.sq_eq_one
    have hEq : u * (u * x * u) * u = x := by
      calc
        u * (u * x * u) * u = (u * u) * x * (u * u) := by group
        _ = x := by rw [huu]; simp
    rw [hEq] at htwice
    exact htwice

/-- For odd `p`, adjoining a Sylow `p`-subgroup to `O_{2'}(G)` still gives
an odd-order subgroup. -/
private theorem theorem4b_odd_card_oddCore_sup_sylow
    {G : Type*} [Group G] [Finite G]
    {p : ℕ} (hp : Nat.Prime p) (hpOdd : Odd p)
    (B : Sylow p G) :
    Odd (Nat.card (pPrimeCore 2 G ⊔ (B : Subgroup G) : Subgroup G)) := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact p.Prime := ⟨hp⟩
  let O : Subgroup G := pPrimeCore 2 G
  let H : Subgroup G := O ⊔ (B : Subgroup G)
  have hOnormal : O.Normal := by
    dsimp [O]
    exact pPrimeCore_normal
  let : O.Normal := hOnormal
  have hOcop : Nat.Coprime 2 (Nat.card O) := by
    simpa [O] using pPrimeCore_coprime_card (p := 2) (G := G)
  have hBodd : Odd (Nat.card (B : Subgroup G)) := by
    rw [B.card_eq_multiplicity]
    exact hpOdd.pow
  have hBcop : Nat.Coprime 2 (Nat.card (B : Subgroup G)) :=
    hBodd.coprime_two_left
  have hmul : (H : Set G) =
      ((B : Subgroup G) : Set G) * (O : Set G) := by
    simpa [H, sup_comm] using
      (Subgroup.mul_normal (B : Subgroup G) O)
  have hcardH : Nat.card H =
      Nat.card (((B : Subgroup G) : Set G) * (O : Set G) : Set G) := by
    exact Nat.card_congr (Equiv.setCongr hmul)
  have hcardMul :
      Nat.card (((B : Subgroup G) : Set G) * (O : Set G) : Set G) =
        Nat.card O *
          Nat.card (((B : Subgroup G) : Set G).image (↑) : Set (G ⧸ O)) := by
    simpa using
      (Subgroup.card_mul_eq_card_subgroup_mul_card_quotient
        (s := O) (t := ((B : Subgroup G) : Set G)))
  have hsetImage :
      (((B : Subgroup G) : Set G).image (↑) : Set (G ⧸ O)) =
        ((B : Subgroup G).map (QuotientGroup.mk' O) : Set (G ⧸ O)) := by
    simp [Subgroup.coe_map]
  have hcardImageSet :
      Nat.card (((B : Subgroup G) : Set G).image (↑) : Set (G ⧸ O)) =
        Nat.card ((B : Subgroup G).map (QuotientGroup.mk' O) : Set (G ⧸ O)) :=
    Nat.card_congr (Equiv.setCongr hsetImage)
  have hcardImageSubgroup :
      Nat.card (((B : Subgroup G) : Set G).image (↑) : Set (G ⧸ O)) =
        Nat.card ((B : Subgroup G).map (QuotientGroup.mk' O)) := by
    exact hcardImageSet
  have himageDvd :
      Nat.card ((B : Subgroup G).map (QuotientGroup.mk' O)) ∣
        Nat.card (B : Subgroup G) :=
    Subgroup.card_map_dvd (B : Subgroup G) (QuotientGroup.mk' O)
  have himageCop : Nat.Coprime 2
      (Nat.card (((B : Subgroup G) : Set G).image (↑) : Set (G ⧸ O))) := by
    have hcop : Nat.Coprime 2
        (Nat.card ((B : Subgroup G).map (QuotientGroup.mk' O))) :=
      Nat.Coprime.of_dvd_right himageDvd hBcop
    rw [hcardImageSubgroup]
    exact hcop
  apply Nat.coprime_two_left.mp
  rw [hcardH, hcardMul]
  exact Nat.Coprime.mul_right hOcop himageCop

/-- `[II1; 4.1]` in the exact form used by Lemma 7.10.  If the operational
`Z*` factorization holds for an involution `u`, then every `u`-invariant
`p`-subgroup for odd `p` lies in a `u`-invariant Sylow `p`-subgroup. -/
private theorem exists_invariant_sylow_containing_of_pPrimeCore_sup_centralizer_eq_top
    {G : Type*} [Group G] [Finite G]
    {u : G} (hu : IsInvolution u)
    {p : ℕ} (hp : Nat.Prime p) (hpOdd : Odd p)
    {P : Subgroup G} (hPp : IsPGroup p P)
    (huNormP : u ∈ Subgroup.normalizer (P : Set G))
    (hfactor : pPrimeCore 2 G ⊔
      Subgroup.centralizer ({u} : Set G) = ⊤) :
    ∃ S : Sylow p G,
      P ≤ (S : Subgroup G) ∧
        u ∈ Subgroup.normalizer ((S : Subgroup G) : Set G) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨B, hPB⟩ := hPp.exists_le_sylow
  let H : Subgroup G := pPrimeCore 2 G ⊔ (B : Subgroup G)
  have hBH : (B : Subgroup G) ≤ H := le_sup_right
  have hPH : P ≤ H := hPB.trans hBH
  have hHodd : Odd (Nat.card H) := by
    simpa [H] using theorem4b_odd_card_oddCore_sup_sylow hp hpOdd B
  have huNormH : u ∈ Subgroup.normalizer (H : Set G) := by
    simpa [H] using
      theorem4b_mem_normalizer_oddCore_sup_of_factorization
        hu (B : Subgroup G) hfactor
  obtain ⟨Q, hQSylH, hPQ, huNormQ⟩ :=
    theorem4b_exists_invariant_sylow_containing
      hHodd hu huNormH hp hPp hPH huNormP
  rcases hQSylH with ⟨QH, hQeq⟩
  let BH : Sylow p H := B.subtype hBH
  have hQcard : Nat.card Q = Nat.card (B : Subgroup G) := by
    calc
      Nat.card Q = Nat.card (QH : Subgroup H) := by
        rw [hQeq, Subgroup.card_map_of_injective H.subtype_injective]
      _ = p ^ (Nat.card H).factorization p := QH.card_eq_multiplicity
      _ = Nat.card (BH : Subgroup H) := BH.card_eq_multiplicity.symm
      _ = Nat.card (B : Subgroup G) := by
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBH).toEquiv
  have hQcardGlobal : Nat.card Q =
      p ^ (Nat.card G).factorization p := by
    rw [hQcard]
    exact B.card_eq_multiplicity
  let S : Sylow p G := Sylow.ofCard Q hQcardGlobal
  refine ⟨S, ?_, ?_⟩
  · simpa [S] using hPQ
  · simpa [S] using huNormQ

/-- The operational `Z*` factorization inherited by a subgroup containing the
centralizer of the distinguished involution. -/
private theorem theorem4b_lemma710_factorization_subgroup
    {G : Type*} [Group G] [Finite G]
    (M : Subgroup G) {z : G} (hzM : z ∈ M)
    (hcentM : Subgroup.centralizer ({z} : Set G) ≤ M)
    (hfactor : pPrimeCore 2 G ⊔
      Subgroup.centralizer ({z} : Set G) = ⊤) :
    let zM : M := ⟨z, hzM⟩
    pPrimeCore 2 M ⊔ Subgroup.centralizer ({zM} : Set M) = ⊤ := by
  classical
  let zM : M := ⟨z, hzM⟩
  let O : Subgroup G := pPrimeCore 2 G
  let OM : Subgroup M := O.comap M.subtype
  have hOnormal : O.Normal := by
    dsimp [O]
    exact pPrimeCore_normal
  let : O.Normal := hOnormal
  have hOMnormal : OM.Normal := by infer_instance
  let : OM.Normal := hOMnormal
  have hOMmapLe : OM.map M.subtype ≤ O := by
    rw [Subgroup.map_le_iff_le_comap]
  have hOMcard : Nat.card OM ∣ Nat.card O := by
    calc
      Nat.card OM = Nat.card (OM.map M.subtype) := by
        symm
        exact Subgroup.card_map_of_injective M.subtype_injective
      _ ∣ Nat.card O := Subgroup.card_dvd_of_le hOMmapLe
  have hOcop : Nat.Coprime 2 (Nat.card O) := by
    simpa [O] using pPrimeCore_coprime_card (p := 2) (G := G)
  have hOMcop : Nat.Coprime 2 (Nat.card OM) :=
    Nat.Coprime.of_dvd_right hOMcard hOcop
  have hOMle : OM ≤ pPrimeCore 2 M := le_sSup ⟨hOMnormal, hOMcop⟩
  apply top_unique
  intro m _hm
  have hmSup : (m : G) ∈ O ⊔ Subgroup.centralizer ({z} : Set G) := by
    rw [hfactor]
    trivial
  rcases Subgroup.mem_sup_of_normal_left.mp hmSup with
    ⟨o, hoO, c, hcC, hoc⟩
  have hcM : c ∈ M := hcentM hcC
  have hoM : o ∈ M := by
    have : (m : G) * c⁻¹ ∈ M := M.mul_mem m.property (M.inv_mem hcM)
    rwa [← hoc, mul_inv_cancel_right] at this
  let oM : M := ⟨o, hoM⟩
  let cM : M := ⟨c, hcM⟩
  have hoOM : oM ∈ OM := hoO
  have hoCore : oM ∈ pPrimeCore 2 M := hOMle hoOM
  have hcCM : cM ∈ Subgroup.centralizer ({zM} : Set M) := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp hcC
  have hprod := Subgroup.mul_mem_sup hoCore hcCM
  have hprodEq : oM * cM = m := by
    apply Subtype.ext
    exact hoc
  rwa [hprodEq] at hprod

/-- Cardinality comparison with a Sylow subgroup represented in an ambient
group by `theorem4bIsSylowSubgroupOf`. -/
private theorem theorem4b_lemma710_card_le_sylow_of_isPGroup
    {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : Nat.Prime p) {P Q E : Subgroup X}
    (hPp : IsPGroup p P) (hPE : P ≤ E)
    (hQsyl : theorem4bIsSylowSubgroupOf p Q E) :
    Nat.card P ≤ Nat.card Q := by
  let : Fact p.Prime := ⟨hp⟩
  let PE : Subgroup E := P.subgroupOf E
  have hPEp : IsPGroup p PE :=
    hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPE).symm
  obtain ⟨S, hPES⟩ := hPEp.exists_le_sylow
  rcases hQsyl with ⟨QE, hQeq⟩
  calc
    Nat.card P = Nat.card PE := (natCard_subgroupOf_eq P E hPE).symm
    _ ≤ Nat.card (S : Subgroup E) := Subgroup.card_le_of_le hPES
    _ = Nat.card (QE : Subgroup E) := by
      rw [S.card_eq_multiplicity, QE.card_eq_multiplicity]
    _ = Nat.card Q := by
      rw [hQeq, Subgroup.card_map_of_injective E.subtype_injective]

private theorem theorem4b_lemma710_conjBy_fixed_unique
    {G Omega : Type*} [Group G] [MulAction G Omega]
    (P : Subgroup G) (g : G) (alpha : Omega)
    (hfix : P ≤ MulAction.stabilizer G alpha)
    (hunique : ∀ omega : Omega,
      P ≤ MulAction.stabilizer G omega → omega = alpha) :
    P.conjBy g ≤ MulAction.stabilizer G (g • alpha) ∧
      ∀ omega : Omega,
        P.conjBy g ≤ MulAction.stabilizer G omega → omega = g • alpha := by
  constructor
  · intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨p, hp, rfl⟩
    apply MulAction.mem_stabilizer_iff.mpr
    have hpfix := MulAction.mem_stabilizer_iff.mp (hfix hp)
    simp [MulAut.conj_apply, mul_smul, hpfix]
  · intro omega homega
    have hpre : P ≤ MulAction.stabilizer G (g⁻¹ • omega) := by
      intro p hp
      have hconj : g * p * g⁻¹ ∈ P.conjBy g := by
        exact Subgroup.mem_map.mpr ⟨p, hp, rfl⟩
      have hfixConj := MulAction.mem_stabilizer_iff.mp (homega hconj)
      apply MulAction.mem_stabilizer_iff.mpr
      calc
        p • (g⁻¹ • omega) = g⁻¹ • ((g * p * g⁻¹) • omega) := by
          simp [mul_smul]
        _ = g⁻¹ • omega := by rw [hfixConj]
    have hpreEq := hunique (g⁻¹ • omega) hpre
    calc
      omega = g • (g⁻¹ • omega) := (smul_inv_smul g omega).symm
      _ = g • alpha := by rw [hpreEq]

/-- Source Lemma 7.10 in its operational Z-star form: the distinguished
involutions in `N_G(Q)` cannot all factor that normalizer as
`O₂'(N) C_N(u)`. -/
public theorem action_lemma710
    {X : Type u} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}
    (h : IsProductDisconnected Z M)
    (d : ActionCounterexample Z M) {beta : X ⧸ M}
    (hne : beta ≠ QuotientGroup.mk 1)
    (q : ActionMaximalNormalizerData d beta) :
    let N : Subgroup X := Subgroup.normalizer (q.chosen.Q : Set X)
    ¬ ∀ u : N, (u : X) ∈ Z →
      pPrimeCore 2 N ⊔ Subgroup.centralizer ({u} : Set N) = ⊤ := by
  classical
  let : Fact d.p.Prime := ⟨d.hp⟩
  let a := q.chosen
  let N : Subgroup X := Subgroup.normalizer (a.Q : Set X)
  let NA : Subgroup N := M.comap N.subtype
  let alpha : conjugateCosetSpace M := QuotientGroup.mk 1
  dsimp only
  intro hfactorAll
  have hzNmem : d.z ∈ N := a.hzNormQ
  let zN : N := ⟨d.z, hzNmem⟩
  have hzNI : IsInvolution zN := IsInvolution.subtype d.hz hzNmem
  have hzFactor : pPrimeCore 2 N ⊔
      Subgroup.centralizer ({zN} : Set N) = ⊤ := hfactorAll zN d.hzZ
  have hzNA : zN ∈ NA := by
    exact d.hzM
  have hcentNA : Subgroup.centralizer ({zN} : Set N) ≤ NA := by
    intro x hx
    change ((x : N) : X) ∈ M
    apply h.centralizer_le d.hzZ d.hzM
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val
      (Subgroup.mem_centralizer_singleton_iff.mp hx)
  let zA : NA := ⟨zN, hzNA⟩
  have hzAI : IsInvolution zA := IsInvolution.subtype hzNI hzNA
  have hzAFactor : pPrimeCore 2 NA ⊔
      Subgroup.centralizer ({zA} : Set NA) = ⊤ := by
    simpa [zA] using theorem4b_lemma710_factorization_subgroup
      NA hzNA hcentNA hzFactor
  obtain ⟨Pstar, _hbot, hzANormPstar⟩ :=
    exists_invariant_sylow_containing_of_pPrimeCore_sup_centralizer_eq_top
      hzAI d.hp d.hpOdd (P := (⊥ : Subgroup NA))
      (IsPGroup.of_bot (p := d.p) (G := NA)) (by
        rw [Subgroup.normalizer_eq_top_iff.mpr
          (inferInstance : (⊥ : Subgroup NA).Normal)]
        trivial) hzAFactor
  let PstarN : Subgroup N := (Pstar : Subgroup NA).map NA.subtype
  let PstarX : Subgroup X := PstarN.map N.subtype
  have hPstarNp : IsPGroup d.p PstarN :=
    Pstar.isPGroup'.map NA.subtype
  have hPstarXp : IsPGroup d.p PstarX :=
    hPstarNp.map N.subtype
  have hPstarNNA : PstarN ≤ NA := by
    exact Subgroup.map_subtype_le (Pstar : Subgroup NA)
  have hPstarXAlpha : PstarX ≤ MulAction.stabilizer X alpha := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨xN, hxN, rfl⟩
    have hxNA : xN ∈ NA := hPstarNNA hxN
    apply MulAction.mem_stabilizer_iff.mpr
    change ((xN : N) : X) • alpha = alpha
    apply MulAction.mem_stabilizer_iff.mp
    rw [show MulAction.stabilizer X alpha = M by
      simp [alpha]]
    exact hxNA
  have hzNNormPstarN : zN ∈
      Subgroup.normalizer (PstarN : Set N) := by
    have hzMap : zN ∈
        (Subgroup.normalizer ((Pstar : Subgroup NA) : Set NA)).map
          NA.subtype :=
      Subgroup.mem_map.mpr ⟨zA, hzANormPstar, rfl⟩
    exact (Subgroup.le_normalizer_map
      (H := (Pstar : Subgroup NA)) NA.subtype) hzMap
  have hzXNormPstarX : d.z ∈
      Subgroup.normalizer (PstarX : Set X) := by
    have hzMap : d.z ∈
        (Subgroup.normalizer (PstarN : Set N)).map N.subtype :=
      Subgroup.mem_map.mpr ⟨zN, hzNNormPstarN, rfl⟩
    exact (Subgroup.le_normalizer_map (H := PstarN) N.subtype) hzMap
  have hRleNDQ : q.R ≤ actionNormalizerInD M beta a.Q :=
    theorem4bIsSylowSubgroupOf_le_final q.hRsylow
  have hRN : q.R ≤ N := by
    exact hRleNDQ.trans inf_le_right
  let RN : Subgroup N := q.R.subgroupOf N
  have hRNA : RN ≤ NA := by
    intro r hr
    change ((r : N) : X) ∈ M
    have hrR : ((r : N) : X) ∈ q.R := hr
    exact (hRleNDQ hrR).1.1
  have hRNp : IsPGroup d.p RN := by
    have hRp : IsPGroup d.p q.R :=
      theorem4bIsSylowSubgroupOf_isPGroup_final q.hRsylow
    exact hRp.of_equiv (Subgroup.subgroupOfEquivOfLe hRN).symm
  have hRcard_le_PstarN : Nat.card q.R ≤ Nat.card PstarN := by
    have hcardRN : Nat.card RN = Nat.card q.R :=
      natCard_subgroupOf_eq q.R N hRN
    rw [← hcardRN]
    exact theorem4b_lemma710_card_le_sylow_of_isPGroup d.hp
      hRNp hRNA ⟨Pstar, rfl⟩
  have hPstarNcardX : Nat.card PstarX = Nat.card PstarN :=
    Subgroup.card_map_of_injective N.subtype_injective
  have hPstarUniqueX : ∀ delta : conjugateCosetSpace M,
      PstarX ≤ MulAction.stabilizer X delta → delta = alpha := by
    intro delta hPdelta
    by_contra hdelta
    have hPzdelta : PstarX ≤ MulAction.stabilizer X (d.z • delta) :=
      theorem4b_le_stabilizer_smul_of_le_stabilizer_of_mem_normalizer
        hzXNormPstarX hPdelta
    have hPtriple : PstarX ≤
        (MulAction.stabilizer X alpha ⊓ MulAction.stabilizer X delta) ⊓
          MulAction.stabilizer X (d.z • delta) :=
      le_inf (le_inf hPstarXAlpha hPdelta) hPzdelta
    have hzAlpha : d.z • alpha = alpha := by
      apply MulAction.mem_stabilizer_iff.mp
      rw [show MulAction.stabilizer X alpha = M by
        simp [alpha]]
      exact d.hzM
    have hcardLe := q.triple_bound d.z d.hzZ alpha delta hzAlpha (Ne.symm hdelta)
      PstarX hPstarXp hPtriple
    have hPstarNcard_le_P₁ : Nat.card PstarN ≤ Nat.card a.P₁ := by
      simpa [hPstarNcardX] using hcardLe
    have hRcard_le_P₁ : Nat.card q.R ≤ Nat.card a.P₁ :=
      hRcard_le_PstarN.trans hPstarNcard_le_P₁
    exact (not_lt_of_ge hRcard_le_P₁) (by
      simpa [a] using q.hP₁card_lt_R)
  have hnormalizerPstar_le_NA :
      Subgroup.normalizer (PstarN : Set N) ≤ NA := by
    intro n hn
    have hfixConj : PstarX ≤
        MulAction.stabilizer X ((n : X) • alpha) := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨p, hpPstar, rfl⟩
      have hconjP : n⁻¹ * p * n ∈ PstarN :=
        (Subgroup.mem_normalizer_iff''.mp hn p).mp hpPstar
      have hconjFix : ((n⁻¹ * p * n : N) : X) • alpha = alpha := by
        apply MulAction.mem_stabilizer_iff.mp
        rw [show MulAction.stabilizer X alpha = M by
          simp [alpha]]
        exact hPstarNNA hconjP
      apply MulAction.mem_stabilizer_iff.mpr
      calc
        ((p : N) : X) • (((n : N) : X) • alpha) =
            ((n : N) : X) • (((n⁻¹ * p * n : N) : X) • alpha) := by
          simp [mul_smul]
        _ = ((n : N) : X) • alpha := by rw [hconjFix]
    have hnFix : ((n : N) : X) • alpha = alpha :=
      hPstarUniqueX _ hfixConj
    change ((n : N) : X) ∈ M
    rw [← baseCoset_stabilizer M]
    exact MulAction.mem_stabilizer_iff.mpr (by
      simpa [alpha, baseCoset_stabilizer] using hnFix)
  have hPstarSylowTop : theorem4bIsSylowSubgroupOf d.p PstarN
      (⊤ : Subgroup N) := by
    by_contra hnotSylow
    have hgrowth :=
      action_factorization_lt_normalizer_of_not_sylow
        d.hp hPstarNp (show PstarN ≤ (⊤ : Subgroup N) from le_top)
        hnotSylow
    have hnormLe :
        (⊤ : Subgroup N) ⊓ Subgroup.normalizer (PstarN : Set N) ≤ NA := by
      simpa using hnormalizerPstar_le_NA
    have hfacLe :
        Nat.factorization
            (Nat.card (((⊤ : Subgroup N) ⊓
              Subgroup.normalizer (PstarN : Set N)) : Subgroup N)) d.p ≤
          Nat.factorization (Nat.card NA) d.p :=
      Nat.factorization_le_factorization_of_dvd_right
        (Subgroup.card_dvd_of_le hnormLe) Nat.card_pos.ne' Nat.card_pos.ne'
    have hPstarCard : Nat.card PstarN =
        d.p ^ (Nat.card NA).factorization d.p := by
      dsimp [PstarN]
      rw [Subgroup.card_map_of_injective NA.subtype_injective]
      exact Pstar.card_eq_multiplicity
    have hfacEq : (Nat.card PstarN).factorization d.p =
        (Nat.card NA).factorization d.p := by
      rw [hPstarCard, Nat.factorization_pow_self d.hp]
    rw [hfacEq] at hgrowth
    exact (not_lt_of_ge hfacLe) hgrowth
  rcases hPstarSylowTop with ⟨Ptop, hPtop⟩
  have hPstarCardN : Nat.card PstarN =
      d.p ^ (Nat.card N).factorization d.p := by
    calc
      Nat.card PstarN = Nat.card (Ptop : Subgroup (⊤ : Subgroup N)) := by
        rw [hPtop, Subgroup.card_map_of_injective
          (⊤ : Subgroup N).subtype_injective]
      _ = d.p ^ (Nat.card (⊤ : Subgroup N)).factorization d.p :=
        Ptop.card_eq_multiplicity
      _ = d.p ^ (Nat.card N).factorization d.p := by simp
  let P0 : Sylow d.p N := Sylow.ofCard PstarN hPstarCardN
  have hP0coe : (P0 : Subgroup N) = PstarN := by rfl
  have htNmem : a.t ∈ N := a.htNormQ
  let tN : N := ⟨a.t, htNmem⟩
  have htNI : IsInvolution tN := IsInvolution.subtype (h.involutions a.t a.htZ) htNmem
  have htFactor : pPrimeCore 2 N ⊔
      Subgroup.centralizer ({tN} : Set N) = ⊤ := hfactorAll tN a.htZ
  have htNormRN : tN ∈ Subgroup.normalizer (RN : Set N) := by
    rw [Subgroup.mem_normalizer_iff]
    intro r
    change ((r : N) : X) ∈ q.R ↔
      a.t * ((r : N) : X) * a.t⁻¹ ∈ q.R
    exact (Subgroup.mem_normalizer_iff.mp q.htNormR ((r : N) : X))
  obtain ⟨Rstar, hRNRstar, htNormRstar⟩ :=
    exists_invariant_sylow_containing_of_pPrimeCore_sup_centralizer_eq_top
      htNI d.hp d.hpOdd hRNp htNormRN htFactor
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq N P0 Rstar
  have hRstarEq : (Rstar : Subgroup N) = PstarN.conjBy n := by
    have hcoe := congrArg
      (fun S : Sylow d.p N => (S : Subgroup N)) hn
    have hconjHom :
        (MulDistribMulAction.toMonoidEnd (MulAut N) N) (MulAut.conj n) =
          (MulAut.conj n).toMonoidHom := by
      ext x
      rfl
    simp only [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def,
      hP0coe] at hcoe
    rw [hconjHom] at hcoe
    symm
    simpa only [Subgroup.conjBy] using hcoe
  have hPstarFixAlphaN : PstarN ≤ MulAction.stabilizer N alpha := by
    intro p hp
    apply MulAction.mem_stabilizer_iff.mpr
    change ((p : N) : X) • alpha = alpha
    apply MulAction.mem_stabilizer_iff.mp
    exact hPstarXAlpha (Subgroup.mem_map.mpr ⟨p, hp, rfl⟩)
  have hPstarUniqueN : ∀ omega : conjugateCosetSpace M,
      PstarN ≤ MulAction.stabilizer N omega → omega = alpha := by
    intro omega homega
    apply hPstarUniqueX omega
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨p, hp, rfl⟩
    exact homega hp
  have hconjFix := theorem4b_lemma710_conjBy_fixed_unique
    PstarN n alpha hPstarFixAlphaN hPstarUniqueN
  have hRstarFix : (Rstar : Subgroup N) ≤
      MulAction.stabilizer N (n • alpha) := by
    rw [hRstarEq]
    exact hconjFix.1
  have hRstarUnique : ∀ omega : conjugateCosetSpace M,
      (Rstar : Subgroup N) ≤ MulAction.stabilizer N omega →
        omega = n • alpha := by
    intro omega homega
    rw [hRstarEq] at homega
    exact hconjFix.2 omega homega
  have htRstarPoint : tN • (n • alpha) = n • alpha := by
    apply hRstarUnique
    exact theorem4b_le_stabilizer_smul_of_le_stabilizer_of_mem_normalizer
      htNormRstar hRstarFix
  let gamma : X ⧸ M := n • alpha
  have htGamma : a.t • gamma = gamma := htRstarPoint
  have hpointEq : n • alpha = gamma := rfl
  have hRgamma : q.R ≤ MulAction.stabilizer X gamma := by
    intro r hr
    let rN : N := ⟨r, hRN hr⟩
    have hrRN : rN ∈ RN := hr
    have hrRstar : rN ∈ (Rstar : Subgroup N) := hRNRstar hrRN
    have hrFix := MulAction.mem_stabilizer_iff.mp (hRstarFix hrRstar)
    apply MulAction.mem_stabilizer_iff.mpr
    change rN • gamma = gamma
    simpa [hpointEq] using hrFix
  have hRalpha : q.R ≤ MulAction.stabilizer X alpha := by
    intro r hr
    have hrM : r ∈ M := (hRleNDQ hr).1.1
    apply MulAction.mem_stabilizer_iff.mp
    rw [show MulAction.stabilizer X alpha = M by
      simp [alpha]]
    exact hrM
  have hRtalpha : q.R ≤ MulAction.stabilizer X (a.t • alpha) :=
    theorem4b_le_stabilizer_smul_of_le_stabilizer_of_mem_normalizer
      q.htNormR hRalpha
  have hgammaAlpha : gamma ≠ alpha := by
    intro heq
    have htAlpha : a.t • alpha = alpha := by simpa [heq] using htGamma
    exact hne (a.htBase.symm.trans htAlpha)
  have hRtriple : q.R ≤
      (MulAction.stabilizer X gamma ⊓ MulAction.stabilizer X alpha) ⊓
        MulAction.stabilizer X (a.t • alpha) :=
    le_inf (le_inf hRgamma hRalpha) hRtalpha
  have hRcardLe := q.triple_bound a.t a.htZ gamma alpha htGamma hgammaAlpha
      q.R (theorem4bIsSylowSubgroupOf_isPGroup_final q.hRsylow) hRtriple
  exact (not_lt_of_ge hRcardLe) (by
    simpa [a] using q.hP₁card_lt_R)


/-- Centrality of an involution modulo the odd core gives the operational
factorization, by conjugacy within each odd-kernel involution fiber. -/
private theorem oddCore_sup_centralizer_of_quotient_center
    {G : Type*} [Group G] [Finite G] {z : G} (hz : IsInvolution z)
    (hc : QuotientGroup.mk' (pPrimeCore 2 G) z ∈
      Subgroup.center (G ⧸ pPrimeCore 2 G)) :
    pPrimeCore 2 G ⊔ Subgroup.centralizer ({z} : Set G) = ⊤ := by
  let f := QuotientGroup.mk' (pPrimeCore 2 G)
  have hker : Nat.Coprime 2 (Nat.card f.ker) := by
    simpa only [f, QuotientGroup.ker_mk'] using
      (pPrimeCore_coprime_card (p := 2) (G := G))
  have hzorder : orderOf z = 2 := orderOf_eq_prime hz.sq_eq_one hz.ne_one
  apply top_unique
  intro g _
  have hgz : IsInvolution ((MulAut.conj g) z) :=
    IsInvolution.map_of_injective hz (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective
  have hgzorder : orderOf ((MulAut.conj g) z) = 2 :=
    orderOf_eq_prime hgz.sq_eq_one hgz.ne_one
  have hf : f z = f ((MulAut.conj g) z) := by
    have hcomm := Subgroup.mem_center_iff.mp hc (f g)
    change f z = f (g * z * g⁻¹)
    rw [map_mul, map_mul, map_inv, hcomm, mul_inv_cancel_right]
  obtain ⟨k, hk⟩ := Subgroup.involutions_same_image_conj_ker f hker
    hzorder hgzorder hf
  have hkO : (k : G) ∈ pPrimeCore 2 G := by
    simpa only [f, QuotientGroup.ker_mk'] using k.property
  have hcentral : (k : G)⁻¹ * g ∈ Subgroup.centralizer ({z} : Set G) := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have hh := congrArg (fun a : G => (k : G)⁻¹ * a * g) hk
    simpa only [MulAut.conj_apply, mul_assoc, inv_mul_cancel_left,
      inv_mul_cancel, mul_one] using hh.symm
  have hprod := Subgroup.mul_mem_sup hkO hcentral
  simpa only [mul_inv_cancel_left] using hprod

/-- Lemma 7.10 with the literal Z-star convention: some distinguished
involution of `N_G(Q)` is not central modulo `O₂'(N_G(Q))`. -/
public theorem action_lemma710_quotient_center
    {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : IsProductDisconnected Z M)
    (d : ActionCounterexample Z M) {beta : G ⧸ M}
    (hne : beta ≠ QuotientGroup.mk 1)
    (q : ActionMaximalNormalizerData d beta) :
    let N := Subgroup.normalizer (q.chosen.Q : Set G)
    ¬ ∀ u : N, (u : G) ∈ Z →
      QuotientGroup.mk' (pPrimeCore 2 N) u ∈ Subgroup.center (N ⧸ pPrimeCore 2 N) := by
  dsimp only
  intro hall
  apply action_lemma710 h d hne q
  intro u hu
  exact oddCore_sup_centralizer_of_quotient_center
    (IsInvolution.subtype (h.involutions u hu) u.property) (hall u hu)

end BenderSuzuki.ZD
