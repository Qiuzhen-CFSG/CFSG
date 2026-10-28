module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Distribution.Geometry
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Distribution.NormalizerGeometry.LocalStructure

/-!
# Subgroup census in Bender's Sylow normalizer

For the actual subgroup `H = N_G(Q)`, Sylow theory and the order-six
centralizer of a three-subgroup give 28 three-subgroups. Taking the relative
centralizer identifies these with the cyclic six-subgroups.

The elementary group `Q` acts freely on the seven-subgroups: an element of
`Q` normalizing such a subgroup must centralize it, whereas an involution
centralizer has order 120. Sylow's congruence then gives eight seven-subgroups,
so every orbit map from `Q` is a bijection. A three-subgroup has a fixed
seven-subgroup by the fixed-point congruence. Using it as the base of this
bijection identifies all its fixed seven-subgroups with its order-two
centralizer in `Q`.

Every subgroup is transported by the literal inclusion into `H` and then
into `G`. No normalizer model or coset-distribution premise is used.

Source: H. Bender, *Finite groups with large subgroups*, Illinois J. Math.
18 (1974), §4, printed pp.226–227, the census following assertion (4.3).
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G]

private noncomputable def censusSylowEquiv (H : Subgroup G) (p : ℕ) [Fact p.Prime]
    (hp : p ^ (Nat.card H).factorization p = p) :
    Sylow p H ≃ BenderSubgroupsOfOrder H p where
  toFun P := ⟨(P : Subgroup H).map H.subtype, map_subtype_le _, by
    rw [card_map_of_injective H.subtype_injective, P.card_eq_multiplicity, hp]⟩
  invFun S := Sylow.ofCard (S.1.subgroupOf H) (by
    rw [Nat.card_congr (subgroupOfEquivOfLe S.2.1).toEquiv, S.2.2, hp])
  left_inv P := Sylow.ext (comap_map_eq_self_of_injective H.subtype_injective _)
  right_inv S := Subtype.ext (map_subgroupOf_eq_of_le S.2.1)

omit [Finite G] in
private theorem census_centralizer_map (H : Subgroup G) (P : Subgroup H) :
    (centralizer ((P : Subgroup H) : Set H)).map H.subtype =
      H ⊓ centralizer (P.map H.subtype : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.property, mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    exact congrArg Subtype.val (mem_centralizer_iff.mp hy a ha)
  · rintro ⟨hxH, hxC⟩
    refine ⟨⟨x, hxH⟩, mem_centralizer_iff.mpr ?_, rfl⟩
    intro a ha
    exact Subtype.ext (mem_centralizer_iff.mp hxC a (mem_map_of_mem H.subtype ha))

private theorem census_three_sylow (h : Janko1CentralizerData G) {d : ℕ}
    (localData : BenderPrimeData G d) (normalizerData : BenderNormalizerData h) :
    Nat.card (Sylow 3 (normalizer (h.sylow : Set G))) = 28 := by
  let H := normalizer (h.sylow : Set G)
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let P : Sylow 3 H := default
  have hP : Nat.card P = 3 := by
    rw [P.card_eq_multiplicity, normalizerData.normalizer_card]
    decide +kernel
  let X := (P : Subgroup H).map H.subtype
  have hX : Nat.card X = 3 := by rw [card_map_of_injective H.subtype_injective]; exact hP
  have hC : Nat.card (centralizer ((P : Subgroup H) : Set H)) = 6 := by
    rw [← card_map_of_injective H.subtype_injective, census_centralizer_map]
    exact h.bender_three_centralizer localData normalizerData X (map_subtype_le _) hX
  let _ : IsCyclic P := isCyclic_of_prime_card hP
  let f := (P : Subgroup H).normalizerMonoidHom
  have hker : Nat.card f.ker = 6 := by
    rw [normalizerMonoidHom_ker,
      Nat.card_congr (subgroupOfEquivOfLe (centralizer_le_normalizer ((P : Subgroup H) : Set H))).toEquiv]
    exact hC
  have ha : Nat.card f.range ∣ 2 := by
    have hd := f.range.card_subgroup_dvd_card
    rwa [IsCyclic.card_mulAut, hP, show Nat.totient 3 = 2 by decide] at hd
  have he := f.ker.card_mul_index
  rw [index_ker, hker] at he
  have hn := (normalizer (P : Set H)).card_mul_index
  simp only [Sylow.coe_coe] at he
  rw [← P.card_eq_index_normalizer, ← he, normalizerData.normalizer_card] at hn
  have hm := card_sylow_modEq_one (p := 3) (G := H)
  change Nat.card (Sylow 3 H) % 3 = 1 % 3 at hm
  change Nat.card (Sylow 3 H) = 28
  rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp ha with ha | ha <;>
    rw [ha] at hn <;> norm_num at hn <;> omega


/-- The actual Sylow normalizer contains 28 subgroups of order three. -/
public theorem bender_three_subgroups (h : Janko1CentralizerData G) {d : ℕ}
    (localData : BenderPrimeData G d) (normalizerData : BenderNormalizerData h) :
    Nat.card (BenderSubgroupsOfOrder (normalizer (h.sylow : Set G)) 3) = 28 := by
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  rw [← Nat.card_congr (censusSylowEquiv _ 3 (by
    rw [normalizerData.normalizer_card]; decide +kernel))]
  exact census_three_sylow h localData normalizerData

omit [Finite G] in
private theorem census_mem_normalizer_map (H : Subgroup G) (P : Subgroup H) (x : H) :
    x ∈ normalizer (P : Set H) ↔ (x : G) ∈ normalizer (P.map H.subtype : Set G) := by
  have he := subgroupOf_normalizer_eq (map_subtype_le P)
  rw [show (P.map H.subtype).subgroupOf H = P from
    comap_map_eq_self_of_injective H.subtype_injective P] at he
  exact Iff.of_eq (congrArg (fun K : Subgroup H => x ∈ K) he.symm)

private theorem census_seven_stabilizer [IsSimpleGroup G] (h : Janko1CentralizerData G)
    (S : Subgroup G) (hSH : S ≤ normalizer (h.sylow : Set G)) (hS : Nat.card S = 7)
    (q : G) (hq : q ∈ (h.sylow : Subgroup G)) (hqn : q ∈ normalizer (S : Set G)) :
    q = 1 := by
  have hd : Disjoint (h.sylow : Subgroup G) S :=
    disjoint_of_coprime_natCard (by rw [h.sylow_card, hS]; decide)
  have hc : q ∈ centralizer (S : Set G) := by
    apply mem_centralizer_iff.mpr
    intro s hs
    have he : s * q * s⁻¹ * q⁻¹ = 1 := by
      apply hd.le_bot
      constructor
      · exact (h.sylow : Subgroup G).mul_mem
          ((mem_normalizer_iff.mp (hSH hs) q).mp hq)
          ((h.sylow : Subgroup G).inv_mem hq)
      · change s * q * s⁻¹ * q⁻¹ ∈ S
        have hmem := S.mul_mem hs
          ((mem_normalizer_iff.mp hqn s⁻¹).mp (S.inv_mem hs))
        simpa only [mul_assoc] using hmem
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp he)
  by_contra hq1
  have hq2 : orderOf q = 2 := orderOf_eq_prime_iff.mpr
    ⟨congrArg Subtype.val (h.sylow_square ⟨q, hq⟩), hq1⟩
  have hle : S ≤ centralizer ({q} : Set G) := by
    intro s hs
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hc s hs)
  have hdiv := card_dvd_of_le hle
  rw [hS, h.involution_centralizer_card q hq2] at hdiv
  norm_num at hdiv

private theorem census_seven_orbit_injective [IsSimpleGroup G] (h : Janko1CentralizerData G)
    (normalizerData : BenderNormalizerData h)
    (P : Sylow 7 (normalizer (h.sylow : Set G))) :
    Function.Injective (fun q : h.sylow =>
      (⟨(q : G), le_normalizer q.property⟩ : normalizer (h.sylow : Set G)) • P) := by
  let H := normalizer (h.sylow : Set G)
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hP : Nat.card P = 7 := by
    rw [P.card_eq_multiplicity, normalizerData.normalizer_card]
    decide +kernel
  intro q r he
  change (⟨q, le_normalizer q.property⟩ : H) • P =
    (⟨r, le_normalizer r.property⟩ : H) • P at he
  have hn : (⟨(r : G)⁻¹ * q, H.mul_mem (H.inv_mem (le_normalizer r.property))
      (le_normalizer q.property)⟩ : H) ∈ normalizer (P : Set H) := by
    apply Sylow.smul_eq_iff_mem_normalizer.mp
    change ((⟨r, le_normalizer r.property⟩ : H)⁻¹ * ⟨q, le_normalizer q.property⟩) • P = P
    rw [mul_smul, he, inv_smul_smul]
  have hnG : (r : G)⁻¹ * q ∈ normalizer ((P : Subgroup H).map H.subtype : Set G) :=
    (census_mem_normalizer_map H (P : Subgroup H) _).mp hn
  have he1 := census_seven_stabilizer h ((P : Subgroup H).map H.subtype)
    (map_subtype_le _) (by rw [card_map_of_injective H.subtype_injective]; exact hP)
    ((r : G)⁻¹ * q) ((h.sylow : Subgroup G).mul_mem
      ((h.sylow : Subgroup G).inv_mem r.property) q.property) hnG
  exact Subtype.ext (inv_mul_eq_one.mp he1).symm

private theorem census_seven_sylow [IsSimpleGroup G] (h : Janko1CentralizerData G)
    (normalizerData : BenderNormalizerData h) :
    Nat.card (Sylow 7 (normalizer (h.sylow : Set G))) = 8 := by
  let H := normalizer (h.sylow : Set G)
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  let P : Sylow 7 H := default
  have hP : Nat.card P = 7 := by
    rw [P.card_eq_multiplicity, normalizerData.normalizer_card]
    decide +kernel
  have hi : (P : Subgroup H).index = 24 := by
    have he := (P : Subgroup H).card_mul_index
    rw [hP, normalizerData.normalizer_card] at he
    omega
  have hd := P.card_dvd_index
  rw [hi] at hd
  have hm := card_sylow_modEq_one (p := 7) (G := H)
  change Nat.card (Sylow 7 H) % 7 = 1 % 7 at hm
  have hlo := Nat.card_le_card_of_injective _ (census_seven_orbit_injective h normalizerData P)
  change Nat.card (h.sylow : Subgroup G) ≤ _ at hlo
  rw [h.sylow_card] at hlo
  have hd' := Nat.mem_divisors.mpr ⟨hd, by decide⟩
  have hd24 : (24 : ℕ).divisors = {1, 2, 3, 4, 6, 8, 12, 24} := by decide
  rw [hd24] at hd'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd'
  change Nat.card (Sylow 7 H) = 8
  change 8 ≤ Nat.card (Sylow 7 H) at hlo
  omega

/-- The eight seven-subgroups form one free orbit under the marked Sylow two-subgroup. -/
public theorem bender_seven_subgroups [IsSimpleGroup G] (h : Janko1CentralizerData G)
    (normalizerData : BenderNormalizerData h) :
    Nat.card (BenderSubgroupsOfOrder (normalizer (h.sylow : Set G)) 7) = 8 := by
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  rw [← Nat.card_congr (censusSylowEquiv _ 7 (by
    rw [normalizerData.normalizer_card]; decide +kernel))]
  exact census_seven_sylow h normalizerData


private theorem census_three_unique_in_six (h : Janko1CentralizerData G)
    (S : Subgroup G) (hSH : S ≤ normalizer (h.sylow : Set G)) (hS : Nat.card S = 6)
    (X Y : Subgroup G) (hXS : X ≤ S) (hYS : Y ≤ S)
    (hX : Nat.card X = 3) (hY : Nat.card Y = 3) : X = Y := by
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let _ : IsCyclic S := h.bender_six_cyclic S hSH hS
  let P : Sylow 3 S := Sylow.ofCard (X.subgroupOf S) (by
    rw [Nat.card_congr (subgroupOfEquivOfLe hXS).toEquiv, hX, hS]; decide +kernel)
  let R : Sylow 3 S := Sylow.ofCard (Y.subgroupOf S) (by
    rw [Nat.card_congr (subgroupOfEquivOfLe hYS).toEquiv, hY, hS]; decide +kernel)
  let _ : Unique (Sylow 3 S) := P.unique_of_normal inferInstance
  have he : X.subgroupOf S = Y.subgroupOf S := congrArg Sylow.toSubgroup (Subsingleton.elim P R)
  have he' := congrArg (fun K : Subgroup S => K.map S.subtype) he
  simpa only [map_subgroupOf_eq_of_le hXS, map_subgroupOf_eq_of_le hYS] using he'

/-- Relative centralization bijects the three-subgroups with the 28 six-subgroups. -/
public theorem bender_six_subgroups (h : Janko1CentralizerData G) {d : ℕ}
    (localData : BenderPrimeData G d) (normalizerData : BenderNormalizerData h) :
    Nat.card (BenderSubgroupsOfOrder (normalizer (h.sylow : Set G)) 6) = 28 := by
  let H := normalizer (h.sylow : Set G)
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let f : BenderSubgroupsOfOrder H 3 → BenderSubgroupsOfOrder H 6 := fun X =>
    ⟨H ⊓ centralizer (X.1 : Set G), inf_le_left,
      h.bender_three_centralizer localData normalizerData X.1 X.2.1 X.2.2⟩
  have hle (X : BenderSubgroupsOfOrder H 3) : X.1 ≤ (f X).1 := by
    let _ : IsCyclic X.1 := isCyclic_of_prime_card X.2.2
    exact le_inf X.2.1 (Subgroup.le_centralizer _)
  have hi : Function.Injective f := by
    intro X Y he
    apply Subtype.ext
    apply census_three_unique_in_six h (f X).1 (f X).2.1 (f X).2.2 X.1 Y.1
      (hle X) (he ▸ hle Y) X.2.2 Y.2.2
  have hs : Function.Surjective f := by
    intro S
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := S.1) 3 (by rw [S.2.2]; decide)
    let X := zpowers (x : G)
    have hX : Nat.card X = 3 := by rw [Nat.card_zpowers, S.1.orderOf_coe, hx]
    have hXS : X ≤ S.1 := zpowers_le.mpr x.property
    let X' : BenderSubgroupsOfOrder H 3 := ⟨X, hXS.trans S.2.1, hX⟩
    refine ⟨X', Subtype.ext ?_⟩
    apply (eq_of_le_of_card_ge (H := S.1) (K := (f X').1) ?_ ?_).symm
    · refine le_inf S.2.1 ?_
      let _ : IsCyclic S.1 := h.bender_six_cyclic S.1 S.2.1 S.2.2
      exact (Subgroup.le_centralizer S.1).trans (centralizer_le hXS)
    · rw [(f X').2.2, S.2.2]
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hi, hs⟩)]
  exact bender_three_subgroups h localData normalizerData


private theorem census_seven_fixed [IsSimpleGroup G] (h : Janko1CentralizerData G) {d : ℕ}
    (localData : BenderPrimeData G d) (normalizerData : BenderNormalizerData h)
    (X : Subgroup G) (hXH : X ≤ normalizer (h.sylow : Set G)) (hX : Nat.card X = 3) :
    Nat.card (MulAction.fixedPoints (X.subgroupOf (normalizer (h.sylow : Set G)))
      (Sylow 7 (normalizer (h.sylow : Set G)))) = 2 := by
  let H := normalizer (h.sylow : Set G)
  let Q := (h.sylow : Subgroup G)
  let A := X.subgroupOf H
  let Ω := Sylow 7 H
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hA : Nat.card A = 3 := (Nat.card_congr (subgroupOfEquivOfLe hXH).toEquiv).trans hX
  have hΩ : Nat.card Ω = 8 := census_seven_sylow h normalizerData
  have hpA : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by simpa using hA)
  obtain ⟨P, hP⟩ := hpA.nonempty_fixed_point_of_prime_not_dvd_card Ω (by rw [hΩ]; decide)
  let i : Q →* H := inclusion (show Q ≤ H from le_normalizer)
  let e : Q ≃ Ω := Equiv.ofBijective (fun q => i q • P)
    ((Nat.bijective_iff_injective_and_card _).mpr
      ⟨census_seven_orbit_injective h normalizerData P, h.sylow_card.trans hΩ.symm⟩)
  have he (q : Q) : e q = i q • P := rfl
  have hfix (q : Q) : e q ∈ MulAction.fixedPoints A Ω ↔ (q : G) ∈ centralizer (X : Set G) := by
    constructor
    · intro hq
      apply mem_centralizer_iff.mpr
      intro x hx
      let xH : H := ⟨x, hXH hx⟩
      let a : A := ⟨xH, hx⟩
      let q' : Q := ⟨x * q * x⁻¹, (mem_normalizer_iff.mp (hXH hx) _).mp q.property⟩
      have haP : xH • P = P := hP a
      have hiP : xH⁻¹ • P = P := inv_smul_eq_iff.mpr haP.symm
      have heq : e q' = e q := by
        rw [he]
        change (xH * i q * xH⁻¹) • P = e q
        rw [mul_smul, mul_smul, hiP, ← he]
        exact hq a
      have hv : x * (q : G) * x⁻¹ = q := congrArg Subtype.val (e.injective heq)
      exact mul_inv_eq_iff_eq_mul.mp hv
    · intro hq a
      have hc : Commute ((a : H) : G) (q : G) := mem_centralizer_iff.mp hq _ a.property
      have hcH : Commute (a : H) (i q) := Subtype.ext hc.eq
      change (a : H) • e q = e q
      rw [he, ← mul_smul, hcH.eq, mul_smul]
      change i q • ((a : H) • P) = i q • P
      rw [show (a : H) • P = P from hP a]
  let eF : {q : Q // (q : G) ∈ centralizer (X : Set G)} ≃ MulAction.fixedPoints A Ω :=
    e.subtypeEquiv (fun q => (hfix q).symm)
  let eD : {q : Q // (q : G) ∈ centralizer (X : Set G)} ≃
      (Q ⊓ centralizer (X : Set G) : Subgroup G) :=
    { toFun := fun q => ⟨q.1.1, q.1.2, q.2⟩
      invFun := fun q => ⟨⟨q.1, q.2.1⟩, q.2.2⟩
      left_inv := by intro q; rfl
      right_inv := by intro q; rfl }
  exact (Nat.card_congr (eF.symm.trans eD)).trans
    (h.bender_sylow_three_centralizer_card localData normalizerData X hXH hX)

/-- Each three-subgroup of the normalizer normalizes exactly two seven-subgroups. -/
public theorem bender_three_normalizes_seven [IsSimpleGroup G] (h : Janko1CentralizerData G) {d : ℕ}
    (localData : BenderPrimeData G d) (normalizerData : BenderNormalizerData h)
    (X : Subgroup G) (hXH : X ≤ normalizer (h.sylow : Set G)) (hX : Nat.card X = 3) :
    Nat.card {S : BenderSubgroupsOfOrder (normalizer (h.sylow : Set G)) 7 //
      X ≤ normalizer (S.1 : Set G)} = 2 := by
  let H := normalizer (h.sylow : Set G)
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  let e := censusSylowEquiv H 7 (by rw [normalizerData.normalizer_card]; decide +kernel)
  have hiff (P : Sylow 7 H) : P ∈ MulAction.fixedPoints (X.subgroupOf H) (Sylow 7 H) ↔
      X ≤ normalizer ((e P).1 : Set G) := by
    rw [Subgroup.sylow_mem_fixedPoints_iff]
    constructor
    · intro hn x hx
      exact (census_mem_normalizer_map H (P : Subgroup H) ⟨x, hXH hx⟩).mp
        (hn (show (⟨x, hXH hx⟩ : H) ∈ X.subgroupOf H from hx))
    · intro hn x hx
      exact (census_mem_normalizer_map H (P : Subgroup H) x).mpr (hn hx)
  exact (Nat.card_congr (e.subtypeEquiv hiff)).symm.trans
    (census_seven_fixed h localData normalizerData X hXH hX)

end CFSG.Quasithin.Janko1CentralizerData
