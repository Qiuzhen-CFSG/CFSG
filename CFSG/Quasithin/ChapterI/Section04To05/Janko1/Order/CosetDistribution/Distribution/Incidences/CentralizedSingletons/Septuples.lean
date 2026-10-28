module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Distribution.Incidences.CentralizedSingletons.Centralizers
/-!
# Commuting involutions in Bender's septuple fibers

The literal inverters of a seven-subgroup S form a set of cardinality 7e.
A three-subgroup normalizing S acts on this set by conjugation. If e = 1,
its seven points force a fixed point. Two fixed inverters have product in
C_G(S) = S and in C_H(X), whose order is six; thus they coincide.

The exact inverted-subgroup description identifies these fixed points with
septuple involutions commuting with X. The two seven-subgroups normalized by
X therefore contribute exactly 2e such involutions.

Source: H. Bender, *Finite groups with large subgroups*, Illinois J. Math.
18 (1974), §4, printed p.227, the commuting-three-subgroup paragraph.
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G]

/-- The involutions inverting every element of the literal subgroup. -/
@[expose] public def BenderSubgroupInverters (S : Subgroup G) :=
  {u : G // orderOf u = 2 ∧ ∀ a ∈ S, u * a * u⁻¹ = a⁻¹}

public theorem bender_seven_generator (S : Subgroup G) (hS : Nat.card S = 7) :
    ∃ y : G, orderOf y = 7 ∧ S = zpowers y := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := S) 7 (by rw [hS])
  have hyG : orderOf (y : G) = 7 := (orderOf_coe y).trans hy
  exact ⟨y, hyG, (eq_of_le_of_card_ge (zpowers_le.mpr y.2)
    (by rw [Nat.card_zpowers, hyG, hS])).symm⟩

public theorem bender_subgroup_inverters_card
    (h : Janko1CentralizerData G) (e : ℕ)
    (hseven : ∀ x : normalizer (h.sylow : Set G), orderOf (x : G) = 7 →
      Nat.card {t : G // orderOf t = 2 ∧ t * (x : G) * t⁻¹ = (x : G)⁻¹} = 7 * e)
    (S : BenderSubgroupsOfOrder (normalizer (h.sylow : Set G)) 7) :
    Nat.card (BenderSubgroupInverters S.1) = 7 * e := by
  obtain ⟨y, hy, hS⟩ := bender_seven_generator S.1 S.2.2
  have hyS : y ∈ S.1 := hS ▸ mem_zpowers y
  let ec : BenderSubgroupInverters S.1 ≃
      {t : G // orderOf t = 2 ∧ t * y * t⁻¹ = y⁻¹} :=
    Equiv.subtypeEquivRight (fun t => and_congr_right (fun _ => by
      constructor
      · intro ht; exact ht y hyS
      · intro ht a ha
        rw [hS] at ha
        obtain ⟨n, rfl⟩ := ha
        rw [← conj_zpow, ht, inv_zpow]))
  exact (Nat.card_congr ec).trans (hseven ⟨y, S.2.1 hyS⟩ hy)

public theorem bender_subgroup_inverter_normalizes (S : Subgroup G)
    (u : BenderSubgroupInverters S) : u.1 ∈ normalizer (S : Set G) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · rintro _ ⟨a, ha, rfl⟩
    change u.1 * a * u.1⁻¹ ∈ S
    rw [u.2.2 a ha]
    exact S.inv_mem ha
  · rw [card_map_of_injective (MulAut.conj u.1).injective]

public theorem bender_seven_inverter_outside
    (h : Janko1CentralizerData G)
    (S : BenderSubgroupsOfOrder (normalizer (h.sylow : Set G)) 7)
    (u : BenderSubgroupInverters S.1) : u.1 ∉ normalizer (h.sylow : Set G) := by
  obtain ⟨y, hy, hS⟩ := bender_seven_generator S.1 S.2.2
  have hyS : y ∈ S.1 := hS ▸ mem_zpowers y
  exact h.bender_inverter_not_mem_normalizer y u.1 (S.2.1 hyS) u.2.1
    (u.2.2 y hyS) (by rw [hy]; decide)

/-- An inverter of an actual seven-subgroup inverts precisely that subgroup inside H. -/
public theorem bender_seven_inverted_exact
    (h : Janko1CentralizerData G) (geometry : BenderNormalizerGeometry h)
    (S : BenderSubgroupsOfOrder (normalizer (h.sylow : Set G)) 7)
    (u : BenderSubgroupInverters S.1) :
    ∀ a : G, a ∈ S.1 ↔ a ∈ normalizer (h.sylow : Set G) ∧ u.1 * a * u.1⁻¹ = a⁻¹ := by
  obtain ⟨K, hK, hc⟩ := geometry.inverted_subgroup u.1 u.2.1
    (bender_seven_inverter_outside h S u)
  have hSK : S.1 ≤ K := fun a ha => (hK a).mpr ⟨S.2.1 ha, u.2.2 a ha⟩
  have hd := card_dvd_of_le hSK
  rw [S.2.2] at hd
  have hc7 : Nat.card K = 7 := by
    rcases hc with hc | hc | hc | hc | hc <;> simp_all
  have he : S.1 = K := eq_of_le_of_card_ge hSK (by rw [S.2.2, hc7])
  exact he ▸ hK

omit [Finite G] in
private theorem inverters_product_centralizes (S : Subgroup G)
    (u v : BenderSubgroupInverters S) : u.1 * v.1 ∈ centralizer (S : Set G) := by
  apply mem_centralizer_iff.mpr
  intro a ha
  have he : (u.1 * v.1) * a * (u.1 * v.1)⁻¹ = a := by
    calc
      _ = u.1 * (v.1 * a * v.1⁻¹) * u.1⁻¹ := by group
      _ = u.1 * a⁻¹ * u.1⁻¹ := by rw [v.2.2 a ha]
      _ = a := by rw [u.2.2 a⁻¹ (S.inv_mem ha), inv_inv]
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- Among the inverters of S, at most one commutes with a three-subgroup normalizing S. -/
public theorem bender_seven_commuting_inverter_unique
    (h : Janko1CentralizerData G) (normalizerData : BenderNormalizerData h)
    (geometry : BenderNormalizerGeometry h)
    (X : BenderSubgroupsOfOrder (normalizer (h.sylow : Set G)) 3)
    (S : BenderSubgroupsOfOrder (normalizer (h.sylow : Set G)) 7)
    (u v : BenderSubgroupInverters S.1)
    (huX : X.1 ≤ centralizer ({u.1} : Set G))
    (hvX : X.1 ≤ centralizer ({v.1} : Set G)) : u = v := by
  have huN := bender_subgroup_inverter_normalizes S.1 u
  have h2 : 2 ∣ Nat.card (normalizer (S.1 : Set G)) := by
    have hd := orderOf_dvd_natCard (⟨u.1, huN⟩ : normalizer (S.1 : Set G))
    rwa [← orderOf_coe, u.2.1] at hd
  have hCS := normalizerData.seven_centralizer S.1 S.2.1 S.2.2 (even_iff_two_dvd.mpr h2)
  have huvS : u.1 * v.1 ∈ S.1 := hCS.le (inverters_product_centralizes S.1 u v)
  have huvC : u.1 * v.1 ∈ centralizer (X.1 : Set G) := by
    apply mem_centralizer_iff.mpr
    intro a ha
    exact (show Commute a u.1 from mem_centralizer_singleton_iff.mp (huX ha)).mul_right
      (show Commute a v.1 from mem_centralizer_singleton_iff.mp (hvX ha))
  have hd7 : orderOf (u.1 * v.1) ∣ 7 := by
    have hd := orderOf_dvd_natCard (⟨u.1 * v.1, huvS⟩ : S.1)
    simpa only [← orderOf_coe, S.2.2] using hd
  have hd6 : orderOf (u.1 * v.1) ∣ 6 := by
    have hd := orderOf_dvd_natCard
      (⟨u.1 * v.1, S.2.1 huvS, huvC⟩ :
        (normalizer (h.sylow : Set G) ⊓ centralizer (X.1 : Set G) : Subgroup G))
    simpa only [← orderOf_coe, geometry.three_centralizer X.1 X.2.1 X.2.2] using hd
  have he : u.1 * v.1 = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp (Nat.dvd_gcd hd7 hd6))
  apply Subtype.ext
  have hvi : v.1⁻¹ = v.1 := inv_eq_of_mul_eq_one_right
    (by simpa only [pow_two] using (orderOf_eq_prime_iff.mp v.2.1).1)
  exact (eq_inv_of_mul_eq_one_left he).trans hvi

omit [Finite G] in
private theorem inverter_conj (S X : Subgroup G)
    (hXN : X ≤ normalizer (S : Set G)) (x : X) (u : BenderSubgroupInverters S) :
    ∀ a ∈ S, (MulAut.conj (x : G)) u.1 * a * ((MulAut.conj (x : G)) u.1)⁻¹ = a⁻¹ := by
  intro a ha
  let e := MulAut.conj (x : G)
  let b := (x : G)⁻¹ * a * (x : G)
  have hb : b ∈ S := by
    simpa only [inv_inv] using (mem_normalizer_iff.mp (hXN (X.inv_mem x.2)) a).mp ha
  have heb : e b = a := by simp [e, b, MulAut.conj_apply, mul_assoc]
  have he := congrArg e (u.2.2 b hb)
  simpa only [map_mul, map_inv, heb] using he

/-- A three-subgroup normalizing S centralizes exactly e of its 7e inverters. -/
public theorem bender_seven_commuting_inverter_card
    (h : Janko1CentralizerData G) (normalizerData : BenderNormalizerData h)
    (geometry : BenderNormalizerGeometry h) (e : ℕ) (he : e ≤ 1)
    (hseven : ∀ x : normalizer (h.sylow : Set G), orderOf (x : G) = 7 →
      Nat.card {t : G // orderOf t = 2 ∧ t * (x : G) * t⁻¹ = (x : G)⁻¹} = 7 * e)
    (X : BenderSubgroupsOfOrder (normalizer (h.sylow : Set G)) 3)
    (S : BenderSubgroupsOfOrder (normalizer (h.sylow : Set G)) 7)
    (hXN : X.1 ≤ normalizer (S.1 : Set G)) :
    Nat.card {u : BenderSubgroupInverters S.1 // X.1 ≤ centralizer ({u.1} : Set G)} = e := by
  classical
  let I := BenderSubgroupInverters S.1
  let J := {u : I // X.1 ≤ centralizer ({u.1} : Set G)}
  have : Finite I := by unfold I BenderSubgroupInverters; infer_instance
  have hI : Nat.card I = 7 * e := bender_subgroup_inverters_card h e hseven S
  let : MulAction X.1 I :=
    { smul x u := ⟨(MulAut.conj (x : G)) u.1,
        ((MulAut.conj (x : G)).orderOf_eq u.1).trans u.2.1,
        inverter_conj S.1 X.1 hXN x u⟩
      one_smul := fun u => Subtype.ext (by
        change (MulAut.conj (1 : G)) u.1 = u.1
        simp)
      mul_smul := fun x y u => Subtype.ext (by
        change (MulAut.conj ((x : G) * (y : G))) u.1 =
          (MulAut.conj (x : G)) ((MulAut.conj (y : G)) u.1)
        simp [MulAut.conj_apply, mul_assoc]) }
  have hfixed (u : I) : u ∈ MulAction.fixedPoints X.1 I ↔
      X.1 ≤ centralizer ({u.1} : Set G) := by
    rw [MulAction.mem_fixedPoints]
    constructor
    · intro hfix x hx
      have he := congrArg Subtype.val (hfix ⟨x, hx⟩)
      change x * u.1 * x⁻¹ = u.1 at he
      exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he)
    · intro hfix x
      apply Subtype.ext
      change (x : G) * u.1 * (x : G)⁻¹ = u.1
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp (hfix x.2))
  have hs : Subsingleton J := ⟨fun u v => Subtype.ext
    (bender_seven_commuting_inverter_unique h normalizerData geometry X S u.1 v.1 u.2 v.2)⟩
  change Nat.card J = e
  have hecases : e = 0 ∨ e = 1 := by omega
  rcases hecases with he0 | he1
  · rw [he0, Nat.mul_zero] at hI
    have hJ : Nat.card J ≤ Nat.card I := Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    omega
  · have hPX : IsPGroup 3 X.1 := IsPGroup.of_card (n := 1) (by simpa using X.2.2)
    obtain ⟨u, hu⟩ := hPX.nonempty_fixed_point_of_prime_not_dvd_card I (by rw [hI, he1]; decide)
    rw [he1]
    exact Nat.card_eq_one_iff_unique.mpr ⟨hs, ⟨⟨u, (hfixed u).mp hu⟩⟩⟩

/-- Exactly 2e septuple involutions commute with each actual three-subgroup. -/
public theorem bender_three_septuple_commuting_card
    (h : Janko1CentralizerData G) (normalizerData : BenderNormalizerData h)
    (geometry : BenderNormalizerGeometry h) (e : ℕ) (he : e ≤ 1)
    (hseven : ∀ x : normalizer (h.sylow : Set G), orderOf (x : G) = 7 →
      Nat.card {t : G // orderOf t = 2 ∧ t * (x : G) * t⁻¹ = (x : G)⁻¹} = 7 * e)
    (X : BenderSubgroupsOfOrder (normalizer (h.sylow : Set G)) 3) :
    Nat.card {u : BenderOutsideInvolutions (normalizer (h.sylow : Set G)) //
      X.1 ≤ centralizer ({u.1} : Set G) ∧
      Nat.card (BenderFiber (normalizer (h.sylow : Set G))
        (benderRightCoset (normalizer (h.sylow : Set G)) u.1)) = 7} = 2 * e := by
  classical
  let H := normalizer (h.sylow : Set G)
  let A := {S : BenderSubgroupsOfOrder H 7 // X.1 ≤ normalizer (S.1 : Set G)}
  let F := fun S : A => {u : BenderSubgroupInverters S.1.1 //
    X.1 ≤ centralizer ({u.1} : Set G)}
  let E := {u : BenderOutsideInvolutions H // X.1 ≤ centralizer ({u.1} : Set G) ∧
    Nat.card (BenderFiber H (benderRightCoset H u.1)) = 7}
  let f : (Σ S : A, F S) → E := fun a =>
    ⟨⟨a.2.1.1, a.2.1.2.1, bender_seven_inverter_outside h a.1.1 a.2.1⟩, a.2.2,
      (bender_fiber_card_of_inverted_subgroup H a.2.1.1 a.2.1.2.1
        (bender_seven_inverter_outside h a.1.1 a.2.1) a.1.1.1
        (bender_seven_inverted_exact h geometry a.1.1 a.2.1)).trans a.1.1.2.2⟩
  have hfi : Function.Injective f := by
    rintro ⟨S, u⟩ ⟨T, v⟩ huv
    have huvG : u.1.1 = v.1.1 := congrArg (fun a : E => a.1.1) huv
    have hST : S = T := by
      apply Subtype.ext
      apply Subtype.ext
      apply Subgroup.ext
      intro a
      rw [bender_seven_inverted_exact h geometry S.1 u.1 a,
        bender_seven_inverted_exact h geometry T.1 v.1 a, huvG]
    subst T
    have huv' : u = v := Subtype.ext (Subtype.ext huvG)
    subst v
    rfl
  have hfs : Function.Surjective f := by
    intro u
    obtain ⟨K, hK, _⟩ := geometry.inverted_subgroup u.1.1 u.1.2.1 u.1.2.2
    have hKH : K ≤ H := fun a ha => ((hK a).mp ha).1
    have hcard : Nat.card K = 7 :=
      (bender_fiber_card_of_inverted_subgroup H u.1.1 u.1.2.1 u.1.2.2 K hK).symm.trans u.2.2
    let S : A := ⟨⟨K, hKH, hcard⟩,
      bender_commuting_normalizes_inverted H X.1 K u.1.1 X.2.1 u.2.1 hK⟩
    refine ⟨⟨S, ⟨⟨u.1.1, u.1.2.1, fun a ha => ((hK a).mp ha).2⟩, u.2.1⟩⟩, ?_⟩
    rfl
  have hA : Nat.card A = 2 := geometry.three_normalizes_seven X.1 X.2.1 X.2.2
  have : Finite A := by unfold A BenderSubgroupsOfOrder; infer_instance
  let : Fintype A := Fintype.ofFinite A
  have : ∀ a : A, Finite (F a) := fun a => by unfold F BenderSubgroupInverters; infer_instance
  have hF (S : A) : Nat.card (F S) = e :=
    bender_seven_commuting_inverter_card h normalizerData geometry e he hseven X S.1 S.2
  change Nat.card E = 2 * e
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hfi, hfs⟩), Nat.card_sigma]
  simp only [hF, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card, hA]

end CFSG.Quasithin.Janko1CentralizerData
