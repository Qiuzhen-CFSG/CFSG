module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Distribution.Geometry
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Distribution.Incidences.Counting
public import Theory.GroupTheory.PrimeOrderCentralizerSylow


/-!
# The local inverter counts in Bender's normalizer

An involution inverting a seven-element makes the normalizer of its cyclic
subgroup even. Bender (4.3) then identifies its centralizer with that subgroup,
and multiplication by the involution identifies the seven-subgroup with the
entire inverter set. Sylow conjugacy inside the actual normalizer of order 168
makes the resulting zero-or-seven count uniform.

Every inverter of an element of order six centralizes its cube. Involution
fusion and the source centralizer isomorphism transport the count into the
actual `A₅ × C₂`. There the cube is central, so inversion is equivalent to
inversion of the fourth power, of order three. Sylow conjugacy reduces this
to one small kernel-checked count in the concrete model.

These are literal ambient involution counts, supplying the two remaining
local inputs of `bender_inversion_counts_of_uniform_inverters`. The geometry
record is accepted at the final interface; its incidence data is not needed
for these local counts.

Source: H. Bender, *Finite groups with large subgroups*, Illinois J. Math.
18 (1974), §4, printed pp.226–227, immediately following (4.3).
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData
namespace LocalInverters
variable {G K : Type*} [Group G] [Group K]

private theorem card_map (e : G ≃* K) (x : G) :
    Nat.card {t : G // orderOf t = 2 ∧ t * x * t⁻¹ = x⁻¹} =
      Nat.card {t : K // orderOf t = 2 ∧ t * e x * t⁻¹ = (e x)⁻¹} := by
  apply Nat.card_congr
  exact e.toEquiv.subtypeEquiv (fun t => by
    change (orderOf t = 2 ∧ t * x * t⁻¹ = x⁻¹) ↔
      (orderOf (e t) = 2 ∧ e t * e x * (e t)⁻¹ = (e x)⁻¹)
    rw [e.orderOf_eq]
    apply and_congr_right
    intro _
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, e.injective.eq_iff])

private theorem inverts_mem_zpowers (t x y : G) (hx : t * x * t⁻¹ = x⁻¹)
    (hy : y ∈ zpowers x) : t * y * t⁻¹ = y⁻¹ := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hy
  change (MulAut.conj t) (x ^ n) = (x ^ n)⁻¹
  rw [map_zpow, show (MulAut.conj t) x = x⁻¹ from hx, inv_zpow]

private theorem card_eq_of_zpowers_eq (x y : G) (he : zpowers x = zpowers y) :
    Nat.card {t : G // orderOf t = 2 ∧ t * x * t⁻¹ = x⁻¹} =
      Nat.card {t : G // orderOf t = 2 ∧ t * y * t⁻¹ = y⁻¹} := by
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro t
  apply and_congr_right
  intro _
  exact ⟨fun hx => inverts_mem_zpowers t x y hx (he ▸ mem_zpowers y),
    fun hy => inverts_mem_zpowers t y x hy (he ▸ mem_zpowers x)⟩

private theorem prime_card_eq [Finite K] (p : ℕ) [Fact p.Prime]
    (hP : ∀ P : Sylow p K, Nat.card P = p) (f : K →* G)
    (x y : K) (hx : orderOf x = p) (hy : orderOf y = p) :
    Nat.card {t : G // orderOf t = 2 ∧ t * f x * t⁻¹ = (f x)⁻¹} =
      Nat.card {t : G // orderOf t = 2 ∧ t * f y * t⁻¹ = (f y)⁻¹} := by
  obtain ⟨g, hg⟩ := exists_conj_mem_of_sylow_card_eq_prime (zpowers y) y
    (mem_zpowers y) hy hP x hx
  have he : zpowers (g * x * g⁻¹) = zpowers y :=
    eq_of_le_of_card_ge (zpowers_le.mpr hg) (by
      rw [Nat.card_zpowers, Nat.card_zpowers, hy]
      exact le_of_eq (((MulAut.conj g).orderOf_eq x).trans hx).symm)
  have hem := congrArg (fun S : Subgroup K => S.map f) he
  simp only [MonoidHom.map_zpowers, map_mul, map_inv] at hem
  exact (card_map (MulAut.conj (f g)) (f x)).trans (card_eq_of_zpowers_eq _ _ hem)

private theorem seven_card_of_inverter [Finite G] (x t : G)
    (hx : orderOf x = 7) (ht : orderOf t = 2)
    (hinv : t * x * t⁻¹ = x⁻¹)
    (hC : centralizer (zpowers x : Set G) = zpowers x) :
    Nat.card {u : G // orderOf u = 2 ∧ u * x * u⁻¹ = x⁻¹} = 7 := by
  have ht2 : t * t = 1 := by
    simpa only [pow_two] using (orderOf_eq_prime_iff.mp ht).1
  have htnot : t ∉ zpowers x := by
    intro hm
    have hd := orderOf_dvd_natCard (⟨t, hm⟩ : zpowers x)
    rw [← orderOf_coe ⟨t, hm⟩, ht, Nat.card_zpowers, hx] at hd
    norm_num at hd
  have hinvS (a : zpowers x) : t * (a : G) * t⁻¹ = (a : G)⁻¹ :=
    inverts_mem_zpowers t x a hinv a.2
  have hprod (a : zpowers x) : orderOf ((a : G) * t) = 2 := by
    apply orderOf_eq_prime
    · calc
        ((a : G) * t) ^ 2 = a * (t * (a : G) * t⁻¹) * (t * t) := by simp only [pow_two]; group
        _ = 1 := by rw [hinvS, ht2]; simp
    · intro he
      apply htnot
      have hate : t = (a : G)⁻¹ := by
        exact eq_inv_of_mul_eq_one_right he
      rw [hate]
      exact (zpowers x).inv_mem a.2
  have hprodInv (a : zpowers x) :
      ((a : G) * t) * x * ((a : G) * t)⁻¹ = x⁻¹ := by
    have hac : (a : G) * x = x * a := by
      apply mem_centralizer_singleton_iff.mp
      rw [← centralizer_closure, ← zpowers_eq_closure, hC]
      exact a.2
    calc
      _ = a * (t * x * t⁻¹) * (a : G)⁻¹ := by group
      _ = a * x⁻¹ * (a : G)⁻¹ := by rw [hinv]
      _ = x⁻¹ := by
        have hc : Commute (a : G) x := hac
        rw [hc.inv_right.eq]
        simp [mul_assoc]
  have hback (u : G) (hu : u * x * u⁻¹ = x⁻¹) : u * t ∈ zpowers x := by
    rw [← hC, zpowers_eq_closure, centralizer_closure, mem_centralizer_singleton_iff]
    apply mul_inv_eq_iff_eq_mul.mp
    calc
      (u * t) * x * (u * t)⁻¹ = u * (t * x * t⁻¹) * u⁻¹ := by group
      _ = u * x⁻¹ * u⁻¹ := by rw [hinv]
      _ = (u * x * u⁻¹)⁻¹ := by group
      _ = x := by rw [hu, inv_inv]
  let e : zpowers x ≃ {u : G // orderOf u = 2 ∧ u * x * u⁻¹ = x⁻¹} :=
    { toFun := fun a => ⟨a * t, hprod a, hprodInv a⟩
      invFun := fun u => ⟨u.1 * t, hback u.1 u.2.2⟩
      left_inv := by
        intro a
        apply Subtype.ext
        change ((a : G) * t) * t = a
        rw [mul_assoc, ht2, mul_one]
      right_inv := by
        intro u
        apply Subtype.ext
        change (u.1 * t) * t = u.1
        rw [mul_assoc, ht2, mul_one] }
  rw [← Nat.card_congr e, Nat.card_zpowers, hx]

private abbrev M := alternatingGroup (Fin 5) × Multiplicative (ZMod 2)
private def three : M :=
  (⟨Equiv.swap 0 1 * Equiv.swap 1 2, by simp [Equiv.Perm.mem_alternatingGroup]⟩, 1)
private theorem three_order : orderOf three = 3 := by
  apply orderOf_eq_prime
  · decide +kernel
  · decide +kernel
private theorem three_count :
    Fintype.card {t : M // t ^ 2 = 1 ∧ t ≠ 1 ∧ t * three * t⁻¹ = three⁻¹} = 6 := by
  decide +kernel
private theorem model_card : Nat.card M = 120 := by
  rw [Nat.card_prod, nat_card_alternatingGroup]
  norm_num [Nat.factorial, Nat.card_eq_fintype_card]
private theorem three_inverter_card (x : M) (hx : orderOf x = 3) :
    Nat.card {t : M // orderOf t = 2 ∧ t * x * t⁻¹ = x⁻¹} = 6 := by
  have hP (P : Sylow 3 M) : Nat.card P = 3 := by
    rw [P.card_eq_multiplicity, model_card]
    decide +kernel
  change Nat.card {t : M // orderOf t = 2 ∧ t * (MonoidHom.id M) x * t⁻¹ = ((MonoidHom.id M) x)⁻¹} = 6
  rw [prime_card_eq 3 hP (MonoidHom.id M) x three hx three_order]
  change Nat.card {t : M // orderOf t = 2 ∧ t * three * t⁻¹ = three⁻¹} = 6
  let e : {t : M // orderOf t = 2 ∧ t * three * t⁻¹ = three⁻¹} ≃
      {t : M // t ^ 2 = 1 ∧ t ≠ 1 ∧ t * three * t⁻¹ = three⁻¹} :=
    Equiv.subtypeEquivRight (fun t => by rw [orderOf_eq_prime_iff, and_assoc])
  exact (Nat.card_congr e).trans ((Nat.card_eq_fintype_card).trans three_count)

private theorem cube_eq_one : ∀ a : alternatingGroup (Fin 5), a ^ 6 = 1 → a ^ 2 ≠ 1 → a ^ 3 = 1 := by
  decide +kernel

private theorem model_six_card (x : M) (hx : orderOf x = 6) :
    Nat.card {t : M // orderOf t = 2 ∧ t * x * t⁻¹ = x⁻¹} = 6 := by
  have hx6 : x ^ 6 = 1 := hx ▸ pow_orderOf_eq_one x
  have hsecond : ∀ a : Multiplicative (ZMod 2), a ^ 2 = 1 := by decide +kernel
  have hx3 : x.1 ^ 3 = 1 := cube_eq_one x.1 (congrArg Prod.fst hx6) (by
    intro hfirst
    have hx2 : x ^ 2 = 1 := Prod.ext hfirst (hsecond x.2)
    have hd := orderOf_dvd_of_pow_eq_one hx2
    rw [hx] at hd
    norm_num at hd)
  have hcube (t : M) : t * x ^ 3 * t⁻¹ = (x ^ 3)⁻¹ := by
    apply Prod.ext
    · simp [hx3]
    · change t.2 * x.2 ^ 3 * t.2⁻¹ = (x.2 ^ 3)⁻¹
      have h2 : (x.2 ^ 3) ^ 2 = 1 := by
        rw [← pow_mul]
        exact congrArg Prod.snd hx6
      rw [mul_right_comm, mul_inv_cancel, one_mul]
      exact (inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using h2)).symm
  have hxsplit : x = x ^ 4 * x ^ 3 := by
    rw [← pow_add]
    change x = x ^ (6 + 1)
    rw [pow_succ, hx6, one_mul]
  have hpred (t : M) : t * x * t⁻¹ = x⁻¹ ↔ t * x ^ 4 * t⁻¹ = (x ^ 4)⁻¹ := by
    constructor
    · intro ht
      change (MulAut.conj t) (x ^ 4) = (x ^ 4)⁻¹
      rw [map_pow, show (MulAut.conj t) x = x⁻¹ from ht, inv_pow]
    · intro ht
      calc
        t * x * t⁻¹ = (t * x ^ 4 * t⁻¹) * (t * x ^ 3 * t⁻¹) := by
          conv_lhs => rw [hxsplit]
          group
        _ = (x ^ 4)⁻¹ * (x ^ 3)⁻¹ := by rw [ht, hcube]
        _ = x⁻¹ := by
          rw [← inv_pow, ← inv_pow, ← pow_add,
            show 4 + 3 = 6 + 1 by decide, pow_succ, inv_pow, hx6]
          simp
  have he : Nat.card {t : M // orderOf t = 2 ∧ t * x * t⁻¹ = x⁻¹} =
      Nat.card {t : M // orderOf t = 2 ∧ t * x ^ 4 * t⁻¹ = (x ^ 4)⁻¹} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun t => and_congr_right (fun _ => hpred t)))
  rw [he]
  apply three_inverter_card
  rw [orderOf_pow, hx]
  decide

end LocalInverters

open LocalInverters
variable {G : Type*} [Group G] [Finite G]

private theorem bender_seven_inverter_card_of_exists (h : Janko1CentralizerData G)
    (normalizerData : BenderNormalizerData h)
    (x : normalizer (h.sylow : Set G)) (hx : orderOf (x : G) = 7)
    (t : G) (ht : orderOf t = 2) (hinv : t * (x : G) * t⁻¹ = (x : G)⁻¹) :
    Nat.card {u : G // orderOf u = 2 ∧ u * (x : G) * u⁻¹ = (x : G)⁻¹} = 7 := by
  have htN : t ∈ normalizer (zpowers (x : G) : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change zpowers (t * (x : G) * t⁻¹) = zpowers (x : G)
    rw [hinv, zpowers_inv]
  have hEven : Even (Nat.card (normalizer (zpowers (x : G) : Set G))) := by
    rw [even_iff_two_dvd]
    have hd := orderOf_dvd_natCard (⟨t, htN⟩ : normalizer (zpowers (x : G) : Set G))
    rwa [← orderOf_coe ⟨t, htN⟩, ht] at hd
  exact seven_card_of_inverter (x : G) t hx ht hinv
    (normalizerData.seven_centralizer (zpowers (x : G)) (zpowers_le.mpr x.2)
      ((Nat.card_zpowers _).trans hx) hEven)

/-- The order-168 Sylow normalizer has a uniform zero-or-seven ambient
inverter count, using precisely the even-normalizer clause of (4.3). -/
public theorem bender_uniform_seven_inverter_counts (h : Janko1CentralizerData G)
    (normalizerData : BenderNormalizerData h) :
    ∃ e : ℕ, e ≤ 1 ∧ ∀ x : normalizer (h.sylow : Set G), orderOf (x : G) = 7 →
      Nat.card {t : G // orderOf t = 2 ∧ t * (x : G) * t⁻¹ = (x : G)⁻¹} = 7 * e := by
  classical
  let H := normalizer (h.sylow : Set G)
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hP (P : Sylow 7 H) : Nat.card P = 7 := by
    rw [P.card_eq_multiplicity, normalizerData.normalizer_card]
    decide +kernel
  obtain ⟨x₀, hx₀⟩ := exists_prime_orderOf_dvd_card' (G := H) 7 (by
    rw [normalizerData.normalizer_card]; decide)
  have hx₀G : orderOf (x₀ : G) = 7 := (orderOf_coe x₀).trans hx₀
  have heq (x : H) (hx : orderOf (x : G) = 7) :
      Nat.card {t : G // orderOf t = 2 ∧ t * (x : G) * t⁻¹ = (x : G)⁻¹} =
        Nat.card {t : G // orderOf t = 2 ∧ t * (x₀ : G) * t⁻¹ = (x₀ : G)⁻¹} :=
    prime_card_eq 7 hP H.subtype x x₀ ((orderOf_coe x).symm.trans hx) hx₀
  by_cases ht : ∃ t : G, orderOf t = 2 ∧ t * (x₀ : G) * t⁻¹ = (x₀ : G)⁻¹
  · obtain ⟨t, ht, hi⟩ := ht
    refine ⟨1, by omega, fun x hx => ?_⟩
    rw [heq x hx, bender_seven_inverter_card_of_exists h normalizerData x₀ hx₀G t ht hi]
  · refine ⟨0, by omega, fun x hx => ?_⟩
    rw [heq x hx, mul_zero]
    apply Nat.card_eq_zero.mpr
    exact Or.inl ⟨fun t => ht ⟨t.1, t.2⟩⟩

/-- Every ambient element of order six has exactly six inverting involutions,
by fusion into the actual involution-centralizer model. -/
public theorem bender_six_inverter_card [IsSimpleGroup G] (h : Janko1CentralizerData G)
    (x : G) (hx : orderOf x = 6) :
    Nat.card {t : G // orderOf t = 2 ∧ t * x * t⁻¹ = x⁻¹} = 6 := by
  have hx3 : orderOf (x ^ 3) = 2 := by rw [orderOf_pow, hx]; decide
  obtain ⟨g, hg⟩ := h.involutions_conjugate (x ^ 3) hx3
  let e := MulAut.conj g
  let y := e x
  have hy3 : y ^ 3 = h.z := by rw [← map_pow]; exact hg
  have hy : orderOf y = 6 := (e.orderOf_eq x).trans hx
  let C := centralizer ({h.z} : Set G)
  have hyC : y ∈ C := by
    apply mem_centralizer_singleton_iff.mpr
    rw [← hy3]
    exact (Commute.self_pow y 3).eq
  let yC : C := ⟨y, hyC⟩
  have hiC (t : G) (ht : t * y * t⁻¹ = y⁻¹) : t ∈ C := by
    apply mem_centralizer_singleton_iff.mpr
    apply mul_inv_eq_iff_eq_mul.mp
    calc
      t * h.z * t⁻¹ = (MulAut.conj t) (y ^ 3) := by rw [hy3]; rfl
      _ = (y ^ 3)⁻¹ := by rw [map_pow, show (MulAut.conj t) y = y⁻¹ from ht, inv_pow]
      _ = h.z := by
        rw [hy3]
        exact inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using
          (orderOf_eq_prime_iff.mp h.involution).1)
  let ec : {t : G // orderOf t = 2 ∧ t * y * t⁻¹ = y⁻¹} ≃
      {t : C // orderOf t = 2 ∧ t * yC * t⁻¹ = yC⁻¹} :=
    { toFun := fun t => ⟨⟨t.1, hiC t.1 t.2.2⟩,
        (orderOf_coe _).symm.trans t.2.1, Subtype.ext t.2.2⟩
      invFun := fun t => ⟨t.1, (orderOf_coe t.1).trans t.2.1,
        congrArg Subtype.val t.2.2⟩
      left_inv := by intro t; rfl
      right_inv := by intro t; rfl }
  calc
    _ = Nat.card {t : G // orderOf t = 2 ∧ t * y * t⁻¹ = y⁻¹} := card_map e x
    _ = Nat.card {t : C // orderOf t = 2 ∧ t * yC * t⁻¹ = yC⁻¹} := Nat.card_congr ec
    _ = Nat.card {t : M // orderOf t = 2 ∧
        t * h.alternatingCentralizerEquiv yC * t⁻¹ = (h.alternatingCentralizerEquiv yC)⁻¹} :=
      card_map h.alternatingCentralizerEquiv yC
    _ = 6 := model_six_card _ ((h.alternatingCentralizerEquiv.orderOf_eq yC).trans
      ((orderOf_coe yC).symm.trans hy))

/-- The uniform ambient six- and seven-inverter counts used in Bender's
coset distribution. No inversion-count or distribution premise remains. -/
public theorem bender_uniform_local_inverter_counts [IsSimpleGroup G]
    (h : Janko1CentralizerData G) (normalizerData : BenderNormalizerData h)
    (_geometry : BenderNormalizerGeometry h) :
    ∃ e : ℕ, e ≤ 1 ∧
      (∀ x : normalizer (h.sylow : Set G), orderOf (x : G) = 7 →
        Nat.card {t : G // orderOf t = 2 ∧ t * (x : G) * t⁻¹ = (x : G)⁻¹} = 7 * e) ∧
      (∀ x : normalizer (h.sylow : Set G), orderOf (x : G) = 6 →
        Nat.card {t : G // orderOf t = 2 ∧ t * (x : G) * t⁻¹ = (x : G)⁻¹} = 6) := by
  obtain ⟨e, he, hseven⟩ := bender_uniform_seven_inverter_counts h normalizerData
  exact ⟨e, he, hseven, fun x hx => bender_six_inverter_card h x hx⟩

end CFSG.Quasithin.Janko1CentralizerData
