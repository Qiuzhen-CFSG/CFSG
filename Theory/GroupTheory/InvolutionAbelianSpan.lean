module
public import Theory.GroupTheory.PGroup.OmegaAmbient
public import Theory.GroupTheory.ThreeCyclicFourSpan
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic
/-!
# Involutions in an abelian span and their centralizer orbits

An involution in an abelian subgroup normalized by R has its commutators
with R in the first omega subgroup of the intersection. Fixed-point-free
conjugation on a four-group identifies any nontrivial invariant displacement
with that whole four-group. When the displacement is central in R, its
literal commutator homomorphism supplies conjugators and the centralizer
order. The final lemma gives the corresponding Frattini factorization.

These are the finite-group calculations used for the opposite involution in
Aschbacher--Smith, 14.3.22, printed p.999. All normality is relative to the
specified subgroups.
-/

public section
open Subgroup
open scoped commutatorElement IsMulCommutative

namespace Theory.GroupTheory
variable {G : Type*} [Group G]

/-- An involution in a normalized abelian span has elementary displacement in its intersection with the actor. -/
theorem commutator_le_omega_of_abelian_span
    (R X : Subgroup G) [IsMulCommutative X] (w : G)
    (hRX : R ≤ normalizer (X : Set G)) (hwX : w ∈ X)
    (hwR : w ∈ normalizer (R : Set G)) (hw2 : w ^ 2 = 1) :
    ⁅R, zpowers w⁆ ≤ omegaOneAmbient (X ⊓ R) := by
  have hWR : zpowers w ≤ normalizer (R : Set G) := zpowers_le.mpr hwR
  have hRW : ⁅R, zpowers w⁆ ≤ R := le_normalizer_iff_commutator_le_left.mp hWR
  have hWX : zpowers w ≤ X := zpowers_le.mpr hwX
  let : IsElementaryAbelian 2 (zpowers w) := IsElementaryAbelian.zpowers_of_pow_eq_one hw2
  apply commutator_le.mpr
  intro r hr y hy
  have hyX := hWX hy
  have hconj : r * y * r⁻¹ ∈ X := (mem_normalizer_iff.mp (hRX hr) y).mp hyX
  have hcomm : Commute (r * y * r⁻¹) y⁻¹ := congrArg Subtype.val
    (mul_comm' (⟨r * y * r⁻¹, hconj⟩ : X) ⟨y⁻¹, X.inv_mem hyX⟩)
  have hy2 : y ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian y hy
  apply (omegaOneAmbient_le_iff (X ⊓ R) (omegaOneAmbient (X ⊓ R))).mp le_rfl _
    ⟨X.mul_mem hconj (X.inv_mem hyX), hRW (commutator_mem_commutator hr hy)⟩
  rw [hcomm.mul_pow, ← MulAut.conj_apply r y, ← map_pow, hy2, map_one, inv_pow, hy2]
  simp

/-- A nontrivial invariant subgroup of a fixed-free four-group is the whole group. -/
theorem invariant_four_eq_of_fixed_free [Finite G]
    (V W : Subgroup G) (a : G) (hV : Nat.card V = 4)
    (hWV : W ≤ V) (hW : W ≠ ⊥) (haW : a ∈ normalizer (W : Set G))
    (hfix : V ⊓ centralizer ({a} : Set G) = ⊥) : W = V := by
  by_contra hne
  have hle : Nat.card W ≤ 4 := (card_le_of_le hWV).trans hV.le
  have hfour : Nat.card W ≠ 4 := fun hh => hne
    (eq_of_le_of_card_ge hWV (by rw [hV, hh]))
  have hdvd : Nat.card W ∣ 4 := hV ▸ card_dvd_of_le hWV
  have hthree : Nat.card W ≠ 3 := by intro hh; norm_num [hh] at hdvd
  have hpos := (one_lt_card_iff_ne_bot W).mpr hW
  have hW2 : Nat.card W = 2 := by omega
  obtain ⟨x, hx, huniq⟩ := (Nat.card_eq_two_iff' (1 : W)).mp hW2
  let y : W := ⟨a * x * a⁻¹, (mem_normalizer_iff.mp haW x).mp x.property⟩
  have hy : y ≠ 1 := by
    intro he
    apply hx
    apply Subtype.ext
    have hh : (MulAut.conj a) (x : G) = (MulAut.conj a) 1 := by
      have hh : a * (x : G) * a⁻¹ = 1 := congrArg Subtype.val he
      simpa only [MulAut.conj_apply, map_one] using hh
    exact (MulAut.conj a).injective hh
  have hxy : y = x := huniq y hy
  have hxC : (x : G) ∈ centralizer ({a} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    have hh : a * (x : G) * a⁻¹ = x := congrArg Subtype.val hxy
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  exact hx (Subtype.ext (mem_bot.mp (hfix ▸ ⟨hWV x.property, hxC⟩)))


/-- The literal commutator map has the full displacement as image and the original relative centralizer as kernel. -/
theorem exists_central_involution_commutator_hom [Finite G]
    (R : Subgroup G) (w : G) (hw : orderOf w = 2)
    (hwR : w ∈ normalizer (R : Set G))
    (hcent : ⁅R, zpowers w⁆ ≤ centralizer (R : Set G)) :
    ∃ f : R →* G, (∀ r, f r = ⁅(r : G), w⁆) ∧
      f.range = ⁅R, zpowers w⁆ ∧ f.ker = (centralizer ({w} : Set G)).subgroupOf R := by
  classical
  let f : R →* G := {
    toFun r := ⁅(r : G), w⁆
    map_one' := by simp
    map_mul' r t := by
      have ht := hcent (commutator_mem_commutator t.property (mem_zpowers w))
      have hrc : (r : G) * ⁅(t : G),w⁆ = ⁅(t : G),w⁆ * r := ht r r.property
      change ⁅(r : G) * t,w⁆ = ⁅(r : G),w⁆ * ⁅(t : G),w⁆
      rw [commutatorElement_mul_left_eq_conj_mul, hrc, mul_inv_cancel_right]
      have hcomm : Commute ⁅(t : G),w⁆ ⁅(r : G),w⁆ := by
        have hwr : ⁅(r : G),w⁆ ∈ R := by
          exact (le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr hwR))
            (commutator_mem_commutator r.property (mem_zpowers w))
        exact (ht _ hwr).symm
      exact hcomm.eq }
  refine ⟨f, fun _ => rfl, ?_, ?_⟩
  · apply le_antisymm
    · rintro _ ⟨r, rfl⟩
      exact commutator_mem_commutator r.property (mem_zpowers w)
    · apply commutator_le.mpr
      intro r hr y hy
      have hy' : y = w ∨ y = 1 := by
        obtain ⟨n, hn, he⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hy)
        rw [Finset.mem_range, hw] at hn
        interval_cases n <;> simp_all
      rcases hy' with rfl | rfl
      · exact ⟨⟨r,hr⟩,rfl⟩
      · simp
  · ext r
    change ⁅(r : G),w⁆ = 1 ↔ (r : G) ∈ centralizer ({w} : Set G)
    rw [commutatorElement_eq_one_iff_mul_comm, mem_centralizer_singleton_iff]

/-- Central displacement computes the order of the actual centralizer in the actor. -/
theorem involution_centralizer_card_of_central_commutator [Finite G]
    (R V : Subgroup G) (w : G) (hw : orderOf w = 2)
    (hwR : w ∈ normalizer (R : Set G))
    (hcomm : ⁅R, zpowers w⁆ = V) (hcent : V ≤ centralizer (R : Set G)) :
    Nat.card (R ⊓ centralizer ({w} : Set G) : Subgroup G) * Nat.card V = Nat.card R := by
  obtain ⟨f, _, hr, hk⟩ := exists_central_involution_commutator_hom R w hw hwR
    (hcomm.symm ▸ hcent)
  have hh := f.ker.card_mul_index
  rw [index_ker, hr, hcomm, hk] at hh
  have hcard : Nat.card ((centralizer ({w} : Set G)).subgroupOf R) =
      Nat.card (R ⊓ centralizer ({w} : Set G) : Subgroup G) := by
    rw [← card_map_of_injective (f := R.subtype) R.subtype_injective, subgroupOf_map_subtype, inf_comm]
  rwa [hcard] at hh

/-- Every displacement element is realized by an actual conjugator in the actor. -/
theorem exists_conjugator_of_central_commutator [Finite G]
    (R V : Subgroup G) (w : G) (hw : orderOf w = 2)
    (hwR : w ∈ normalizer (R : Set G))
    (hcomm : ⁅R, zpowers w⁆ = V) (hcent : V ≤ centralizer (R : Set G)) :
    ∀ v ∈ V, ∃ r ∈ R, r * w * r⁻¹ = v * w := by
  obtain ⟨f, hf, hr, _⟩ := exists_central_involution_commutator_hom R w hw hwR
    (hcomm.symm ▸ hcent)
  intro v hv
  have hv' : v ∈ f.range := hr.symm ▸ (hcomm.symm ▸ hv)
  obtain ⟨r, hr⟩ := hv'
  refine ⟨r, r.property, ?_⟩
  rw [hf] at hr
  rw [← hr, commutatorElement_def]
  group


/-- The omega subgroup retains the marked square subgroup and the third involution. -/
theorem omega_three_cyclic_four_span [Finite G]
    (X V : Subgroup G) [IsMulCommutative X] [IsElementaryAbelian 2 V]
    (x y w : G) (hx : orderOf x = 4) (hy : orderOf y = 4) (hw : w ^ 2 = 1)
    (hxy : x ^ 2 ≠ y ^ 2) (hX : X = zpowers x ⊔ zpowers y ⊔ zpowers w)
    (hVX : V ≤ X) (hxV : x ^ 2 ∈ V) (hyV : y ^ 2 ∈ V) :
    omegaOneAmbient X = V ⊔ zpowers w := by
  have hxX : x ∈ X := hX.symm ▸ mem_sup_left (mem_sup_left (mem_zpowers x))
  have hyX : y ∈ X := hX.symm ▸ mem_sup_left (mem_sup_right (mem_zpowers y))
  have hwX : w ∈ X := hX.symm ▸ mem_sup_right (mem_zpowers w)
  have hcomm (a b : G) (ha : a ∈ X) (hb : b ∈ X) : Commute a b :=
    congrArg Subtype.val (mul_comm' (⟨a,ha⟩ : X) ⟨b,hb⟩)
  have hPX : zpowers x ⊔ zpowers y ≤ X := sup_le (zpowers_le.mpr hxX) (zpowers_le.mpr hyX)
  have hWX : zpowers w ≤ X := zpowers_le.mpr hwX
  apply le_antisymm
  · apply (omegaOneAmbient_le_iff _ _).mpr
    intro t ht ht2
    have hWP : zpowers w ≤ normalizer ((zpowers x ⊔ zpowers y : Subgroup G) : Set G) :=
      (show zpowers w ≤ centralizer ((zpowers x ⊔ zpowers y : Subgroup G) : Set G) from
        fun a ha b hb => (hcomm b a (hPX hb) (hWX ha)).eq).trans (centralizer_le_normalizer _)
    rw [hX] at ht
    change t ∈ (↑(zpowers x ⊔ zpowers y ⊔ zpowers w) : Set G) at ht
    rw [coe_mul_of_right_le_normalizer_left _ _ hWP] at ht
    obtain ⟨u, hu, v, hv, rfl⟩ := ht
    let : IsElementaryAbelian 2 (zpowers w) := IsElementaryAbelian.zpowers_of_pow_eq_one hw
    have hv2 : v ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian v hv
    have hu2 : u ^ 2 = 1 := by
      rw [(hcomm u v (hPX hu) (hWX hv)).mul_pow, hv2, mul_one] at ht2
      exact ht2
    have huV : u ∈ V := (sup_le (zpowers_le.mpr hxV) (zpowers_le.mpr hyV))
      (Theory.GroupTheory.square_one_mem_square_join x y u hx hy hxy (hcomm x y hxX hyX) hu hu2)
    exact (V ⊔ zpowers w).mul_mem (mem_sup_left huV) (mem_sup_right hv)
  · apply sup_le
    · exact (omegaOneAmbient_eq_self V).symm.le.trans (omegaOneAmbient_mono hVX)
    · apply zpowers_le.mpr
      exact (omegaOneAmbient_le_iff X (omegaOneAmbient X)).mp le_rfl w hwX hw

/-- Transitivity on the opposite involution coset yields the literal centralizer factorization. -/
theorem eq_sup_centralizer_of_involution_coset [Finite G]
    (I R V X : Subgroup G) [IsMulCommutative X] (w : G)
    (hRI : R ≤ I) (hVX : V ≤ X) (hwX : w ∈ X)
    (hw : orderOf w = 2) (hwV : w ∉ V)
    (hIX : I ≤ normalizer (X : Set G)) (hIV : I ≤ normalizer (V : Set G))
    (homega : omegaOneAmbient X = V ⊔ zpowers w)
    (horbit : ∀ v ∈ V, ∃ r ∈ R, r * w * r⁻¹ = v * w) :
    I = R ⊔ (I ⊓ centralizer ({w} : Set G)) := by
  classical
  apply le_antisymm
  · intro i hi
    have htX : i * w * i⁻¹ ∈ X := (mem_normalizer_iff.mp (hIX hi) w).mp hwX
    have ht2 : (i * w * i⁻¹) ^ 2 = 1 := by
      rw [← MulAut.conj_apply i w, ← map_pow, show w ^ 2 = 1 from hw ▸ pow_orderOf_eq_one w, map_one]
    have ht : i * w * i⁻¹ ∈ V ⊔ zpowers w := homega ▸
      (omegaOneAmbient_le_iff X (omegaOneAmbient X)).mp le_rfl _ htX ht2
    have hWV : zpowers w ≤ normalizer (V : Set G) := by
      apply zpowers_le.mpr
      apply centralizer_le_normalizer
      intro v hv
      exact congrArg Subtype.val (mul_comm' (⟨v,hVX hv⟩ : X) ⟨w,hwX⟩)
    change i * w * i⁻¹ ∈ (↑(V ⊔ zpowers w) : Set G) at ht
    rw [coe_mul_of_right_le_normalizer_left _ _ hWV] at ht
    obtain ⟨v,hv,y,hy,he⟩ := ht
    have hy' : y = w ∨ y = 1 := by
      obtain ⟨n,hn,he⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hy)
      rw [Finset.mem_range,hw] at hn
      interval_cases n <;> simp_all
    have hiy : i * w * i⁻¹ = v * w := by
      rcases hy' with rfl | rfl
      · exact he.symm
      · exfalso
        apply hwV
        apply (mem_normalizer_iff.mp (hIV hi) w).mpr
        have hvt : v = i * w * i⁻¹ := by simpa only [mul_one] using he
        exact hvt ▸ hv
    obtain ⟨r,hr,hri⟩ := horbit v hv
    have hc : r⁻¹ * i ∈ I ⊓ centralizer ({w} : Set G) := by
      refine ⟨I.mul_mem (I.inv_mem (hRI hr)) hi, ?_⟩
      apply mem_centralizer_singleton_iff.mpr
      apply mul_inv_eq_iff_eq_mul.mp
      calc
        (r⁻¹ * i) * w * (r⁻¹ * i)⁻¹ = r⁻¹ * (i * w * i⁻¹) * r := by group
        _ = r⁻¹ * (r * w * r⁻¹) * r := by rw [hiy, ← hri]
        _ = w := by group
    have hh := (R ⊔ (I ⊓ centralizer ({w} : Set G))).mul_mem (mem_sup_left hr) (mem_sup_right hc)
    simpa only [mul_inv_cancel_left] using hh
  · exact sup_le hRI inf_le_left

end Theory.GroupTheory
