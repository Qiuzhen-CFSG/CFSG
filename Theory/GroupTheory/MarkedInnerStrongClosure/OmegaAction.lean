module

public import Theory.GroupTheory.MarkedInnerStrongClosure.CentralTwoQuotient
public import Theory.Frattini.OmegaProducts

/-!
# Whole-subgroup action from a marked inner involution

Returning conjugates of the marked element z have a common centralizing
factor. Quotients of two such conjugates cancel that factor, so transitivity
on a subgroup of order greater than two puts the whole subgroup into U.
For the first omega of the actual component Sylow, U then fixes it pointwise.
Strong closure and elementarity give square-one Sylow displacements, and
normalization of the component gives Sylow stability.

The intrinsic square-displacement criterion transports under equivalences.
Once a model proves innerness, centerlessness and Sylow-normalizer containment
place the square-one implementer in the actual first omega. These are the
action inputs in Aschbacher--Smith, Proposition 2.2.2, printed p.520,
combined manuscript of 1 March 2004. No U≤L or whole-U innerness is assumed.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.MarkedInnerStrongClosure
variable {G K D : Type*} [Group G] [Group K] [Group D]

theorem map_le_of_transitive_inner_marker
    (S U : Subgroup G) (hU : IsStronglyClosedSet (U : Set G) S ⊤)
    (f : K →* G) (Q : Subgroup K) [Finite Q]
    (hQS : Q.map f ≤ S) (hsize : 2 < Nat.card Q)
    (z : G) (hzU : z ∈ U) (t : Q)
    (haction : ∀ x : K, f ((t : K) * x * (t : K)⁻¹) = z * f x * z⁻¹)
    (htrans : ∀ a : Q, a ≠ 1 → IsConj (t : K) (a : K)) :
    Q.map f ≤ U := by
  classical
  let c : G := (f t)⁻¹ * z
  have hcS : c ∈ S :=
    S.mul_mem (S.inv_mem (hQS (mem_map_of_mem f t.property))) (hU.1 hzU)
  have hcf (x : K) : Commute c (f x) := by
    apply mul_inv_eq_iff_eq_mul.mp
    change ((f t)⁻¹ * z) * f x * ((f t)⁻¹ * z)⁻¹ = f x
    calc
      _ = (f t)⁻¹ * (z * f x * z⁻¹) * f t := by group
      _ = (f t)⁻¹ * f ((t : K) * x * (t : K)⁻¹) * f t := by rw [haction]
      _ = f x := by simp only [map_mul, map_inv]; group
  have hz : z = f t * c := by dsimp [c]; group
  have hforced (a : Q) (ha : a ≠ 1) : f a * c ∈ U := by
    obtain ⟨g, hg⟩ := isConj_iff.mp (htrans a ha)
    have he : f g * z * (f g)⁻¹ = f a * c := by
      rw [hz]
      calc
        _ = f g * f t * (c * (f g)⁻¹) := by group
        _ = f g * f t * ((f g)⁻¹ * c) := by rw [(hcf g).inv_right.eq]
        _ = f (g * (t : K) * g⁻¹) * c := by simp only [map_mul, map_inv]; group
        _ = f a * c := by rw [hg]
    have hs : f a * c ∈ S := S.mul_mem (hQS (mem_map_of_mem f a.property)) hcS
    have hu := hU.2 z hzU (f g)⁻¹ (mem_top _) (by simpa only [inv_inv, he] using hs)
    change f a * c ∈ (U : Set G)
    simpa only [inv_inv, he] using hu
  let := Fintype.ofFinite Q
  have hthree : 3 ≤ ENat.card Q := by
    rw [ENat.card_eq_coe_fintype_card]
    have hh : 3 ≤ Fintype.card Q := by
      rw [← Nat.card_eq_fintype_card]
      omega
    exact_mod_cast hh
  rintro y ⟨q, hq, rfl⟩
  let q0 : Q := ⟨q, hq⟩
  obtain ⟨b, hb, hbq⟩ := ENat.exists_ne_ne_of_three_le hthree (1 : Q) q0⁻¹
  let a : Q := q0 * b
  have ha : a ≠ 1 := by
    intro he
    apply hbq
    calc
      b = q0⁻¹ * (q0 * b) := by group
      _ = q0⁻¹ := by change q0⁻¹ * a = q0⁻¹; rw [he, mul_one]
  have hab : (a : K) * (b : K)⁻¹ = q := by
    change ((q : K) * (b : K)) * (b : K)⁻¹ = q
    group
  have hu := U.mul_mem (hforced a ha) (U.inv_mem (hforced b hb))
  have he : (f a * c) * (f b * c)⁻¹ = f q := by
    calc
      _ = f a * (f b)⁻¹ := by group
      _ = f ((a : K) * (b : K)⁻¹) := by rw [map_mul, map_inv]
      _ = f q := by rw [hab]
  exact he ▸ hu


/-- The intrinsic model implication needed after strong closure has supplied
Sylow stability, omega fixation and square-one displacements. -/
@[expose] def SquareDisplacementInner (K : Type*) [Group K] : Prop :=
  ∀ (P : Sylow 2 K) (a : MulAut K), a ^ 2 = 1 →
    (∀ x ∈ P, a x ∈ P) →
    (∀ x ∈ omegaOneAmbient (P : Subgroup K), a x = x) →
    (∀ x ∈ P, (a x * x⁻¹) ^ 2 = 1) →
    (∃ t ∈ P, t ≠ 1 ∧ t ^ 2 = 1) → ∃ g, a = MulAut.conj g

/-- The criterion is transported through an actual group equivalence. -/
theorem SquareDisplacementInner.of_mulEquiv [Finite K]
    (e : K ≃* D) (hD : SquareDisplacementInner D) : SquareDisplacementInner K := by
  intro P a ha hs hf hd ⟨t, htP, htn, ht2⟩
  let R := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let b := MulAut.congr e a
  have he (x : K) : b (e x) = e (a x) := by simp [b, MulAut.congr_apply]
  have hb : b ^ 2 = 1 := by
    change (MulAut.congr e a) ^ 2 = 1
    rw [← map_pow, ha, map_one]
  have hRs : ∀ x ∈ R, b x ∈ R := by
    rintro _ ⟨x, hx, rfl⟩
    change b (e x) ∈ R
    rw [he]
    exact mem_map_of_mem e.toMonoidHom (hs x hx)
  have hRf : ∀ x ∈ omegaOneAmbient (R : Subgroup D), b x = x := by
    intro x hx
    have hm : omegaOneAmbient (R : Subgroup D) =
        (omegaOneAmbient (P : Subgroup K)).map e.toMonoidHom :=
      (map_omegaOneAmbient_injective e.toMonoidHom e.injective _).symm
    rw [hm] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    change b (e y) = e y
    rw [he, hf y hy]
  have hRd : ∀ x ∈ R, (b x * x⁻¹) ^ 2 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    change (b (e x) * (e x)⁻¹) ^ 2 = 1
    rw [he, ← map_inv, ← map_mul, ← map_pow, hd x hx, map_one]
  obtain ⟨g, hg⟩ := hD R b hb hRs hRf hRd
    ⟨e t, mem_map_of_mem e.toMonoidHom htP,
      (fun h => htn (e.injective (h.trans (map_one e).symm))), by rw [← map_pow, ht2, map_one]⟩
  refine ⟨e.symm g, ?_⟩
  ext x
  apply e.injective
  have hh := congrArg (fun α : MulAut D => α (e x)) hg
  simpa only [he, MulAut.conj_apply, map_mul, map_inv, e.apply_symm_apply] using hh

/-- A square-one inner action stabilizing the actual Sylow is implemented by
an element of its first omega, when the component has trivial center. -/
theorem inner_implementer_mem_omega (hc : center K = ⊥) (P : Sylow 2 K)
    (a : MulAut K) (ha : a ^ 2 = 1) (hs : ∀ x ∈ P, a x ∈ P)
    (hi : ∃ g, a = MulAut.conj g) :
    ∃ g ∈ omegaOneAmbient (P : Subgroup K), a = MulAut.conj g := by
  obtain ⟨g, rfl⟩ := hi
  have hg2 : g ^ 2 = 1 := MulAut.conj_injective_of_center_eq_bot hc (by
    simpa only [map_pow, map_one] using ha)
  have hgN : g ∈ normalizer (P : Set K) := by
    change ∀ x : K, x ∈ (P : Subgroup K) ↔ g * x * g⁻¹ ∈ (P : Subgroup K)
    intro x
    constructor
    · exact hs x
    · intro hx
      have hh := hs (g * x * g⁻¹) hx
      have he : g * (g * x * g⁻¹) * g⁻¹ = x := by
        calc
          _ = g ^ 2 * x * (g ^ 2)⁻¹ := by simp only [pow_two, mul_inv_rev, mul_assoc]
          _ = x := by rw [hg2]; simp
      exact he ▸ hh
  have hp := (IsElementaryAbelian.zpowers_of_pow_eq_one (p := 2) hg2).isPGroup 2 _
  have hgP : g ∈ P := by
    have hh : g ∈ zpowers g ⊓ normalizer (P : Set K) := ⟨mem_zpowers g, hgN⟩
    rw [hp.inf_normalizer_sylow P] at hh
    exact hh.2
  exact ⟨g, (omegaOneAmbient_le_iff _ _).mp le_rfl g hgP hg2, rfl⟩

/-- The action of an elementary strongly closed U on a normalized component
has the exact Sylow stability, omega fixation and displacement properties. -/
theorem omega_action_inputs (S U L : Subgroup G) [IsElementaryAbelian 2 U]
    (hU : IsStronglyClosedSet (U : Set G) S ⊤)
    (hUL : U ≤ normalizer (L : Set G))
    (P : Subgroup L) (hP : P = S.subgroupOf L)
    (hQU : (omegaOneAmbient P).map L.subtype ≤ U) (u : U) :
    let a := L.normalizerMonoidHom ⟨u, hUL u.property⟩
    a ^ 2 = 1 ∧ (∀ x ∈ P, a x ∈ P) ∧
      (∀ x ∈ omegaOneAmbient P, a x = x) ∧
      (∀ x ∈ P, (a x * x⁻¹) ^ 2 = 1) := by
  let ρ : U →* MulAut L := L.normalizerMonoidHom.comp (inclusion hUL)
  change ρ u ^ 2 = 1 ∧ _
  have hu2 : u ^ 2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) (u : G) u.property)
  refine ⟨by rw [← map_pow, hu2, map_one], ?_, ?_, ?_⟩
  · intro x hx
    rw [hP] at hx ⊢
    change (u : G) * (x : G) * (u : G)⁻¹ ∈ S
    exact S.mul_mem (S.mul_mem (hU.1 u.property) hx) (S.inv_mem (hU.1 u.property))
  · intro x hx
    apply Subtype.ext
    have hxU : (x : G) ∈ U := hQU (mem_map_of_mem L.subtype hx)
    have hc := congrArg Subtype.val (mul_comm u (⟨x, hxU⟩ : U))
    change (u : G) * (x : G) = (x : G) * (u : G) at hc
    change (u : G) * (x : G) * (u : G)⁻¹ = (x : G)
    rw [hc]
    simp only [mul_assoc, mul_inv_cancel, mul_one]
  · intro x hx
    have hxS : (x : G) ∈ S := by
      change x ∈ S.subgroupOf L
      rw [← hP]
      exact hx
    have hconj : (x : G) * (u : G)⁻¹ * (x : G)⁻¹ ∈ U := by
      have hh := hU.2 (u : G)⁻¹ (U.inv_mem u.property) (x : G)⁻¹ (mem_top _)
        (by simpa only [inv_inv] using
          S.mul_mem (S.mul_mem hxS (S.inv_mem (hU.1 u.property))) (S.inv_mem hxS))
      change (x : G) * (u : G)⁻¹ * (x : G)⁻¹ ∈ (U : Set G)
      simpa only [inv_inv] using hh
    have hdU : (u : G) * (x : G) * (u : G)⁻¹ * (x : G)⁻¹ ∈ U := by
      simpa only [mul_assoc] using U.mul_mem u.property hconj
    exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian _ hdU)

end Theory.GroupTheory.MarkedInnerStrongClosure
