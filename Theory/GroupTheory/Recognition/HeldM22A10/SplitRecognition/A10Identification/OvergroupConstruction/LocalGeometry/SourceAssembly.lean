module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.Relations
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SourceContracts
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.ModelInvolutions
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.Crossing
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group

/-!
# Held's marked generators from the corrected source geometry

The corrected six-point data and its seven-point extension give the eight
Dickson generators of Held 5.11. Their crossing centralizer excludes an
order-six adjacent product, and their marked word is the original central
involution. The proof uses the actual source geometry, including the
`tau_lam_mem` membership; it does not pass through the inconsistent older
six-point interface.

This module preserves the older assembly and provides the source version
used by the A10 identification assembly. The algebraic relations need
only the common action and centralizer fields of the two interfaces.

Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), pp.238--239, Lemma 5.11,
DOI 10.1215/ijm/1256053756.
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.Source

variable {G : Type*} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)
  (L : SixLocalData D e) (K : SevenLocalData D e L)

local notation "π" => pi D e
local notation "μ" => mu D e
local notation "μ'" => mu' D e
local notation "ℓ" => lam D e
local notation "ξ" => xi D e

private theorem cube_mul_of_cycling {r a b : G} (hr : r ^ 3 = 1)
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (hra : r⁻¹ * a * r = b) (hrb : r⁻¹ * b * r = a * b) : (r * a) ^ 3 = 1 := by
  have har : a * r = r * b := by
    calc
      a * r = r * (r⁻¹ * a * r) := by group
      _ = r * b := by rw [hra]
  have hbr : b * r = r * (a * b) := by
    calc
      b * r = r * (r⁻¹ * b * r) := by group
      _ = r * (a * b) := by rw [hrb]
  calc
    (r * a) ^ 3 = r * (a * r) * (a * r) * a := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = r * (r * b) * (r * b) * a := by rw [har]
    _ = r * r * (b * r) * b * a := by group
    _ = r * r * (r * (a * b)) * b * a := by rw [hbr]
    _ = r ^ 3 * a * b ^ 2 * a := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = 1 := by rw [hr, hb, one_mul, mul_one, ← pow_two, ha]

public theorem root_cube : (L.u * L.v) ^ 3 = 1 := by
  rw [L.u_v_commute.mul_pow, ← L.u_order, pow_orderOf_eq_one,
    L.u_order, ← L.v_order, pow_orderOf_eq_one, mul_one]

public theorem root_mu_cube : (L.u * L.v * μ) ^ 3 = 1 := by
  apply cube_mul_of_cycling (root_cube D e L)
    (element_square D e 1 (by decide)) (element_square D e 6 (by decide))
  · calc
      (L.u * L.v)⁻¹ * μ * (L.u * L.v) = L.v⁻¹ * (L.u⁻¹ * μ * L.u) * L.v := by group
      _ = L.v⁻¹ * ℓ * L.v := by rw [L.mu_u]
      _ = ℓ := by rw [L.v_lam_commute.inv_left.eq]; group
  · calc
      (L.u * L.v)⁻¹ * ℓ * (L.u * L.v) = L.v⁻¹ * (L.u⁻¹ * ℓ * L.u) * L.v := by group
      _ = L.v⁻¹ * (μ * ℓ) * L.v := by rw [L.lam_u]
      _ = μ * ℓ := by rw [(L.v_mu_commute.mul_right L.v_lam_commute).inv_left.eq]; group

public theorem mu_commute_of_fix_six (p : Perm (Fin 7)) (hp : p 6 = 6) :
    Commute μ (K.embedding p) := by
  have hm : K.embedding p ∈ L.A ⊔ zpowers μ' := by
    rw [← K.six_range]
    exact ⟨p, hp, rfl⟩
  have hs : L.A ⊔ zpowers μ' ≤ centralizer ({μ} : Set G) := by
    apply sup_le
    · intro a ha
      apply mem_centralizer_singleton_iff.mpr
      exact (mem_centralizer_iff.mp (L.A_centralizes ha) μ (by simp)).symm
    · apply zpowers_le.mpr
      exact mem_centralizer_singleton_iff.mpr (mu_commute_mu' D e).symm.eq
  exact (mem_centralizer_singleton_iff.mp (hs hm)).symm

private def sixCycle : Perm (Fin 7) :=
  swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4 * swap 4 5

public theorem mu_not_commute_sigma
    (hcentralizer : Nat.card (centralizer ({D.a10NoncentralInvolution e} : Set G)) = 2880) :
    ¬ Commute μ (K.embedding (swap 0 6)) := by
  intro h
  have hc : Commute μ (K.embedding (swap 0 6 * sixCycle)) := by
    rw [map_mul]
    exact h.mul_right (mu_commute_of_fix_six D e L K sixCycle (by decide +kernel))
  have ho : orderOf (K.embedding (swap 0 6 * sixCycle)) = 7 := by
    rw [orderOf_injective K.embedding K.injective]
    let : Fact (Nat.Prime 7) := ⟨by decide⟩
    apply orderOf_eq_prime
    · decide +kernel
    · decide +kernel
  have hd := (centralizer ({μ} : Set G)).orderOf_dvd_natCard
    (mem_centralizer_singleton_iff.mpr hc.symm.eq)
  rw [ho, mu_eq, hcentralizer] at hd
  norm_num at hd

private theorem embedding_mem_crossing (p : Perm (Fin 7))
    (h1 : Commute p (swap 1 2)) (h2 : Commute p (swap 2 3))
    (h3 : Commute p (swap 4 5)) : K.embedding p ∈ crossingCentralizer D e L := by
  apply mem_centralizer_iff.mpr
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl | rfl
  · rw [← K.mark_v_mu']
    exact (h1.map K.embedding).symm.eq
  · rw [← K.mark_pi_mu_mu']
    exact (h2.map K.embedding).symm.eq
  · rw [← K.mark_xi]
    exact (h3.map K.embedding).symm.eq

public theorem mu_sigma_cube
    (hcentralizer : Nat.card (centralizer ({D.a10NoncentralInvolution e} : Set G)) = 2880) :
    (μ * K.embedding (swap 0 6)) ^ 3 = 1 := by
  let X := crossingCentralizer D e L
  have hmu : μ ∈ X := by
    apply mem_centralizer_iff.mpr
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · rw [← K.mark_v_mu']
      exact (mu_commute_of_fix_six D e L K (swap 1 2) (by decide)).symm.eq
    · rw [← K.mark_pi_mu_mu']
      exact (mu_commute_of_fix_six D e L K (swap 2 3) (by decide)).symm.eq
    · rw [← K.mark_xi]
      exact (mu_commute_of_fix_six D e L K (swap 4 5) (by decide)).symm.eq
  have hsigma : K.embedding (swap 0 6) ∈ X := by
    apply embedding_mem_crossing D e L K <;> (change _ * _ = _ * _; decide +kernel)
  have hxi : ξ ∈ X := by
    rw [← K.mark_xi]
    apply embedding_mem_crossing D e L K <;> (change _ * _ = _ * _; decide +kernel)
  have hxi_center : ∀ g : X, Commute (⟨ξ, hxi⟩ : X) g := by
    intro g
    exact Subtype.ext (mem_centralizer_iff.mp g.property ξ (by simp))
  have hxi_ne : (⟨ξ, hxi⟩ : X) ≠ 1 := by
    intro h
    exact element_ne_one D e 7 (congrArg Subtype.val h)
  have hsquare : K.embedding (swap 0 6) ^ 2 = 1 := by
    rw [← map_pow, show (swap (0 : Fin 7) 6) ^ 2 = 1 by decide +kernel, map_one]
  have hn : ¬ Commute (⟨μ, hmu⟩ : X) ⟨K.embedding (swap 0 6), hsigma⟩ := by
    intro h
    exact mu_not_commute_sigma D e L K hcentralizer (congrArg Subtype.val h.eq)
  rcases cube_eq_one_or_central K.crossingEquiv
    (a := ⟨μ, hmu⟩) (b := ⟨K.embedding (swap 0 6), hsigma⟩)
    (Subtype.ext (element_square D e 1 (by decide))) (Subtype.ext hsquare)
    hn hxi_center hxi_ne with h | h
  · exact congrArg Subtype.val h
  · have hcube : (μ * K.embedding (swap 0 6)) ^ 3 = ξ := congrArg Subtype.val h
    have hdelta : Commute (μ * K.embedding (swap 0 6)) (K.embedding (swap 3 4)) := by
      apply Commute.mul_left
      · exact mu_commute_of_fix_six D e L K (swap 3 4) (by decide)
      · exact (show Commute (swap (0 : Fin 7) 6) (swap 3 4) by
          change _ * _ = _ * _; decide +kernel).map K.embedding
    have hxd : Commute ξ (K.embedding (swap 3 4)) := by
      rw [← hcube]
      exact hdelta.pow_left 3
    have heq : K.embedding (swap 3 4) = ξ := by
      apply involutions_eq_of_commute_of_product_cube
      · rw [← map_pow, show (swap (3 : Fin 7) 4) ^ 2 = 1 by decide +kernel, map_one]
      · exact element_square D e 7 (by decide)
      · exact hxd.symm
      · rw [← K.mark_xi, ← map_mul, ← map_pow,
          show (swap (3 : Fin 7) 4 * swap 4 5) ^ 3 = 1 by decide +kernel, map_one]
    rw [← K.mark_xi] at heq
    have hfalse := K.injective heq
    have : swap (3 : Fin 7) 4 ≠ swap 4 5 := by decide +kernel
    exact (this hfalse).elim

public theorem mu_sigma_order
    (hcentralizer : Nat.card (centralizer ({D.a10NoncentralInvolution e} : Set G)) = 2880) :
    orderOf (μ * K.embedding (swap 0 6)) = 3 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  apply orderOf_eq_prime
  · exact mu_sigma_cube D e L K hcentralizer
  · intro h
    have hs : K.embedding (swap 0 6) = μ⁻¹ := eq_inv_of_mul_eq_one_right h
    apply mu_not_commute_sigma D e L K hcentralizer
    rw [hs]
    exact (Commute.refl μ).inv_right

private def tailPermutation : Fin 6 → Perm (Fin 7) :=
  ![swap 0 6, swap 0 1, swap 1 2, swap 2 3, swap 3 4, swap 4 5]

private theorem square_of_inverts {r a : G} (ha : a ^ 2 = 1)
    (hra : a * r * a⁻¹ = r⁻¹) : (r * a) ^ 2 = 1 := by
  calc
    (r * a) ^ 2 = r * (a * r * a⁻¹) * a ^ 2 := by
      simp only [pow_two]
      group
    _ = 1 := by rw [hra, ha, mul_inv_cancel, mul_one]

include L K in
public theorem exists_marked_of_local_geometry [Finite G]
    (hcentralizer : Nat.card (centralizer ({D.a10NoncentralInvolution e} : Set G)) = 2880) :
    ∃ M : Fin 8 → G, DicksonRelations M ∧ M 1 * M 3 * M 5 = D.z := by
  let T := tailPermutation
  let M : Fin 8 → G := Fin.cases (L.u * L.v) (Fin.cases μ (K.embedding ∘ T))
  have hs : ∀ i, K.embedding (T i) ^ 2 = 1 := by
    intro i
    rw [← map_pow, show (T i) ^ 2 = 1 from
      (show ∀ i, tailPermutation i ^ 2 = 1 by decide +kernel) i, map_one]
  have hadj : ∀ i : Fin 5,
      (K.embedding (T i.castSucc) * K.embedding (T i.succ)) ^ 3 = 1 := by
    intro i
    rw [← map_mul, ← map_pow, show (T i.castSucc * T i.succ) ^ 3 = 1 from
      (show ∀ i : Fin 5, (tailPermutation i.castSucc * tailPermutation i.succ) ^ 3 = 1
        by decide +kernel) i, map_one]
  have hfar : ∀ i j : Fin 6, i.val + 1 < j.val →
      (K.embedding (T i) * K.embedding (T j)) ^ 2 = 1 := by
    intro i j h
    rw [← map_mul, ← map_pow, show (T i * T j) ^ 2 = 1 from
      (show ∀ i j : Fin 6, i.val + 1 < j.val →
        (tailPermutation i * tailPermutation j) ^ 2 = 1 by decide +kernel) i j h, map_one]
  have hroot : ∀ i, (L.u * L.v * K.embedding (T i)) ^ 2 = 1 := by
    intro i
    apply square_of_inverts (hs i)
    have h := K.root_action (T i)
    rw [if_neg ((show ∀ i, Equiv.Perm.sign (tailPermutation i) ≠ 1
      by decide +kernel) i)] at h
    exact h
  have hmu : ∀ i : Fin 6, i ≠ 0 → Commute μ (K.embedding (T i)) := by
    intro i hi
    apply mu_commute_of_fix_six D e L K
    exact (show ∀ i : Fin 6, i ≠ 0 → tailPermutation i 6 = 6 by decide +kernel) i hi
  refine ⟨M, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact root_cube D e L
  · intro i
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i _ => ?_) i) i
    · exact fun h => (h rfl).elim
    · exact fun _ => element_square D e 1 (by decide)
    · exact hs i
  · intro i
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i
    · exact root_mu_cube D e L
    · exact mu_sigma_cube D e L K hcentralizer
    · exact hadj i
  · intro i
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i
    · intro j
      refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j _ => ?_) j) j
      · intro h; omega
      · intro h; simp only [Fin.val_succ, Fin.val_zero] at h; omega
      · exact hroot j
    · intro j
      refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j h => ?_) j) j
      · intro h; simp only [Fin.val_succ, Fin.val_zero] at h; omega
      · intro h; simp only [Fin.val_succ, Fin.val_zero] at h; omega
      · have hj : j ≠ 0 := by intro hj; subst hj; simp at h
        change (μ * K.embedding (T j)) ^ 2 = 1
        rw [(hmu j hj).mul_pow, element_square D e 1 (by decide), hs j, mul_one]
    · intro j
      refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j h => ?_) j) j
      · intro h; simp only [Fin.val_succ, Fin.val_zero] at h; omega
      · intro h; simp only [Fin.val_succ, Fin.val_zero] at h; omega
      · exact hfar i j (by simpa using h)
  · change μ * K.embedding (swap 0 1) * K.embedding (swap 2 3) = D.z
    rw [K.mark_mu', K.mark_pi_mu_mu']
    have hc := (commute_pi D e 1).mul_right (commute_pi D e 2)
    calc
      μ * μ' * (π * μ * μ') = (μ * μ') * (π * (μ * μ')) := by group
      _ = π * (μ * μ') ^ 2 := by rw [← mul_assoc, hc.symm.eq, pow_two, mul_assoc]
      _ = π := by rw [(mu_commute_mu' D e).mul_pow,
          element_square D e 1 (by decide), element_square D e 2 (by decide), mul_one, mul_one]
      _ = D.z := pi_eq D e

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.Source
