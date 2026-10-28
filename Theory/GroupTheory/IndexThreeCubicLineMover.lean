module

public import Theory.GroupTheory.PrimeSubgroupInvolution
public import Theory.GroupTheory.CyclicThreeNormalizer
public import Theory.GroupTheory.SubgroupConjugateIncidence
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.IndexNormal

/-!
# Moving a cubic line out of an involution fixed plane

Suppose K fixes U and preserves V, with U∨B=X=C_V(z) and |B|=3.
If N_K(X) fixes B and has index three, and z is the square of an
exponent-four element of K, then a K-conjugate F of B is inverted by z.
Indeed, the degree-three coset action kills z, so z normalizes every
conjugate of B.  A conjugate outside X exists because K does not fix X.
The prime-order involution dichotomy then gives inversion and [F,z]=F.
All conjugates are literal images under the original inner automorphisms.

Source: Aschbacher, *Sporadic Groups* (1994),45.8,printed p.246.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Squares of elements of exponent four lie in every index-three core. -/
theorem square_mem_normalCore_of_index_three (H : Subgroup G) (hH : H.index = 3)
    (r : G) (hr : r ^ 4 = 1) : r ^ 2 ∈ H.normalCore := by
  have hd : H.normalCore.index ∣ 6 := by
    have hh : H.normalCore.index ∣ H.index.factorial := by
      rw [normalCore_eq_ker, index_ker, index_eq_card, ←Nat.card_perm]
      exact card_subgroup_dvd_card _
    simpa [hH,Nat.factorial] using hh
  let q := QuotientGroup.mk' H.normalCore
  have hd6 : orderOf (q r) ∣ 6 := (_root_.orderOf_dvd_natCard (q r)).trans hd
  have hd4 : orderOf (q r) ∣ 4 := orderOf_dvd_of_pow_eq_one (by rw [←map_pow,hr,map_one])
  have hd2 : orderOf (q r) ∣ 2 := by simpa using Nat.dvd_gcd hd4 hd6
  apply (QuotientGroup.eq_one_iff _).mp
  change q (r^2) = 1
  rw [map_pow]
  exact orderOf_dvd_iff_pow_eq_one.mp hd2

theorem exists_inverted_cubic_conjugate_of_normal_core
    (K V X U B : Subgroup G) (z : G) (hz : z ^ 2 = 1)
    (hB : Nat.card B = 3) (hBV : B ≤ V) (hjoin : U ⊔ B = X)
    (hKU : K ≤ normalizer (U : Set G)) (hKV : K ≤ normalizer (V : Set G))
    (hfixed : V ⊓ centralizer ({z} : Set G) = X)
    (hNB : K ⊓ normalizer (X : Set G) ≤ normalizer (B : Set G))
    (hzK : z ∈ K)
    (hzcore : (⟨z,hzK⟩ : K) ∈ ((normalizer (X : Set G)).subgroupOf K).normalCore)
    (hmoves : ¬ K ≤ normalizer (X : Set G)) :
    ∃ g ∈ K, let F := B.map (MulAut.conj g).toMonoidHom
      F ≤ V ∧ Nat.card F = 3 ∧ ¬ F ≤ X ∧
        (∀ x ∈ F, z * x * z⁻¹ = x⁻¹) ∧ ⁅F, zpowers z⁆ = F := by
  obtain ⟨g,hg,hgX⟩ := SetLike.not_le_iff_exists.mp hmoves
  let F := B.map (MulAut.conj g).toMonoidHom
  have hFV : F ≤ V := by
    have hv := map_mono (f := (MulAut.conj g).toMonoidHom) hBV
    have he : V.map (MulAut.conj g).toMonoidHom = V := mem_normalizer_iff_map_conj_eq.mp (hKV hg)
    rwa [he] at hv
  have hFc : Nat.card F = 3 := by rw [card_map_of_injective (MulAut.conj g).injective,hB]
  have hFX : ¬ F ≤ X := by
    intro hh
    have hle : X.map (MulAut.conj g).toMonoidHom ≤ X := by
      have he : U.map (MulAut.conj g).toMonoidHom = U := mem_normalizer_iff_map_conj_eq.mp (hKU hg)
      rw [←hjoin, map_sup, he]
      exact sup_le le_sup_left (hh.trans (by rw [hjoin]))
    exact hgX (mem_normalizer_iff_map_conj_eq.mpr (eq_of_le_of_card_ge hle
      (by rw [card_map_of_injective (MulAut.conj g).injective])))
  have hn : z ∈ normalizer (F : Set G) := by
    have hh := hzcore (⟨g⁻¹,K.inv_mem hg⟩ : K)
    have hpre : g⁻¹*z*g ∈ K ⊓ normalizer (X : Set G) := by
      constructor
      · exact K.mul_mem (K.mul_mem (K.inv_mem hg) hzK) hg
      · change g⁻¹*z*g ∈ normalizer (X : Set G)
        change g⁻¹*z*(g⁻¹)⁻¹ ∈ normalizer (X : Set G) at hh
        rw [inv_inv] at hh
        exact hh
    have hBnorm := hNB hpre
    rw [←map_equiv_normalizer_eq (f := MulAut.conj g) B]
    refine ⟨g⁻¹*z*g,hBnorm,?_⟩
    change g * (g⁻¹*z*g) * g⁻¹ = z
    group
  have hinv : ∀ x ∈ F, z*x*z⁻¹=x⁻¹ := by
    rcases centralizes_or_inverts_prime_subgroup_of_sq_eq_one F
      (hFc ▸ Nat.prime_three) z hz hn with hc | hi
    · exfalso
      apply hFX
      rw [←hfixed]
      exact le_inf hFV (fun x hx => mem_centralizer_singleton_iff.mpr (hc x hx).symm.eq)
    · exact hi
  have hcomm_le : ⁅F,zpowers z⁆ ≤ F :=
    le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr hn)
  have hcomm_ne : ⁅F,zpowers z⁆ ≠ ⊥ := by
    intro he
    have hc := commutator_eq_bot_iff_le_centralizer.mp he
    apply hFX
    rw [←hfixed]
    refine le_inf hFV (hc.trans ?_)
    exact centralizer_le (Set.singleton_subset_iff.mpr (mem_zpowers z))
  have hc3 : Nat.card (⁅F,zpowers z⁆ : Subgroup G) = 3 := by
    have hd : Nat.card (⁅F,zpowers z⁆ : Subgroup G) ∣ 3 := hFc ▸ card_dvd_of_le hcomm_le
    exact ((Nat.dvd_prime Nat.prime_three).mp hd).resolve_left
      (fun he => hcomm_ne ((eq_bot_iff_card _).mpr he))
  exact ⟨g,hg,hFV,hFc,hFX,hinv,eq_of_le_of_card_ge hcomm_le (by rw [hc3,hFc])⟩
/-- The index-three form of the cubic-line mover uses the original rotation
whose square is the marked involution. -/
theorem exists_inverted_cubic_conjugate_of_index_three
    (K V X U B : Subgroup G) (z r : G) (hrK : r ∈ K)
    (hr : r ^ 4 = 1) (hrz : r ^ 2 = z)
    (hB : Nat.card B = 3) (hBV : B ≤ V) (hjoin : U ⊔ B = X)
    (hKU : K ≤ normalizer (U : Set G)) (hKV : K ≤ normalizer (V : Set G))
    (hfixed : V ⊓ centralizer ({z} : Set G) = X)
    (hNB : K ⊓ normalizer (X : Set G) ≤ normalizer (B : Set G))
    (hindex : (normalizer (X : Set G)).relIndex K = 3) :
    ∃ g ∈ K, let F := B.map (MulAut.conj g).toMonoidHom
      F ≤ V ∧ Nat.card F = 3 ∧ ¬ F ≤ X ∧
        (∀ x ∈ F, z * x * z⁻¹ = x⁻¹) ∧ ⁅F, zpowers z⁆ = F := by
  have hz : z ^ 2 = 1 := by rw [←hrz,←pow_mul]; exact hr
  have hzK : z ∈ K := hrz ▸ K.pow_mem hrK 2
  have hc := square_mem_normalCore_of_index_three
    ((normalizer (X : Set G)).subgroupOf K) hindex
    (⟨r,hrK⟩ : K) (Subtype.ext hr)
  have hzc : (⟨z,hzK⟩ : K) ∈ ((normalizer (X : Set G)).subgroupOf K).normalCore := by
    have he : (⟨r,hrK⟩ : K)^2 = ⟨z,hzK⟩ := Subtype.ext hrz
    exact he ▸ hc
  have hmoves : ¬K ≤ normalizer (X : Set G) := by
    intro hh
    have h1 := relIndex_eq_one.mpr hh
    omega
  exact exists_inverted_cubic_conjugate_of_normal_core K V X U B z hz hB hBV
    hjoin hKU hKV hfixed hNB hzK hzc hmoves

end Subgroup
