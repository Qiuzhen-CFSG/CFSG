module

public import Theory.GroupTheory.PGroup.AbelianOmega
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# The Sylow-center divisor from involution fusion

For a finite group with one conjugacy class of involutions, Burnside fusion
makes the Sylow normalizer transitive on the nonidentity elements of
Ω₁(Z(S)). If Z(S) is noncyclic, this elementary abelian subgroup has order
2ʳ with r > 1. Orbit–stabilizer gives 2ʳ−1 ∣ |N(S)|.

The proof uses the intrinsic Ω₁(Z(S)), its inclusion into S and then the
actual inclusion S → G. Conjugation is the canonical action of N_G(S) on S.
This is the argument for (3G) following GLS, Volume 4, Chapter 1, Lemma 3.10
(`refs/KGroup/GLS4/Chapter1.tex`, lines 456–462).
-/

open Subgroup MulAction
open scoped IsMulCommutative

namespace Sylow

/-- The first omega subgroup of a noncyclic Sylow center supplies a
nontrivial Mersenne divisor of the literal Sylow normalizer. -/
public theorem exists_omega_center_card_and_normalizer_divisor {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hZ : ¬ IsCyclic (center S))
    (hfusion : ∀ z w : G, orderOf z = 2 → orderOf w = 2 → IsConj z w) :
    ∃ r : ℕ, 1 < r ∧ Nat.card (omega₁ (center S) (p := 2)) = 2 ^ r ∧
      2 ^ r ≤ Nat.card S ∧
      2 ^ r - 1 ∣ Nat.card (normalizer (S : Set G)) := by
  classical
  let Z := omega₁ (center S) (p := 2)
  let i : Z →* S := (center S).subtype.comp Z.subtype
  have hi : Function.Injective i :=
    (center S).subtype_injective.comp Z.subtype_injective
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.omega₁_of_isMulCommutative _
  have hpZ : IsPGroup 2 Z := (S.isPGroup'.to_subgroup (center S)).to_subgroup Z
  obtain ⟨r, hr⟩ := hpZ.exists_card_eq
  have hr1 : 1 < r := by
    by_contra! h
    apply hZ
    apply (S.isPGroup'.to_subgroup (center S)).isCyclic_of_card_omega_one_le_two
    change Nat.card Z ≤ 2
    rw [hr]
    exact (Nat.pow_le_pow_right (by decide : 1 ≤ 2) h).trans (by decide)
  have hrS : 2 ^ r ≤ Nat.card S := by
    rw [← hr]
    exact Nat.card_le_card_of_injective i hi
  have hZcard : 1 < Nat.card Z := by
    rw [hr]
    exact Nat.one_lt_pow (by omega) (by decide)
  let : Nontrivial Z := Finite.one_lt_card_iff_nontrivial.mp hZcard
  obtain ⟨z, hz⟩ := exists_ne (1 : Z)
  let N := normalizer ((S : Subgroup G) : Set G)
  let : MulDistribMulAction N S := inferInstanceAs
    (MulDistribMulAction (normalizer ((S : Subgroup G) : Set G)) (S : Subgroup G))
  have hcentral (x : Z) : i x ∈ center S := x.val.property
  have hsq (x : Z) : (i x) ^ 2 = 1 := by
    have hx : x ^ 2 = 1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 Z) x
    rw [← map_pow, hx, map_one]
  have hne (x : Z) (hx : x ≠ 1) : i x ≠ 1 := by
    intro he
    exact hx (hi (he.trans i.map_one.symm))
  have horbit (x : Z) (hx : x ≠ 1) : i x ∈ orbit N (i z) := by
    have hord (y : Z) (hy : y ≠ 1) : orderOf ((i y : S) : G) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact orderOf_eq_prime (hsq y) (hne y hy)
    obtain ⟨g, hg⟩ := isConj_iff.mp (hfusion (i z) (i x) (hord z hz) (hord x hx))
    have hc (y : Z) : ((i y : S) : G) ∈ centralizer (S : Set G) := by
      intro a ha
      exact congrArg Subtype.val (mem_center_iff.mp (hcentral y) (⟨a, ha⟩ : S))
    obtain ⟨n, hn, he⟩ := S.conj_eq_normalizer_conj_of_mem_centralizer
      (i z) g⁻¹ (hc z) (by simpa only [inv_inv, hg] using hc x)
    apply mem_orbit_iff.mpr
    refine ⟨(⟨n, hn⟩ : N)⁻¹, Subtype.ext ?_⟩
    change n⁻¹ * ((i z : S) : G) * (n⁻¹)⁻¹ = ((i x : S) : G)
    simpa only [inv_inv, hg] using he.symm
  have hback (y : orbit N (i z)) : ∃ x : Z, x ≠ 1 ∧ i x = y.val := by
    obtain ⟨a, ha⟩ := mem_orbit_iff.mp y.property
    let f := (S : Subgroup G).normalizerMonoidHom a
    have hf : f (i z) = y.val := ha
    have hyc : y.val ∈ center S := by
      rw [← hf]
      have he := characteristic_iff_map_eq.mp (inferInstance : (center S).Characteristic) f
      have hm := mem_map_of_mem f.toMonoidHom (hcentral z)
      simpa only [he, MulEquiv.coe_toMonoidHom] using hm
    have hyp : y.val ^ 2 = 1 := by rw [← hf, ← map_pow, hsq z, map_one]
    have hyn : y.val ≠ 1 := by
      rw [← hf]
      exact fun h => hne z hz (f.injective (h.trans f.map_one.symm))
    let yc : center S := ⟨y.val, hyc⟩
    have hyZ : yc ∈ Z := Subgroup.subset_closure (by
      change yc ^ (2 ^ 1) = 1
      apply Subtype.ext
      change y.val ^ (2 ^ 1) = 1
      simpa only [pow_one] using hyp)
    refine ⟨⟨yc, hyZ⟩, ?_, rfl⟩
    intro h
    exact hyn (congrArg i h)
  let e : {x : Z // x ≠ 1} ≃ orbit N (i z) :=
    Equiv.ofBijective (fun x => ⟨i x.val, horbit x.val x.property⟩)
      ⟨fun x y h => Subtype.ext (hi (congrArg (fun t : orbit N (i z) => t.val) h)), fun y => by
        obtain ⟨x, hx, he⟩ := hback y
        exact ⟨⟨x, hx⟩, Subtype.ext he⟩⟩
  have hc : Nat.card (orbit N (i z)) = 2 ^ r - 1 := by
    rw [← Nat.card_congr e]
    let : Fintype Z := Fintype.ofFinite Z
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    simp only [Fintype.card_unique, ← Nat.card_eq_fintype_card, hr]
  refine ⟨r, hr1, hr, hrS, ?_⟩
  rw [← hc, Nat.card_congr (orbitEquivQuotientStabilizer N (i z)), ← Subgroup.index_eq_card]
  exact Subgroup.index_dvd_card _

end Sylow
