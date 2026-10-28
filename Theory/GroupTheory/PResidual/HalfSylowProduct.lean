module
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Mathlib.GroupTheory.IndexNormal

/-!
# Two-perfect subgroups in half-Sylow products

A product J = NRQ with N,R ≤ X and Q ≤ T puts X∩J at index dividing two
when [T:R]=2. Every two-perfect subgroup of J lies in this intersection,
since a subgroup of index two is normal with two-group quotient.
The literal set product is retained, and finiteness is unnecessary.

Source application: Aschbacher--Smith14.6.9, printed p.1026.
-/

public section
namespace Subgroup
open scoped Pointwise
variable {G : Type*} [Group G]

private theorem twoPerfect_le_of_index_dvd_two
    (L A : Subgroup G) (hL : IsPPerfect 2 L) (hA : A.index ∣ 2) : L ≤ A := by
  rcases (Nat.dvd_prime Nat.prime_two).mp hA with hone | htwo
  · rw [index_eq_one.mp hone]
    exact le_top
  · let : A.Normal := A.normal_of_index_eq_two htwo
    have hQ : IsPGroup 2 (G ⧸ A) := IsPGroup.of_card (n := 1) (by
      simpa only [← index_eq_card,pow_one] using htwo)
    exact (le_pResidual_of_isPPerfect L hL).trans (sInf_le ⟨inferInstance,hQ⟩)

/-- A two-perfect subgroup lies in X whenever the displayed product has
a right factor in T and X contains a subgroup of index two in T. -/
theorem twoPerfect_le_of_halfSylow_product
    (L T R N Q X : Subgroup G) (hL : IsPPerfect 2 L)
    (hR : R.relIndex T = 2) (hQT : Q ≤ T) (hNX : N ≤ X) (hRX : R ≤ X)
    (hfac : ((L ⊔ T : Subgroup G) : Set G) = (N : Set G) * R * Q) : L ≤ X := by
  let J := L ⊔ T
  let A := X.subgroupOf J
  obtain ⟨a,ha,htwo⟩ := (relIndex_dvd_two_iff (H := R) (K := T)).mp (dvd_of_eq hR)
  have hd : A.index ∣ 2 := index_dvd_two_iff.mpr ⟨⟨a,(show T ≤ J from le_sup_right) ha⟩,?_⟩
  · have hLp : IsPPerfect 2 (L.subgroupOf J) := hL.of_surjective
      (subgroupOfEquivOfLe (show L ≤ J from le_sup_left)).symm.toMonoidHom
      (subgroupOfEquivOfLe (show L ≤ J from le_sup_left)).symm.surjective
    have hh := twoPerfect_le_of_index_dvd_two (L.subgroupOf J) A hLp hd
    intro l hl
    exact hh (show (⟨l,(show L ≤ J from le_sup_left) hl⟩ : J) ∈ L.subgroupOf J from hl)
  · intro x
    have hx : (x : G) ∈ (N : Set G) * R * Q := hfac ▸ x.property
    obtain ⟨nr,⟨n,hn,r,hr,rfl⟩,q,hq,he⟩ := hx
    rcases htwo q (hQT hq) with hqa | hqR
    · apply Or.inl
      change (x : G) * a ∈ X
      rw [←he,mul_assoc]
      exact X.mul_mem (X.mul_mem (hNX hn) (hRX hr)) (hRX hqa)
    · exact Or.inr (show (x : G) ∈ X from he ▸
        X.mul_mem (X.mul_mem (hNX hn) (hRX hr)) (hRX hqR))

end Subgroup
