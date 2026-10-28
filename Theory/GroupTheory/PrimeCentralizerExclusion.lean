module
public import Theory.GroupTheory.NormalPrimeOrder
public import Theory.GroupTheory.PerfectSubgroupAutomorphismFixer
public import Theory.GroupTheory.InnerImageGeometry

/-!
# Prime-order centralizer exclusions when the prime occurs once

If p divides the order of H but p² does not divide the ambient order,
a centralizing element of order p belongs to H by normality inside its
join with H. It then lies in Z(H). A prime-core bound on this center,
with a different prime, excludes the element. For a perfect H and a
centerless ambient group this also excludes inner automorphisms of order
p centralizing the actual inner image of H.

Source application: Aschbacher–Smith, elimination of original 4.3.16(3),
printed p.618; the J₁ application is NonblockEndgameSieveExclusionsJanko.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory
variable {J : Type*} [Group J] [Finite J] {p q : ℕ} [Fact p.Prime]

/-- A prime occurring only once cannot appear in this subgroup centralizer. -/
theorem orderOf_ne_prime_of_centralizes_of_square_not_dvd
    (H : Subgroup J) (hd : p ∣ Nat.card H) (hsq : ¬ p ^ 2 ∣ Nat.card J)
    (hz : center H ≤ pCore q H) (hpq : q.Coprime p)
    (g : J) (hc : g ∈ centralizer (H : Set J)) : orderOf g ≠ p := by
  intro hg
  let A := H ⊔ zpowers g
  have hN : A ≤ normalizer (H : Set J) := sup_le H.le_normalizer
    ((zpowers_le.mpr hc).trans (centralizer_le_normalizer _))
  let H' := H.subgroupOf A
  let : H'.Normal := normal_subgroupOf_of_le_normalizer hN
  have hd' : p ∣ Nat.card H' := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe (show H ≤ A from le_sup_left)).toEquiv]
  let g' : A := ⟨g,mem_sup_right (mem_zpowers g)⟩
  have hin : g' ∈ H' := mem_normal_of_prime_order_of_square_not_dvd H' hd' g'
    (by simpa only [g', Subgroup.orderOf_mk] using hg)
    (fun h => hsq (h.trans A.card_subgroup_dvd_card))
  have hgH : g ∈ H := hin
  have hgZ : (⟨g,hgH⟩ : H) ∈ center H := by
    apply mem_center_iff.mpr
    intro x
    exact Subtype.ext (hc x x.property)
  have ho := (pCore_isPGroup (p := q) (G := H)).orderOf_coprime hpq ⟨⟨g,hgH⟩,hz hgZ⟩
  have he : orderOf (⟨⟨g,hgH⟩,hz hgZ⟩ : pCore q H) = orderOf g := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
  rw [he,hg,Nat.coprime_self] at ho
  exact (Fact.out : p.Prime).ne_one ho

/-- The same exclusion holds for actual inner automorphisms centralizing a perfect image. -/
theorem inner_automorphism_orderOf_ne_prime_of_square_not_dvd
    (H : Subgroup J) [Group.IsPerfect H]
    (hd : p ∣ Nat.card H) (hsq : ¬ p ^ 2 ∣ Nat.card J)
    (hz : center H ≤ pCore q H) (hpq : q.Coprime p) (hJ : center J = ⊥)
    (a : MulAut J) (ha : a ∈ centralizer (H.map MulAut.conj : Set (MulAut J)))
    (hi : ∃ g : J, MulAut.conj g = a) : orderOf a ≠ p := by
  obtain ⟨g,rfl⟩ := hi
  have hi : Function.Injective (MulAut.conj : J →* MulAut J) := by
    rw [← MonoidHom.ker_eq_bot_iff, DoubleCoverCentralizer.conj_kernel, hJ]
  rw [orderOf_injective _ hi]
  apply orderOf_ne_prime_of_centralizes_of_square_not_dvd H hd hsq hz hpq g
  rw [PerfectSubgroupAutomorphismFixer.inner_centralizer_eq_fixer] at ha
  have hf := (mem_fixingSubgroup_iff _).mp ha
  intro x hx
  exact (mul_inv_eq_iff_eq_mul.mp (hf x hx)).symm
end Theory.GroupTheory
