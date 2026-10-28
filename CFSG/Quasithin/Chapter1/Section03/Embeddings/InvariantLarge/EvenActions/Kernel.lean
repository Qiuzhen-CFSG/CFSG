module

public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# The inner kernel of a Cartan normalizer action

If B normalizes U, the commutator of an element of N_U(B) with B belongs
to both U and B. Disjointness makes this commutator trivial. If B lies in
an abelian Cartan H, a product uh normalizing B therefore centralizes B.
This supplies the inner-action kernel after a concrete Borel decomposition;
it does not assume that an arbitrary inner automorphism centralizes B.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, proof of Proposition 1.3.4, printed p.511, and the
Cartan configuration of Lemma A.3.15(5), printed p.50.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions

/-- In the raw field–Cartan product, an inner-diagonal subgroup lies in the
Cartan when the field and inner-diagonal groups are disjoint. The product
factorization and disjointness must be established in the actual model. -/
theorem le_cartan_of_field_inner_disjoint {G : Type*} [Group G]
    (B F H I : Subgroup G) (hBI : B ≤ I) (hHI : H ≤ I)
    (hFI : Disjoint F I)
    (hprod : ∀ b ∈ B, ∃ f ∈ F, ∃ h ∈ H, b = f * h) : B ≤ H := by
  intro b hb
  obtain ⟨f, hf, h, hh, he⟩ := hprod b hb
  have hfI : f ∈ I := by
    have hm := I.mul_mem (hBI hb) (I.inv_mem (hHI hh))
    rw [he] at hm
    simpa only [mul_inv_cancel_right] using hm
  have hf1 : f = 1 := hFI.le_bot ⟨hf, hfI⟩
  simpa only [he, hf1, one_mul] using hh

/-- A unipotent element normalizing a disjoint subgroup that normalizes the
unipotent group centralizes that subgroup. -/
theorem unipotent_centralizes {G : Type*} [Group G] (U B : Subgroup G)
    (hdis : Disjoint U B) (hn : B ≤ normalizer U) {u : G}
    (hu : u ∈ U) (hub : u ∈ normalizer B) : u ∈ centralizer (B : Set G) := by
  apply mem_centralizer_iff.mpr
  intro b hb
  have hU : u * b * u⁻¹ * b⁻¹ ∈ U := by
    simpa only [mul_assoc] using U.mul_mem hu
      ((mem_normalizer_iff.mp (hn hb) u⁻¹).mp (U.inv_mem hu))
  have hB : u * b * u⁻¹ * b⁻¹ ∈ B :=
    B.mul_mem ((mem_normalizer_iff.mp hub b).mp hb) (B.inv_mem hb)
  have he : u * b * u⁻¹ = b := mul_inv_eq_one.mp (hdis.le_bot ⟨hU, hB⟩)
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- The unipotent and toral factors both centralize an odd Cartan subgroup
whenever their product normalizes it. -/
theorem borel_centralizes {G : Type*} [Group G] (U H B : Subgroup G)
    [IsMulCommutative H] (hdis : Disjoint U H) (hn : H ≤ normalizer U)
    (hBH : B ≤ H) {u h : G} (hu : u ∈ U) (hh : h ∈ H)
    (huh : u * h ∈ normalizer B) : u * h ∈ centralizer (B : Set G) := by
  have hc : h ∈ centralizer (B : Set G) := by
    apply mem_centralizer_iff.mpr
    intro b hb
    exact congrArg Subtype.val (mul_comm (⟨b, hBH hb⟩ : H) ⟨h, hh⟩)
  have hun : u ∈ normalizer B := by
    have hhB : h ∈ normalizer (B : Set G) := centralizer_le_normalizer _ hc
    simpa using (normalizer (B : Set G)).mul_mem huh
      ((normalizer (B : Set G)).inv_mem hhB)
  exact (centralizer _).mul_mem
    (unipotent_centralizes U B (hdis.mono_right hBH) (hBH.trans hn) hu hun) hc

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions
