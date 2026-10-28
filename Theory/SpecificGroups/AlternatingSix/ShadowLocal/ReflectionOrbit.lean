module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.SylowGeometry
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry

/-!
# Reflection orbits compatible with four-group normalizers in A₆

A four-group has index two in the inner Sylow D₈, so that D₈ normalizes it.
The proved outer complement of its A₆ normalizer therefore centralizes D₈.
The full Aut(A₆) centralizer of D₈ lies in the specified Sylow subgroup:
its central involution already has a Sylow centralizer. Finally the two
outer elements of this centralizer are conjugate by the marked rotation.
Transporting that conjugation gives an actual element of the specified
Sylow subgroup that makes the reflection fix the entire A₆ normalizer.

The result is a scalar statement about actual automorphisms, with no
chapter records or assumed orbit identities. An involution hypothesis on
the outer element is unnecessary, since the centralizer calculation forces it.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, printed pp.569–570, the choice of the conjugate
reflection in the terminal A₆ argument.
-/

public section

open Subgroup
namespace AlternatingSix.ShadowLocal
open Identification

private theorem inner_image (P : Sylow 2 AutA6) :
    (sylowInner P).map (P : Subgroup AutA6).subtype = (P : Subgroup AutA6) ⊓ inner := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.property, hy⟩
  · intro hx
    exact ⟨⟨x, hx.1⟩, hx.2, rfl⟩

/-- The full automorphism centralizer of the inner Sylow intersection is
already contained in the specified Sylow subgroup. -/
theorem inner_centralizer_le_sylow (P : Sylow 2 AutA6) :
    centralizer (((P : Subgroup AutA6) ⊓ inner : Subgroup AutA6) : Set AutA6) ≤
      (P : Subgroup AutA6) := by
  let z : P := sylowEquiv P (Holomorph.rotation ^ 4)
  have hzD : z ∈ sylowInner P := by
    rw [← sylowEquiv_innerD P, mem_map_equiv]
    simp only [z, MulEquiv.symm_apply_apply]
    rw [show 4 = 2 * 2 from rfl, pow_mul]
    exact Subgroup.pow_mem _ (subset_closure (by simp)) _
  have hzZ : z ∈ center P := by
    rw [SylowGeometry.center_eq]
    exact mem_zpowers _
  have hzorder : orderOf (z : AutA6) = 2 := by
    rw [Subgroup.orderOf_coe]
    change orderOf (sylowEquiv P (Holomorph.rotation ^ 4)) = 2
    rw [(sylowEquiv P).orderOf_eq]
    apply orderOf_eq_prime
    · decide +kernel
    · decide +kernel
  obtain ⟨Q, hQ⟩ := inner_involution_centralizer_sylow z hzorder hzD
  have hPQ : (P : Subgroup AutA6) ≤ (Q : Subgroup AutA6) := by
    rw [hQ]
    intro x hx
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (mem_center_iff.mp hzZ (⟨x, hx⟩ : P))
  have heq : (P : Subgroup AutA6) = (Q : Subgroup AutA6) :=
    (P.is_maximal' Q.isPGroup' hPQ).symm
  intro x hx
  rw [heq, hQ, mem_centralizer_singleton_iff]
  exact (hx z ⟨z.property, hzD⟩).symm

set_option synthInstance.maxSize 1024 in
private theorem model_outer_centralizer_orbit (u v : Holomorph.Model)
    (hu : u ∈ centralizer (Holomorph.innerD : Set Holomorph.Model))
    (huD : u ∉ Holomorph.innerD)
    (hv : v ∈ centralizer (Holomorph.innerD : Set Holomorph.Model))
    (hvD : v ∉ Holomorph.innerD) :
    ∃ a : Holomorph.Model, a⁻¹ * u * a = v := by
  rw [Holomorph.centralizer_innerD, Holomorph.mem_centralTwo_sup_transposition] at hu hv
  rw [Holomorph.mem_innerD] at huD hvD
  have table : ∀ u v : Holomorph.Model,
      (∃ i, Holomorph.centralTranspositionEmbedding i = u) →
      (¬ ∃ i, Holomorph.innerEmbedding i = u) →
      (∃ i, Holomorph.centralTranspositionEmbedding i = v) →
      (¬ ∃ i, Holomorph.innerEmbedding i = v) →
      u = v ∨ Holomorph.rotation⁻¹ * u * Holomorph.rotation = v := by
    decide +kernel
  rcases table u v hu huD hv hvD with h | h
  · exact ⟨1, by simpa using h⟩
  · exact ⟨Holomorph.rotation, h⟩

private theorem map_model_centralizer (P : Sylow 2 AutA6) :
    (centralizer (Holomorph.innerD : Set Holomorph.Model)).map (sylowEquiv P).toMonoidHom =
      centralizer (sylowInner P : Set P) := by
  rw [Holomorph.centralizer_innerD, Subgroup.map_sup, SylowGeometry.centralizer_inner,
    Holomorph.centralTwo, MonoidHom.map_zpowers, SylowGeometry.center_eq]
  simp only [MulEquiv.coe_toMonoidHom]
  rfl

/-- Any outer element centralizing the inner Sylow intersection can be
conjugated within P to fix the entire A₆ normalizer of a specified four-group.
This is the scalar reflection-orbit identity used on printed p.570. -/
theorem four_normalizer_reflection_orbit (P : Sylow 2 AutA6)
    (F : Subgroup A6) [IsKleinFour F]
    (hFD : F.map (MulAut.conj : A6 →* AutA6) ≤ (P : Subgroup AutA6) ⊓ inner)
    (b : AutA6) (hbP : b ∈ (P : Subgroup AutA6))
    (hbC : b ∈ centralizer (((P : Subgroup AutA6) ⊓ inner : Subgroup AutA6) : Set AutA6))
    (hbD : b ∉ (P : Subgroup AutA6) ⊓ inner) :
    ∃ a ∈ (P : Subgroup AutA6),
      ∀ k ∈ normalizer (F : Set A6), (a⁻¹ * b * a) k = k := by
  let D : Subgroup AutA6 := (P : Subgroup AutA6) ⊓ inner
  let E := F.map (MulAut.conj : A6 →* AutA6)
  have hDcard : Nat.card D = 8 := by
    dsimp only [D]
    rw [← inner_image P, card_map_of_injective (P : Subgroup AutA6).subtype_injective,
      sylowInner_card]
  have hEcard : Nat.card E = 4 := by
    rw [card_map_of_injective inner_injective, IsKleinFour.card_four]
  have hindex : (E.subgroupOf D).index = 2 := by
    have h := (E.subgroupOf D).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hFD).toEquiv, hEcard, hDcard] at h
    omega
  have hDN : D ≤ normalizer (E : Set AutA6) :=
    (normal_subgroupOf_iff_le_normalizer hFD).mp (normal_of_index_eq_two hindex)
  obtain ⟨τ, _, hτouter, hfix, _, _⟩ := FourNormalizers.exists_outer_complement F
  have hτC : τ ∈ centralizer (D : Set AutA6) := by
    intro d hd
    obtain ⟨k, rfl⟩ := hd.2
    have hk : k ∈ normalizer (F : Set A6) :=
      mem_normalizer_iff_map_conj_eq.mpr ((FourNormalizers.mem_inner_normalizer_iff F _).mp
        (hDN hd))
    have h := aut_conj_inner τ k
    rw [hfix k hk, mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  have hτP : τ ∈ (P : Subgroup AutA6) := inner_centralizer_le_sylow P hτC
  let e := sylowEquiv P
  let u := e.symm ⟨b, hbP⟩
  let v := e.symm ⟨τ, hτP⟩
  have hu : u ∈ centralizer (Holomorph.innerD : Set Holomorph.Model) := by
    have h : (⟨b, hbP⟩ : P) ∈ centralizer (sylowInner P : Set P) := by
      intro d hd
      exact Subtype.ext (hbC d ⟨d.property, hd⟩)
    rwa [← map_model_centralizer P, mem_map_equiv] at h
  have hv : v ∈ centralizer (Holomorph.innerD : Set Holomorph.Model) := by
    have h : (⟨τ, hτP⟩ : P) ∈ centralizer (sylowInner P : Set P) := by
      intro d hd
      exact Subtype.ext (hτC d ⟨d.property, hd⟩)
    rwa [← map_model_centralizer P, mem_map_equiv] at h
  have huD : u ∉ Holomorph.innerD := by
    intro h
    have hm : (⟨b, hbP⟩ : P) ∈ sylowInner P := by
      rwa [← sylowEquiv_innerD P, mem_map_equiv]
    exact hbD ⟨hbP, hm⟩
  have hvD : v ∉ Holomorph.innerD := by
    intro h
    have hm : (⟨τ, hτP⟩ : P) ∈ sylowInner P := by
      rwa [← sylowEquiv_innerD P, mem_map_equiv]
    exact hτouter hm
  obtain ⟨a, ha⟩ := model_outer_centralizer_orbit u v hu huD hv hvD
  refine ⟨e a, (e a).property, ?_⟩
  have heq : (e a : AutA6)⁻¹ * b * (e a : AutA6) = τ := by
    have h := congrArg e ha
    simp only [map_mul, map_inv, u, v, e.apply_symm_apply] at h
    exact congrArg Subtype.val h
  intro k hk
  rw [heq]
  exact hfix k hk

end AlternatingSix.ShadowLocal
