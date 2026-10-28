module

public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SylowPointwiseInner
public import Theory.GroupTheory.SubgroupCenterImageBound
public import Theory.SpecificGroups.SymplecticFour.BorelActionGeometry.TorusInvariant

/-!
# The pointwise Sylow and Borel fixers in nonbinary Sp₄

The semilinear coverage premise and the actual Sylow pointwise-fixer theorem
put every fixing automorphism in the inner image of the Sylow center. Its
order is q², by the two-root coordinates and Sylow conjugacy. If the whole
Borel is fixed, the inner actor is fixed by its diagonal torus, hence is the
identity. Conjugacy gives this assertion for every Sylow normalizer.

Semilinear coverage remains an explicit independent premise. No local
normalizer classification or chapter alternative is assumed.

Source: Aschbacher–Smith, E.6.8(2), printed pp.247–248 (PDF pp.258–259),
and the automorphism input of 16.1.6, printed p.1172.
-/

public section

open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.BorelActionGeometry
open CentralRootGeometry DiagramAutomorphisms
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem sylow_fixer_range_le_center {A : Type*} [Group A]
    {n : ℕ} (hcard : Nat.card F = 2 ^ n) (hn : 1 < n)
    (hclass : ∀ a : MulAut (Sp F), PreservesDiagram a →
      ∃ g : Sp F, ∃ σ : F ≃+* F, a = MulAut.conj g * fieldAutomorphism σ)
    (P : Sylow 2 (Sp F)) (ρ : A →* MulAut (Sp F))
    (hfix : ∀ a : A, ∀ x ∈ (P : Subgroup (Sp F)), ρ a x = x) :
    ρ.range ≤ ((center P).map (P : Subgroup (Sp F)).subtype).map MulAut.conj := by
  rintro _ ⟨a, rfl⟩
  obtain ⟨g, hg, he⟩ := aut_fixing_sylow_inner hcard hn hclass P (ρ a) (hfix a)
  refine ⟨g, ⟨⟨g,hg⟩, mem_center_iff.mpr ?_, rfl⟩, he.symm⟩
  intro x
  apply Subtype.ext
  have hh := hfix a x x.property
  rw [he] at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

theorem card_sylow_center {n : ℕ} (hcard : Nat.card F = 2 ^ n)
    (hn : 0 < n) (P : Sylow 2 (Sp F)) : Nat.card (center P) = Nat.card F ^ 2 := by
  let S := unipotentSylow hcard hn
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Sp F) S P
  have hm : (S : Subgroup (Sp F)).map (MulAut.conj g).toMonoidHom = P :=
    congrArg (fun R : Sylow 2 (Sp F) => (R : Subgroup (Sp F))) hg
  have he := map_subgroup_center_eq (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
    (S : Subgroup (Sp F))
  rw [hm] at he
  have hc := congrArg (fun H : Subgroup (Sp F) => Nat.card H) he
  rw [card_map_of_injective (MulAut.conj g).injective,
    card_map_of_injective (S : Subgroup (Sp F)).subtype_injective,
    card_map_of_injective (P : Subgroup (Sp F)).subtype_injective] at hc
  rw [← hc]
  change Nat.card (center (unipotent (F := F))) = _
  rw [← Nat.card_congr (centerEquiv (F := F)).toEquiv, Nat.card_prod,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative F ≃ F), pow_two]

theorem sylow_fixer_card_le {A : Type*} [Group A]
    {n : ℕ} (hcard : Nat.card F = 2 ^ n) (hn : 1 < n)
    (hclass : ∀ a : MulAut (Sp F), PreservesDiagram a →
      ∃ g : Sp F, ∃ σ : F ≃+* F, a = MulAut.conj g * fieldAutomorphism σ)
    (P : Sylow 2 (Sp F)) (ρ : A →* MulAut (Sp F))
    (hfix : ∀ a : A, ∀ x ∈ (P : Subgroup (Sp F)), ρ a x = x) :
    Nat.card ρ.range ≤ 2 ^ (2 * n) := by
  have hle := card_le_of_le (sylow_fixer_range_le_center hcard hn hclass P ρ hfix)
  have hmap := Nat.card_le_card_of_surjective
    (MulAut.conj.subgroupMap ((center P).map (P : Subgroup (Sp F)).subtype))
    (MulAut.conj.subgroupMap_surjective _)
  have hh := hle.trans hmap
  rw [card_map_of_injective (P : Subgroup (Sp F)).subtype_injective,
    card_sylow_center hcard (by omega) P, hcard] at hh
  simpa only [← pow_mul, Nat.mul_comm n 2] using hh

theorem aut_fixing_borel_eq_one
    {n : ℕ} (hcard : Nat.card F = 2 ^ n) (hn : 1 < n)
    (hclass : ∀ a : MulAut (Sp F), PreservesDiagram a →
      ∃ g : Sp F, ∃ σ : F ≃+* F, a = MulAut.conj g * fieldAutomorphism σ)
    (a : MulAut (Sp F)) (hfix : ∀ x ∈ borel (F := F), a x = x) : a = 1 := by
  have hU : ∀ x ∈ unipotent (F := F), a x = x :=
    fun x hx => hfix x (unipotent_le_borel hx)
  obtain ⟨g, hg, he⟩ := aut_fixing_unipotent_inner hcard hn hclass a hU
  have hgc : g ∈ (parameter (F := F)).range := by
    rw [parameter_range]
    refine ⟨⟨g,hg⟩, mem_center_iff.mpr ?_, rfl⟩
    intro x
    apply Subtype.ext
    have hh := hU x x.property
    rw [he] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hgt : g ∈ centralizer ((diagonalTorusHom (F := F)).range : Set (Sp F)) := by
    rintro x ⟨c, rfl⟩
    have hh := hfix (diagonalTorusHom c) (diagonalTorus_mem_borel c.1 c.2)
    rw [he] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hlarge : 2 < Nat.card F := by
    rw [hcard]
    exact (by decide : 2 = 2 ^ 1) ▸ Nat.pow_lt_pow_right (by decide) hn
  have hg1 : g = 1 := mem_bot.mp (centralPlane_torus_fixed_eq_bot hlarge ▸ ⟨hgc,hgt⟩)
  rw [he, hg1, map_one]

theorem aut_fixing_sylow_normalizer_eq_one
    {n : ℕ} (hcard : Nat.card F = 2 ^ n) (hn : 1 < n)
    (hclass : ∀ a : MulAut (Sp F), PreservesDiagram a →
      ∃ g : Sp F, ∃ σ : F ≃+* F, a = MulAut.conj g * fieldAutomorphism σ)
    (P : Sylow 2 (Sp F)) (a : MulAut (Sp F))
    (hfix : ∀ x ∈ normalizer (P : Set (Sp F)), a x = x) : a = 1 := by
  let S := unipotentSylow hcard (show 0 < n by omega)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Sp F) S P
  let e := MulAut.conj g
  have hm : (unipotent (F := F)).map e.toMonoidHom = P :=
    congrArg (fun R : Sylow 2 (Sp F) => (R : Subgroup (Sp F))) hg
  have hB : (borel (F := F)).map e.toMonoidHom = normalizer (P : Set (Sp F)) := by
    rw [borel_eq_normalizer_unipotent, map_normalizer_eq_of_bijective _ e.bijective, hm]
    rfl
  have hb : ∀ x ∈ borel (F := F), (e⁻¹ * a * e) x = x := by
    intro x hx
    change e.symm (a (e x)) = x
    rw [hfix (e x) (hB ▸ mem_map_of_mem e.toMonoidHom hx), e.symm_apply_apply]
  have he := aut_fixing_borel_eq_one hcard hn hclass (e⁻¹ * a * e) hb
  apply MulEquiv.ext
  intro x
  have hh := congrArg (fun c : MulAut (Sp F) => e (c (e.symm x))) he
  simpa using hh

end Theory.SpecificGroups.SymplecticFour.BorelActionGeometry
