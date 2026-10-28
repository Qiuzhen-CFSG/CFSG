module

public import Theory.GroupTheory.CyclicSubgroupNormalizer
public import Theory.GroupTheory.CoprimeNormalizerAutomorphisms
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.PGroupCore

/-!
# Cyclic Hall normalizer escape

This module packages the elementary normalizer argument used for a full cyclic
Cartan in a finite Borel.  A normal subgroup supplement controls the Cartan
index; if a prime does not divide that index, Sylow conjugacy places every
`p`-subgroup of the Borel inside the Cartan.  A Weyl element normalizing the
Cartan and lying outside the Borel then escapes the normalizer of the original
subgroup.  The final lemmas transport this escape through a coprime quotient,
and in particular through a quotient with a 2-group kernel for odd primes.

The source use is the full quadratic-field torus in the unitary minimal
parabolic (Aschbacher--Smith 4.4.13(1)); the matrix-specific torus and Weyl
calculation are proved in the corresponding `SpecificGroups.SU3` module.
-/

open Subgroup

namespace Theory.GroupTheory

variable {G H : Type*} [Group G] [Finite G] [Group H]

/-- The index of a supplement to a normal subgroup divides the order of the
normal subgroup. -/
public theorem index_dvd_of_normal_supplement (U T : Subgroup G) [U.Normal]
    (hgen : U ⊔ T = ⊤) : T.index ∣ Nat.card U := by
  have h := card_mul_eq_card_inf_mul_card_sup_of_normalizes U T le_normalizer_of_normal
  rw [hgen, card_top, ← T.card_mul_index] at h
  have he : Nat.card U = Nat.card (U ⊓ T : Subgroup G) * T.index := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := T))
    calc
      Nat.card U * Nat.card T = Nat.card (U ⊓ T : Subgroup G) *
          (Nat.card T * T.index) := h
      _ = (Nat.card (U ⊓ T : Subgroup G) * T.index) * Nat.card T := by ac_rfl
  rw [he]
  exact dvd_mul_left _ _

/-- A `p`-subgroup can be conjugated into a subgroup whose index is not
divisible by `p`. -/
public theorem exists_conj_le_of_prime_not_dvd_index {p : ℕ} [Fact p.Prime]
    (T A : Subgroup G) (hindex : ¬ p ∣ T.index) (hA : IsPGroup p A) :
    ∃ g : G, A.map (MulAut.conj g).toMonoidHom ≤ T := by
  let P : Sylow p T := default
  have hP : ¬ p ∣ ((P : Subgroup T).map T.subtype).index := by
    rw [index_map_subtype]
    exact fun h => ((Fact.out : p.Prime).dvd_mul.mp h).elim P.not_dvd_index hindex
  let Q := (P.isPGroup'.map T.subtype).toSylow hP
  obtain ⟨R, hR⟩ := hA.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G R Q
  refine ⟨g, le_trans ?_ (map_subtype_le (P : Subgroup T))⟩
  change A.map (MulAut.conj g).toMonoidHom ≤ (Q : Subgroup G)
  rw [← hg]
  exact map_mono hR

/-- A normalizer element for a cyclic Cartan outside the Borel implies
normalizer escape for every `p`-subgroup of the Borel, when `p` does not
divide the Cartan index. -/
public theorem normalizer_not_le_of_cyclic_torus
    (B T A : Subgroup G) [IsCyclic T]
    (_hTB : T ≤ B) {p : ℕ} [Fact p.Prime]
    (hindex : ¬ p ∣ (T.subgroupOf B).index)
    (hA : IsPGroup p A) (hAB : A ≤ B)
    (w : G) (hw : w ∈ normalizer (T : Set G)) (hout : w ∉ B) :
    ¬ normalizer (A : Set G) ≤ B := by
  obtain ⟨g, hg⟩ := exists_conj_le_of_prime_not_dvd_index
    (T.subgroupOf B) (A.subgroupOf B) hindex hA.comap_subtype
  have hconj : A.map (MulAut.conj (g : G)).toMonoidHom ≤ T := by
    rintro _ ⟨a, ha, rfl⟩
    exact hg ⟨⟨a, hAB ha⟩, ha, rfl⟩
  have hwA : w ∈ normalizer (A.map (MulAut.conj (g : G)).toMonoidHom : Set G) :=
    normalizer_le_normalizer_of_le_cyclic _ T hconj hw
  intro hN
  apply hout
  have hnConj : normalizer (A.map (MulAut.conj (g : G)).toMonoidHom : Set G) ≤ B := by
    rw [← map_equiv_normalizer_eq]
    rintro _ ⟨x, hx, rfl⟩
    exact B.mul_mem (B.mul_mem g.property (hN hx)) (B.inv_mem g.property)
  exact hnConj hwA

/-- Escape lifts through a quotient whose kernel is coprime to the prime. -/
public theorem normalizer_not_le_of_coprime_image
    (q : G →* H) (hq : Function.Surjective q)
    (M A : Subgroup G) {p : ℕ} [Fact p.Prime] (hA : IsPGroup p A)
    (hcop : Nat.Coprime p (Nat.card q.ker))
    (hout : ¬ normalizer (A.map q : Set H) ≤ M.map q) :
    ¬ normalizer (A : Set G) ≤ M := by
  let : Fact (IsPGroup p A) := ⟨hA⟩
  intro hN
  apply hout
  rw [normalizer_map_eq_of_coprime_kernel p A q hq hcop]
  exact map_mono hN

/-- Escape lifts through a quotient with a 2-group kernel for an odd
primary subgroup. -/
public theorem normalizer_not_le_of_two_kernel
    (q : G →* H) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (M A : Subgroup G) {p : ℕ} [Fact p.Prime] (hp : Odd p) (hA : IsPGroup p A)
    (hout : ¬ normalizer (A.map q : Set H) ≤ M.map q) :
    ¬ normalizer (A : Set G) ≤ M := by
  obtain ⟨n, hn⟩ := hk.exists_card_eq
  exact normalizer_not_le_of_coprime_image q hq M A hA
    (by rw [hn]; exact hp.coprime_two_right.pow_right n) hout

end Theory.GroupTheory
