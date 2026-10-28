module

public import CFSG.Quasithin.Chapter16.Section04To05.Basic

/-!
# Choice of the relative Sylow subgroup in Δ₀

The definition of Δ₀ uses one Sylow subgroup of N_J(K). Since N_G(K) =
N_G(L) normalizes KL, Sylow conjugacy inside N_J(K) shows that its omega
condition holds for every choice of this Sylow subgroup. Failure of the
condition produces an actual involution outside KL.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, definition
preceding 16.4.9, printed pp.1188–1189. These lemmas do not assert the
order-two bound or nonemptiness proved in 16.4.9.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.Intersections

open Subgroup

variable {G : Type*} [Group G]

/-- The order assertion in 16.4.9(1), stated for every relative Sylow choice.
This predicate is an interface for that assertion, not a proof of it. -/
def OrderTwoOutsideDeltaZero (L : Subgroup G) : Prop :=
  ∀ J ∈ delta L, J ∉ deltaZero L → ∀ R : Subgroup G,
    SylowIn R (J ⊓ normalizer (centralizer (L : Set G) : Set G)) → Nat.card R = 2

/-- Relative Sylow subgroups are conjugate by an element of their overgroup. -/
theorem SylowIn.exists_conjugator [Finite G] {R S H : Subgroup G}
    (hR : SylowIn R H) (hS : SylowIn S H) :
    ∃ x ∈ H, R.conjBy x = S := by
  obtain ⟨P, rfl⟩ := hR
  obtain ⟨Q, rfl⟩ := hS
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq H P Q
  refine ⟨x, x.property, ?_⟩
  rw [← hx]
  change ((P : Subgroup H).map H.subtype).map (MulAut.conj (x : G)).toMonoidHom =
    ((P : Subgroup H).map (MulAut.conj x).toMonoidHom).map H.subtype
  rw [map_map, map_map]
  rfl

private theorem omega_conj_le {R D : Subgroup G} {x : G}
    (hx : x ∈ normalizer (D : Set G))
    (hR : omegaOneAmbient R ≤ D) : omegaOneAmbient (R.conjBy x) ≤ D := by
  apply (omegaOneAmbient_le_iff _ _).mpr
  rintro y ⟨a, ha, rfl⟩ hy
  have ha2 : a ^ 2 = 1 := (MulAut.conj x).injective (by simpa using hy)
  exact (mem_normalizer_iff.mp hx a).mp
    ((omegaOneAmbient_le_iff R D).mp hR a ha ha2)

/-- An omega containment in a normalized subgroup is independent of the
relative Sylow subgroup chosen. -/
theorem SylowIn.omega_le_iff_of_normalized [Finite G] {R S H D : Subgroup G}
    (hR : SylowIn R H) (hS : SylowIn S H)
    (hHD : H ≤ normalizer (D : Set G)) :
    omegaOneAmbient R ≤ D ↔ omegaOneAmbient S ≤ D := by
  constructor
  · intro h
    obtain ⟨x, hx, heq⟩ := hR.exists_conjugator hS
    rw [← heq]
    exact omega_conj_le (hHD hx) h
  · intro h
    obtain ⟨x, hx, heq⟩ := hS.exists_conjugator hR
    rw [← heq]
    exact omega_conj_le (hHD hx) h

/-- The common normalizer of K and L normalizes their product KL. -/
theorem normalizer_le_componentProduct_normalizer {L : Subgroup G}
    (hn : normalizer (centralizer (L : Set G) : Set G) = normalizer (L : Set G)) :
    normalizer (centralizer (L : Set G) : Set G) ≤
      normalizer ((centralizer (L : Set G) ⊔ L : Subgroup G) : Set G) := by
  intro x hx
  exact normalizer_inf_normalizer_le_normalizer_sup _ _ ⟨hx, hn ▸ hx⟩

/-- The source definition of Δ₀ may be tested with any relative Sylow subgroup. -/
theorem mem_deltaZero_iff_of_sylow [Finite G] {L J R : Subgroup G}
    (hn : normalizer (centralizer (L : Set G) : Set G) = normalizer (L : Set G))
    (hR : SylowIn R (J ⊓ normalizer (centralizer (L : Set G) : Set G))) :
    J ∈ deltaZero L ↔ J ∈ delta L ∧
      omegaOneAmbient R ≤ centralizer (L : Set G) ⊔ L := by
  constructor
  · rintro ⟨hJ, S, hS, hSinner⟩
    exact ⟨hJ, (hS.omega_le_iff_of_normalized hR
      (inf_le_right.trans (normalizer_le_componentProduct_normalizer hn))).mp hSinner⟩
  · rintro ⟨hJ, hinner⟩
    exact ⟨hJ, R, hR, hinner⟩

/-- The outer involution chosen in the first paragraph of the proof of 16.4.9. -/
theorem exists_outer_involution_of_not_mem_deltaZero {L J R : Subgroup G}
    (hJ : J ∈ delta L) (hnot : J ∉ deltaZero L)
    (hR : SylowIn R (J ⊓ normalizer (centralizer (L : Set G) : Set G))) :
    ∃ r ∈ R, orderOf r = 2 ∧ r ∉ centralizer (L : Set G) ⊔ L := by
  have hno : ¬ omegaOneAmbient R ≤ centralizer (L : Set G) ⊔ L :=
    fun hi => hnot ⟨hJ, R, hR, hi⟩
  rw [omegaOneAmbient_le_iff] at hno
  push Not at hno
  obtain ⟨r, hr, hr2, hout⟩ := hno
  refine ⟨r, hr, orderOf_eq_prime_iff.mpr ⟨hr2, ?_⟩, hout⟩
  intro he
  exact hout (he ▸ (centralizer (L : Set G) ⊔ L).one_mem)

end CFSG.Quasithin.Chapter16.Intersections
