module

public import Theory.GroupTheory.ConjugateSpanOrder
public import Theory.GroupTheory.Commutator.SimpleSubnormal
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.IndexNormal

/-!
# Sylow conjugate spans and commutator generation

A subgroup with one or two conjugates has a normal span under a Sylow
2-subgroup. In the two-conjugate case its normalizer has index two, and
the odd Sylow index makes the Sylow subgroup supplement that normalizer.
Normality of the normalizer then propagates to the conjugate span.

We also identify spans with joins of conjugates, transport them through
homomorphisms, and propagate [K,A] = K to the T-span when A is normalized
by T. These facts supply the orbit step following 13.6.13 in
Aschbacher–Smith, combined manuscript of 1 March 2004, printed p.929.
They do not assert the existence of a suitable component.
-/

@[expose] public section
open Subgroup
namespace Subgroup
variable {G H : Type*} [Group G] [Group H]

/-- The closure and join definitions of a conjugate span agree. -/
theorem conjugateSpanBy_eq_iSup_conj (K T : Subgroup G) :
    conjugateSpanBy K T = ⨆ t : T, K.map (MulAut.conj (t : G)).toMonoidHom := by
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro x ⟨t, ht, k, hk, rfl⟩
    exact (le_iSup (fun t : T => K.map (MulAut.conj (t : G)).toMonoidHom)
      ⟨t, ht⟩) (mem_map_of_mem _ hk)
  · apply iSup_le
    rintro ⟨t, ht⟩ x ⟨k, hk, rfl⟩
    exact subset_closure ⟨t, ht, k, hk, rfl⟩

/-- Homomorphisms preserve the actual conjugate span. -/
theorem map_conjugateSpanBy (K T : Subgroup G) (f : G →* H) :
    (conjugateSpanBy K T).map f = conjugateSpanBy (K.map f) (T.map f) := by
  apply le_antisymm
  · apply map_le_iff_le_comap.mpr
    apply (closure_le _).mpr
    rintro x ⟨t, ht, k, hk, rfl⟩
    change f (t * k * t⁻¹) ∈ conjugateSpanBy (K.map f) (T.map f)
    rw [map_mul, map_mul, map_inv]
    exact subset_closure ⟨f t, mem_map_of_mem f ht, f k, mem_map_of_mem f hk, rfl⟩
  · apply (closure_le _).mpr
    rintro x ⟨_, ⟨t, ht, rfl⟩, _, ⟨k, hk, rfl⟩, rfl⟩
    exact mem_map.mpr ⟨t * k * t⁻¹, subset_closure ⟨t, ht, k, hk, rfl⟩, by simp⟩

/-- A supplement of a normal subgroup normalizer generates a normal orbit. -/
theorem conjugateSpanBy_normal_of_normalizer_normal (K T : Subgroup G)
    [(normalizer (K : Set G)).Normal]
    (hgen : normalizer (K : Set G) ⊔ T = ⊤) : (conjugateSpanBy K T).Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [← hgen]
  refine sup_le ?_ (le_normalizer_conjugateSpanBy K T)
  apply le_normalizer_closure_iff.mpr
  rintro n hn x ⟨t, ht, k, hk, rfl⟩
  have htn : t⁻¹ * n * t ∈ normalizer (K : Set G) := by
    simpa only [inv_inv] using
      (inferInstance : (normalizer (K : Set G)).Normal).conj_mem n hn t⁻¹
  have hk' := (mem_normalizer_iff.mp htn k).mp hk
  apply subset_closure
  refine ⟨t, ht, (t⁻¹ * n * t) * k * (t⁻¹ * n * t)⁻¹, hk', ?_⟩
  group

/-- A Sylow two-subgroup generates a normal orbit for a subgroup with at most two conjugates. -/
theorem conjugateSpanBy_sylow_normal [Finite G] (K : Subgroup G) (T : Sylow 2 G)
    (hK : K.Normal ∨ (normalizer (K : Set G)).index = 2) :
    (conjugateSpanBy K (T : Subgroup G)).Normal := by
  rcases hK with hn | hi
  · let := hn
    have he : conjugateSpanBy K (T : Subgroup G) = K :=
      le_antisymm (conjugateSpanBy_le le_rfl (by rw [normalizer_eq_top]; exact le_top))
        (le_conjugateSpanBy K _)
    rw [he]
    infer_instance
  · let := normal_of_index_eq_two hi
    apply conjugateSpanBy_normal_of_normalizer_normal
    apply index_eq_one.mp
    have hd : (normalizer (K : Set G) ⊔ (T : Subgroup G)).index ∣ 2 :=
      by simpa only [hi] using index_dvd_of_le (show normalizer (K : Set G) ≤
        normalizer (K : Set G) ⊔ (T : Subgroup G) from le_sup_left)
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with he | he
    · exact he
    · have hdT := index_dvd_of_le (show (T : Subgroup G) ≤
        normalizer (K : Set G) ⊔ (T : Subgroup G) from le_sup_right)
      rw [he] at hdT
      exact (T.not_dvd_index hdT).elim

/-- Generation by commutators propagates to an orbit under a normalizing actor. -/
theorem commutator_conjugateSpanBy_eq_self (K T A : Subgroup G)
    (hAT : A ≤ T) (hTA : T ≤ normalizer (A : Set G)) (hc : ⁅K, A⁆ = K) :
    ⁅conjugateSpanBy K T, A⁆ = conjugateSpanBy K T := by
  apply le_antisymm
    (le_normalizer_iff_commutator_le_left.mp (hAT.trans (le_normalizer_conjugateSpanBy K T)))
  rw [conjugateSpanBy_eq_iSup_conj]
  apply iSup_le
  intro t
  have he := congrArg (map (MulAut.conj (t : G)).toMonoidHom) hc
  have hfix : A.map (MulAut.conj (t : G)).toMonoidHom = A :=
    mem_normalizer_iff_map_conj_eq.mp (hTA t.property)
  rw [map_commutator, hfix] at he
  exact he.symm.le.trans (commutator_mono
    (le_iSup (fun t : T => K.map (MulAut.conj (t : G)).toMonoidHom) t) le_rfl)

/-- A conjugate span of a perfect subgroup is perfect. -/
theorem conjugateSpanBy_isPerfect (K T : Subgroup G) [Group.IsPerfect K] :
    Group.IsPerfect (conjugateSpanBy K T) := by
  rw [conjugateSpanBy_eq_iSup_conj]
  exact isPerfect_iSup_conjugates K T

end Subgroup
