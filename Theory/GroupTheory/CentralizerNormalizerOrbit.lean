module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic

/-!
# Centralizing Sylow subgroups and normalizer fusion

Suppose the centralizer of an element is transitive on the conjugates of a
subgroup containing that element. Its ambient conjugacy class inside the
subgroup is then a single normalizer orbit. If a Sylow p-subgroup of that
normalizer centralizes the element, orbit-stabilizer makes this fusion set
have cardinality prime to p.

The proof transports a conjugating element into the normalizer, preserving
literal conjugation `x ↦ gxg⁻¹`, and applies the Sylow index theorem. The binary
cardinality-eight consequence is used in Aschbacher–Smith, *The Classification
of Quasithin Groups*, combined manuscript of 1 March 2004, printed p.559.
-/

public section

open Subgroup MulAction

namespace Subgroup

private theorem map_conj_mul {G : Type*} [Group G] (Q : Subgroup G) (a b : G) :
    Q.map (MulAut.conj (a * b)).toMonoidHom =
      (Q.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext z
  change (a * b) * z * (a * b)⁻¹ = a * (b * z * b⁻¹) * a⁻¹
  group

/-- Centralizer transitivity on the subgroup family and a centralizing Sylow
subgroup force the ambient fusion set to have cardinality prime to p. -/
theorem prime_not_dvd_card_fusion_of_sylow_centralizes
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (Q : Subgroup G) (t : G) (ht : t ∈ Q)
    (P : Sylow p (normalizer (Q : Set G)))
    (hP : (P : Subgroup (normalizer (Q : Set G))).map
      (normalizer (Q : Set G)).subtype ≤ centralizer ({t} : Set G))
    (hfamily : ∀ g : G, t ∈ Q.map (MulAut.conj g).toMonoidHom →
      ∃ c ∈ centralizer ({t} : Set G),
        Q.map (MulAut.conj g).toMonoidHom = Q.map (MulAut.conj c).toMonoidHom) :
    ¬ p ∣ Nat.card {y : G // y ∈ Q ∧ IsConj t y} := by
  classical
  let N := normalizer (Q : Set G)
  let tQ : Q := ⟨t, ht⟩
  have htrans (y : G) (hy : y ∈ Q) (hconj : IsConj t y) :
      (⟨y, hy⟩ : Q) ∈ orbit N tQ := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    have htmap : t ∈ Q.map (MulAut.conj g⁻¹).toMonoidHom := by
      rw [mem_map_equiv]
      simpa only [MulAut.conj_symm_apply, inv_inv, hg] using hy
    obtain ⟨c, hc, hcg⟩ := hfamily g⁻¹ htmap
    have hn : g * c ∈ N := by
      apply mem_normalizer_iff_map_conj_eq.mpr
      change Q.map (MulAut.conj (g * c)).toMonoidHom = Q
      rw [map_conj_mul, ← hcg, ← map_conj_mul]
      ext z
      simp
    apply mem_orbit_iff.mpr
    refine ⟨⟨g * c, hn⟩, Subtype.ext ?_⟩
    have hct : c * t = t * c := mem_centralizer_singleton_iff.mp hc
    change (g * c) * t * (g * c)⁻¹ = y
    calc
      (g * c) * t * (g * c)⁻¹ = g * (c * t) * c⁻¹ * g⁻¹ := by group
      _ = g * (t * c) * c⁻¹ * g⁻¹ := by rw [hct]
      _ = g * t * g⁻¹ := by group
      _ = y := hg
  have hconj (x : orbit N tQ) : IsConj t (x.val : G) := by
    obtain ⟨n, hn⟩ := mem_orbit_iff.mp x.property
    refine isConj_iff.mpr ⟨n, ?_⟩
    exact congrArg Subtype.val hn
  let e : orbit N tQ ≃ {y : G // y ∈ Q ∧ IsConj t y} :=
    Equiv.ofBijective (fun x => ⟨x.val, x.val.property, hconj x⟩) (by
      constructor
      · intro x y h
        have he : ((x.val : Q) : G) = ((y.val : Q) : G) :=
          congrArg (fun z : {y : G // y ∈ Q ∧ IsConj t y} => z.val) h
        exact Subtype.ext (Subtype.ext he)
      · intro y
        exact ⟨⟨⟨y.val, y.property.1⟩, htrans y.val y.property.1 y.property.2⟩, rfl⟩)
  have hPS : (P : Subgroup N) ≤ stabilizer N tQ := by
    intro n hn
    rw [mem_stabilizer_iff]
    apply Subtype.ext
    change (n : G) * t * (n : G)⁻¹ = t
    apply mul_inv_eq_iff_eq_mul.mpr
    exact mem_centralizer_singleton_iff.mp (hP (mem_map_of_mem N.subtype hn))
  have hcard : Nat.card {y : G // y ∈ Q ∧ IsConj t y} =
      (stabilizer N tQ).index := by
    rw [← Nat.card_congr e, Nat.card_congr (orbitEquivQuotientStabilizer N tQ)]
    rfl
  rw [hcard]
  exact fun hd => P.not_dvd_index (hd.trans (index_dvd_of_le hPS))

/-- The cardinality-eight fusion configuration is incompatible with a
centralizing Sylow two-subgroup of the literal normalizer. -/
theorem false_of_eight_fusion_and_sylow_centralizes {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) (t : G) (ht : t ∈ Q)
    (P : Sylow 2 (normalizer (Q : Set G)))
    (hP : (P : Subgroup (normalizer (Q : Set G))).map
      (normalizer (Q : Set G)).subtype ≤ centralizer ({t} : Set G))
    (hfamily : ∀ g : G, t ∈ Q.map (MulAut.conj g).toMonoidHom →
      ∃ c ∈ centralizer ({t} : Set G),
        Q.map (MulAut.conj g).toMonoidHom = Q.map (MulAut.conj c).toMonoidHom)
    (hcard : Nat.card {y : G // y ∈ Q ∧ IsConj t y} = 8) : False := by
  have h := prime_not_dvd_card_fusion_of_sylow_centralizes Q t ht P hP hfamily
  rw [hcard] at h
  exact h (by decide)

end Subgroup
