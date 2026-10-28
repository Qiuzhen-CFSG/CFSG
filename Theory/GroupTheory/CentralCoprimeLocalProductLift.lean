module

public import Theory.GroupTheory.PerfectCentralPGroupSplit
public import Theory.GroupTheory.PerfectCentralizerLift
public import Theory.GroupTheory.CentralCoprimePrimeLift
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.Algebra.Group.Equiv.TypeTags

open Subgroup

/-!
# Lifting local products through central prime-group kernels

A perfect subgroup with cyclic Sylow p-subgroups splits in a finite central
p-extension. If one factor of a product centralizes the entire perfect
support of the second factor, the two sections commute: centralizer lifting
for perfect subgroups removes the possible central commutator.

A nontrivial q-subgroup normalized by the product, for q coprime to p, has a
canonical lift with the full normalizer pulled back. Thus the product lift
remains local, rather than merely preserving ordinary rank.

The concrete application is the affine local of J₃ in Aschbacher--Smith,
A.2.19, printed p.41, supplementing the splitting argument of I.2.1, p.409.
-/

namespace MonoidHom

/-- Split the inverse image of a perfect subgroup with cyclic Sylow p-subgroups. -/
public theorem exists_lift_of_perfect_cyclicSylow_subgroup
    {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    {p : ℕ} [Fact p.Prime] (π : G →* H) (hπ : Function.Surjective π)
    (hz : π.ker ≤ center G) (hp : IsPGroup p π.ker)
    (D : Subgroup H) [Group.IsPerfect D]
    (hD : ∀ S : Sylow p D, IsCyclic S) :
    ∃ s : D →* G, π.comp s = D.subtype := by
  let E := D.comap π
  let q : E →* D := π.subgroupComap D
  have hq : Function.Surjective q := π.subgroupComap_surjective_of_surjective D hπ
  have hqz : q.ker ≤ center E := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact mem_center_iff.mp (hz (congrArg Subtype.val hx)) y
  let k : q.ker →* π.ker :=
    (E.subtype.comp q.ker.subtype).codRestrict π.ker
      (fun x => congrArg Subtype.val x.property)
  have hki : Function.Injective k := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : π.ker => (z : G)) h))
  obtain ⟨s, hs⟩ := PerfectCentralCovering.exists_section_of_central_pGroup_kernel
    q hq hqz (hp.of_injective k hki) hD
  refine ⟨E.subtype.comp s, ?_⟩
  ext d
  exact congrArg Subtype.val (DFunLike.congr_fun hs d)

/-- Lift a product when both factors have perfect splitting supports and the
first factor centralizes the full support of the second. -/
public theorem exists_product_lift_of_perfect_cyclicSylow_subgroups
    {G H A B : Type*} [Group G] [Finite G] [Group H] [Finite H]
    [Group A] [Group B] {p : ℕ} [Fact p.Prime]
    (π : G →* H) (hπ : Function.Surjective π)
    (hz : π.ker ≤ center G) (hp : IsPGroup p π.ker)
    (C D : Subgroup H) [Group.IsPerfect C] [Group.IsPerfect D]
    (hC : ∀ S : Sylow p C, IsCyclic S) (hD : ∀ S : Sylow p D, IsCyclic S)
    (f : A × B →* H) (hleft : ∀ a, f (a, 1) ∈ C)
    (hright : ∀ b, f (1, b) ∈ D)
    (hcomm : ∀ a, f (a, 1) ∈ centralizer (D : Set H)) :
    ∃ F : A × B →* G, π.comp F = f := by
  obtain ⟨s, hs⟩ := π.exists_lift_of_perfect_cyclicSylow_subgroup hπ hz hp C hC
  obtain ⟨t, ht⟩ := π.exists_lift_of_perfect_cyclicSylow_subgroup hπ hz hp D hD
  let u : A →* C := (f.comp (MonoidHom.inl A B)).codRestrict C hleft
  let v : B →* D := (f.comp (MonoidHom.inr A B)).codRestrict D hright
  have hsr (a : A) : π (s (u a)) = f (a, 1) := DFunLike.congr_fun hs (u a)
  have htr (b : B) : π (t (v b)) = f (1, b) := DFunLike.congr_fun ht (v b)
  let : Group.IsPerfect t.range := Group.IsPerfect.range t
  have hmap : t.range.map π = D := by rw [map_range, ht, range_subtype]
  have hc (a : A) : s (u a) ∈ centralizer (t.range : Set G) := by
    rw [← comap_centralizer_map_eq_of_perfect π t.range
      (hz.trans (center_le_centralizer _)), hmap]
    change π (s (u a)) ∈ centralizer (D : Set H)
    rw [hsr]
    exact hcomm a
  have hst (a : A) (b : B) : Commute (s (u a)) (t (v b)) :=
    (mem_centralizer_iff.mp (hc a) _ ⟨v b, rfl⟩).symm
  refine ⟨(s.comp u).noncommCoprod (t.comp v) hst, ?_⟩
  ext ab
  change π (s (u ab.1) * t (v ab.2)) = f ab
  rw [map_mul, hsr, htr, ← map_mul]
  simp

/-- Preserve a genuine local witness while lifting the product. The equality
with the original product map allows injectivity to be checked downstairs. -/
public theorem exists_local_product_lift_of_perfect_cyclicSylow_subgroups
    {G H A B : Type*} [Group G] [Finite G] [Group H] [Finite H]
    [Group A] [Group B] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hpq : Nat.Coprime q p)
    (π : G →* H) (hπ : Function.Surjective π)
    (hz : π.ker ≤ center G) (hp : IsPGroup p π.ker)
    (C D : Subgroup H) [Group.IsPerfect C] [Group.IsPerfect D]
    (hC : ∀ S : Sylow p C, IsCyclic S) (hD : ∀ S : Sylow p D, IsCyclic S)
    (f : A × B →* H) (hleft : ∀ a, f (a, 1) ∈ C)
    (hright : ∀ b, f (1, b) ∈ D)
    (hcomm : ∀ a, f (a, 1) ∈ centralizer (D : Set H))
    (Q₀ : Subgroup H) (hQ₀ : IsPGroup q Q₀) (hQ₀ne : Q₀ ≠ ⊥)
    (hn : ∀ a, f a ∈ normalizer (Q₀ : Set H)) :
    ∃ (Q : Subgroup G) (F : A × B →* G),
      Q ≠ ⊥ ∧ IsPGroup q Q ∧ π.comp F = f ∧
        ∀ a, F a ∈ normalizer (Q : Set G) := by
  obtain ⟨F, hF⟩ := π.exists_product_lift_of_perfect_cyclicSylow_subgroups hπ hz hp C D hC hD f hleft hright hcomm
  have hcoprime : Nat.Coprime q (Nat.card π.ker) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
    rw [hn]
    exact hpq.pow_right n
  obtain ⟨Q, hQ, hmap, hnorm, _, _⟩ :=
    exists_prime_lift_of_central_coprime π hπ hz hcoprime Q₀ hQ₀
  refine ⟨Q, F, ?_, hQ, hF, ?_⟩
  · intro hbot
    apply hQ₀ne
    rw [← hmap, hbot, Subgroup.map_bot]
  · intro a
    rw [← hnorm]
    change (π.comp F) a ∈ normalizer (Q₀ : Set H)
    rw [DFunLike.congr_fun hF a]
    exact hn a

end MonoidHom
