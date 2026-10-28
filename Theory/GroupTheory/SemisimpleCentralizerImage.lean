module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Index

/-!
# Images of element centralizers in semisimple normal subgroups

A normal subgroup of a finite direct power of a nonabelian simple group is a
product of coordinate factors. Its centralizer is therefore a canonical direct
complement. If the power is normal in an ambient group, the relative centralizer
of its intersection with a homomorphism kernel is also ambient normal.

Every element of the image has a representative in that complement. If its
image commutes with the image of an ambient element, the commutator of the
representative with that element lies both in the complement and in the kernel,
so is trivial. Consequently the image of the element centralizer is exactly the
element centralizer in the image. The cardinal divisibility of a homomorphic
image then transports prime-to-three (and other coprimality) conditions.

This supplies the kernel transport in the first split-constituent paragraph of
Aschbacher–Smith, *The Classification of Quasithin Groups*, combined manuscript
of 1 March 2004, proof of 15.3.58, printed p.1149. That application has one or two
simple factors; the finite-coordinate proof treats both uniformly. Neither
faithfulness nor surjectivity of the ambient homomorphism is assumed.
-/

public section

open Subgroup
namespace Theory.GroupTheory.SemisimpleCentralizer
variable {S I : Type*} [Group S] [IsSimpleGroup S]

private theorem simple_center (hna : ¬ IsMulCommutative S) : center S = ⊥ :=
  (inferInstance : (center S).Normal).eq_bot_or_eq_top.resolve_right
    (fun h => hna (center_eq_top_iff.mp h))

private theorem coordinate_dichotomy [DecidableEq I]
    (hna : ¬ IsMulCommutative S) (N : Subgroup (I → S)) [N.Normal] (i : I) :
    (∀ s : S, Pi.mulSingle i s ∈ N) ∨ (∀ x ∈ N, x i = 1) := by
  let single : S →* (I → S) := MonoidHom.mulSingle (fun _ : I => S) i
  rcases (inferInstance : (N.comap single).Normal).eq_bot_or_eq_top with hb | ht
  · right
    intro x hx
    have hc : x i ∈ center S := by
      apply mem_center_iff.mpr
      intro s
      have hm : Pi.mulSingle i (s * x i * s⁻¹ * (x i)⁻¹) ∈ N := by
        have he : Pi.mulSingle i (s * x i * s⁻¹ * (x i)⁻¹) =
            single s * x * (single s)⁻¹ * x⁻¹ := by
          ext j
          by_cases hj : j = i
          · subst j; simp [single]
          · simp [single, Pi.mulSingle_eq_of_ne hj]
        rw [he]
        exact N.mul_mem ((inferInstance : N.Normal).conj_mem x hx (single s))
          (N.inv_mem hx)
      have hmem : s * x i * s⁻¹ * (x i)⁻¹ ∈ N.comap single := hm
      rw [hb, mem_bot] at hmem
      exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hmem))
    simpa only [simple_center hna, mem_bot] using hc
  · left
    intro s
    exact show s ∈ N.comap single from ht ▸ mem_top s

/-- A normal subgroup of a finite power of a nonabelian simple group has its
centralizer as a direct complement. -/
theorem normal_centralizer_complement [Finite I]
    (hna : ¬ IsMulCommutative S) (N : Subgroup (I → S)) [N.Normal] :
    N ⊓ centralizer (N : Set (I → S)) = ⊥ ∧
      N ⊔ centralizer (N : Set (I → S)) = ⊤ := by
  classical
  constructor
  · apply eq_bot_iff.mpr
    intro x hx
    apply mem_bot.mpr
    funext i
    rcases coordinate_dichotomy hna N i with hall | hz
    · have hc : x i ∈ center S := by
        apply mem_center_iff.mpr
        intro s
        have h := congrFun (mem_centralizer_iff.mp hx.2 _ (hall s)) i
        simpa using h
      exact mem_bot.mp (simple_center hna ▸ hc)
    · exact hz x hx.1
  · apply eq_top_iff.mpr
    intro x _
    apply pi_mem_of_mulSingle_mem
    intro i
    rcases coordinate_dichotomy hna N i with hall | hz
    · exact mem_sup_left (hall (x i))
    · apply mem_sup_right
      apply mem_centralizer_iff.mpr
      intro y hy
      ext j
      by_cases hj : j = i
      · subst j; simp [hz y hy]
      · simp [Pi.mulSingle_eq_of_ne hj]

variable {G : Type*} [Group G]

omit [IsSimpleGroup S] in
private theorem map_centralizer_equiv (e : G ≃* (I → S)) (N : Subgroup G) :
    (centralizer (N : Set G)).map e.toMonoidHom =
      centralizer (N.map e.toMonoidHom : Set (I → S)) := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    apply mem_centralizer_iff.mpr
    rintro _ ⟨b, hb, rfl⟩
    change e b * e a = e a * e b
    simpa only [map_mul] using congrArg e (mem_centralizer_iff.mp ha b hb)
  · intro hx
    refine ⟨e.symm x, mem_centralizer_iff.mpr ?_, e.apply_symm_apply x⟩
    intro b hb
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using
      mem_centralizer_iff.mp hx (e b) (mem_map_of_mem e.toMonoidHom hb)

private theorem complement_of_equiv [Finite I]
    (hna : ¬ IsMulCommutative S) (e : G ≃* (I → S))
    (N : Subgroup G) [N.Normal] :
    N ⊓ centralizer (N : Set G) = ⊥ ∧ N ⊔ centralizer (N : Set G) = ⊤ := by
  let : (N.map e.toMonoidHom).Normal := Subgroup.Normal.map inferInstance _ e.surjective
  obtain ⟨hd, hs⟩ := normal_centralizer_complement hna (N.map e.toMonoidHom)
  constructor
  · apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_inf _ _ _ e.injective, map_centralizer_equiv, Subgroup.map_bot]
    exact hd
  · apply map_injective (f := e.toMonoidHom) e.injective
    rw [Subgroup.map_sup, map_centralizer_equiv, map_top_of_surjective _ e.surjective]
    exact hs

/-- The kernel intersection has its relative centralizer as an ambient-normal
complement inside a normal semisimple subgroup. -/
theorem relative_complement [Finite I]
    (hna : ¬ IsMulCommutative S) (K N : Subgroup G) [K.Normal] [N.Normal]
    (hNK : N ≤ K) (e : K ≃* (I → S)) :
    N ⊓ (K ⊓ centralizer (N : Set G)) = ⊥ ∧
      N ⊔ (K ⊓ centralizer (N : Set G)) = K := by
  have he : (centralizer (N.subgroupOf K : Set K)).map K.subtype =
      K ⊓ centralizer (N : Set G) := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨a.property, mem_centralizer_iff.mpr ?_⟩
      intro b hb
      exact congrArg Subtype.val (mem_centralizer_iff.mp ha ⟨b, hNK hb⟩ hb)
    · rintro ⟨hxK, hx⟩
      refine ⟨⟨x, hxK⟩, mem_centralizer_iff.mpr ?_, rfl⟩
      intro b hb
      exact Subtype.ext (mem_centralizer_iff.mp hx b hb)
  obtain ⟨hd, hs⟩ := complement_of_equiv hna e (N.subgroupOf K)
  constructor
  · have hh := congrArg (Subgroup.map K.subtype) hd
    rwa [map_inf _ _ _ K.subtype_injective, map_subgroupOf_eq_of_le hNK,
      he, Subgroup.map_bot] at hh
  · have hh := congrArg (Subgroup.map K.subtype) hs
    rwa [Subgroup.map_sup, map_subgroupOf_eq_of_le hNK, he,
      ← MonoidHom.range_eq_map, range_subtype] at hh

variable {H : Type*} [Group H]

/-- Homomorphisms preserve element centralizers on normal finite powers of
nonabelian simple groups, even when the homomorphism has a kernel. -/
theorem map_inf_centralizer [Finite I]
    (hna : ¬ IsMulCommutative S) (K : Subgroup G) [K.Normal]
    (e : K ≃* (I → S)) (f : G →* H) (v : G) :
    (K ⊓ centralizer ({v} : Set G)).map f =
      K.map f ⊓ centralizer ({f v} : Set H) := by
  let N := K ⊓ f.ker
  let C := K ⊓ centralizer (N : Set G)
  obtain ⟨hd, hs⟩ := relative_complement hna K N inf_le_left e
  change N ⊓ C = ⊥ at hd
  change N ⊔ C = K at hs
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨mem_map_of_mem f hx.1, mem_centralizer_singleton_iff.mpr ?_⟩
    simpa only [map_mul] using congrArg f (mem_centralizer_singleton_iff.mp hx.2)
  · rintro y ⟨⟨x, hx, hxy⟩, hy⟩
    obtain ⟨a, ha, c, hc, hac⟩ := mem_sup_of_normal_left.mp (hs.symm ▸ hx)
    have hfc : f c = y := by
      have ha1 : f a = 1 := ha.2
      calc
        f c = f (a * c) := by rw [map_mul, ha1, one_mul]
        _ = y := (congrArg f hac).trans hxy
    have hccomm : f c * f v = f v * f c := by
      rw [hfc]
      exact mem_centralizer_singleton_iff.mp hy
    have hdc : v * c * v⁻¹ * c⁻¹ ∈ C :=
      C.mul_mem ((inferInstance : C.Normal).conj_mem c hc v) (C.inv_mem hc)
    have hdf : f (v * c * v⁻¹ * c⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hccomm,
        mul_inv_cancel_right, mul_inv_cancel]
    have hd1 : v * c * v⁻¹ * c⁻¹ = 1 := by
      have hm : v * c * v⁻¹ * c⁻¹ ∈ N ⊓ C := ⟨⟨hdc.1, hdf⟩, hdc⟩
      simpa only [hd, mem_bot] using hm
    refine ⟨c, ⟨hc.1, mem_centralizer_singleton_iff.mpr ?_⟩, hfc⟩
    exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hd1)).symm

/-- Coprimality of the original centralizer order with `m` survives passage
to a homomorphic image of the normal semisimple subgroup. In particular take
`m = 3` for a prime-to-three order. -/
theorem coprime_card_image_centralizer [Finite I]
    (hna : ¬ IsMulCommutative S) (K : Subgroup G) [K.Normal]
    (e : K ≃* (I → S)) (f : G →* H) (v : G) (m : ℕ)
    (hc : Nat.Coprime m (Nat.card ↥(K ⊓ centralizer ({v} : Set G)))) :
    Nat.Coprime m (Nat.card ↥(K.map f ⊓ centralizer ({f v} : Set H))) := by
  rw [← map_inf_centralizer hna K e f v]
  exact hc.of_dvd_right ((K ⊓ centralizer ({v} : Set G)).card_map_dvd f)

end Theory.GroupTheory.SemisimpleCentralizer
