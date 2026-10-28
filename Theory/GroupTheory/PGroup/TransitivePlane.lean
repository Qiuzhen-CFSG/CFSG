module

public import Theory.ElementaryAbelian.Quotient
public import Theory.GroupTheory.CentralCoprimePrimeLift

/-!
# Transitive elementary abelian planes through central quotients

The configuration is an actual elementary abelian subgroup of order p² whose
ambient normalizer is transitive on its nonidentity elements. It passes along
injective homomorphisms and lifts through central kernels of order prime to p.
For lifting, use the canonical Sylow lift and the exact normalizer preimage;
faithfulness of the restricted quotient map preserves each conjugacy equation.

The concrete PSL₃ prime-field parabolic supplies this configuration. Its binary
hyperplane-orbit bound is used for the large-prime branch of Aschbacher--Smith
K.2, printed p.453, and Guralnick--Malle, Classification of 2F-modules I,
Proposition 4.2. No representation-degree conclusion is part of the definition.
-/

public section
open Subgroup
namespace Theory.GroupTheory


/-- An actual elementary plane with transitive ambient conjugation. -/
@[expose] def HasTransitiveElementaryPlane (G : Type*) [Group G] (p : ℕ) : Prop :=
  ∃ P : Subgroup G, IsElementaryAbelian p P ∧ Nat.card P = p ^ 2 ∧
    ∀ x y : P, x ≠ 1 → y ≠ 1 →
      ∃ g : normalizer (P : Set G), P.normalizerMonoidHom g x = y

/-- Central coprime quotients lift the plane and its actual conjugation action. -/
theorem HasTransitiveElementaryPlane.of_central_coprime
    {G H : Type*} [Group G] [Finite G] [Group H]
    {p : ℕ} [Fact p.Prime] (f : G →* H) (hf : Function.Surjective f)
    (hcentral : f.ker ≤ center G) (hcop : Nat.Coprime p (Nat.card f.ker))
    (h : HasTransitiveElementaryPlane H p) : HasTransitiveElementaryPlane G p := by
  obtain ⟨P, hP, hcard, htrans⟩ := h
  let : IsElementaryAbelian p P := hP
  obtain ⟨A, _, hmap, hnorm, _, hi⟩ := exists_prime_lift_of_central_coprime
    f hf hcentral hcop P (IsElementaryAbelian.isPGroup p P)
  let r : A →* P := (f.comp A.subtype).codRestrict P (fun a =>
    hmap ▸ mem_map_of_mem f a.property)
  have hr : Function.Bijective r := by
    constructor
    · intro a b hab
      exact hi (congrArg Subtype.val hab)
    · intro b
      obtain ⟨a, ha, hab⟩ := (hmap.symm ▸ b.property : (b : H) ∈ A.map f)
      exact ⟨⟨a, ha⟩, Subtype.ext hab⟩
  let e : A ≃* P := MulEquiv.ofBijective r hr
  refine ⟨A, IsElementaryAbelian.of_surjective e.symm.toMonoidHom e.symm.surjective,
    (Nat.card_congr e.toEquiv).trans hcard, ?_⟩
  intro x y hx hy
  obtain ⟨g, hg⟩ := htrans (e x) (e y)
    (fun he => hx (e.injective (he.trans e.map_one.symm)))
    (fun he => hy (e.injective (he.trans e.map_one.symm)))
  obtain ⟨a, ha⟩ := hf (g : H)
  have han : a ∈ normalizer (A : Set G) := by
    rw [← hnorm]
    change f a ∈ normalizer (P : Set H)
    rw [ha]
    exact g.property
  refine ⟨⟨a, han⟩, hi ?_⟩
  change f (a * (x : G) * a⁻¹) = f y
  have hh := congrArg Subtype.val hg
  change (g : H) * f x * (g : H)⁻¹ = f y at hh
  simpa only [map_mul, map_inv, ha] using hh

/-- An embedding preserves the plane and its normalizer conjugacies. -/
theorem HasTransitiveElementaryPlane.of_injective
    {G H : Type*} [Group G] [Group H] {p : ℕ} [Fact p.Prime]
    (f : G →* H) (hf : Function.Injective f)
    (h : HasTransitiveElementaryPlane G p) : HasTransitiveElementaryPlane H p := by
  obtain ⟨P, hP, hcard, htrans⟩ := h
  let : IsElementaryAbelian p P := hP
  let A := P.map f
  let e : P ≃* A := MulEquiv.ofBijective (f.subgroupMap P)
    ⟨fun x y h => Subtype.ext (hf (congrArg Subtype.val h)), f.subgroupMap_surjective P⟩
  refine ⟨A, IsElementaryAbelian.map f,
    (Subgroup.card_map_of_injective hf).trans hcard, ?_⟩
  intro x y hx hy
  obtain ⟨g, hg⟩ := htrans (e.symm x) (e.symm y)
    (fun he => hx (e.symm.injective (he.trans e.symm.map_one.symm)))
    (fun he => hy (e.symm.injective (he.trans e.symm.map_one.symm)))
  have hgn : f g ∈ normalizer (A : Set H) :=
    P.le_normalizer_map f (mem_map_of_mem f g.property)
  refine ⟨⟨f g, hgn⟩, ?_⟩
  apply Subtype.ext
  change f g * (x : H) * (f g)⁻¹ = y
  have he (v : A) : f (e.symm v : P) = (v : H) :=
    congrArg Subtype.val (e.apply_symm_apply v)
  have hh := congrArg (fun z : P => f (z : G)) hg
  change f ((g : G) * (e.symm x : P) * (g : G)⁻¹) = f (e.symm y : P) at hh
  simpa only [map_mul, map_inv, he] using hh

end Theory.GroupTheory
