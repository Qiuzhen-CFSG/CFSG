module
public import Theory.GroupAction.IrreducibleTwoCoreKernel
public import Mathlib.Algebra.Group.Hom.Basic

/-!
# An equivariant family with only small images is trivial

Let a group act on a family group A, a source group X and a commutative target
V. Suppose A is a finite elementary abelian two-group, its actual automorphism
image is a two-group, and A injects into the homomorphisms X →* V through a
simultaneously equivariant pairing. If V is finite and its only invariant
subgroups are the trivial and full subgroups, then strict smallness of every
individual image forces A to be trivial. Neither the acting group nor X must
be finite, and no action is assumed faithful.

A nontrivial A would have a nonidentity point fixed by its actual two-group
automorphism image. The corresponding homomorphism is equivariant, so its
image is invariant in V. Injectivity makes that image nontrivial; irreducibility
makes it all of V, contradicting its cardinality bound. This is the
source-neutral family argument used for the commutator pairing in
Stellmacher (10.1)(16), printed p.64.
-/

public theorem equivariant_family_subsingleton_of_small_images
    {G X A V : Type*} [Group G] [Group X] [Group A] [CommGroup V]
    [Finite A] [Finite V] [IsElementaryAbelian 2 A]
    [MulDistribMulAction G X] [MulDistribMulAction G A] [MulDistribMulAction G V]
    (pairing : A →* (X →* V)) (hinjective : Function.Injective pairing)
    (hequivariant : ∀ (g : G) (a : A) (x : X),
      pairing (g • a) (g • x) = g • pairing a x)
    (htwo : IsPGroup 2 (MulDistribMulAction.toMulAut G A).range)
    (hirreducible : ∀ D : Subgroup V,
      (∀ g : G, ∀ v : V, v ∈ D → g • v ∈ D) → D = ⊥ ∨ D = ⊤)
    (hsmall : ∀ a : A, Nat.card (pairing a).range < Nat.card V) :
    Subsingleton A := by
  classical
  by_contra hnontrivial
  let _ : Nontrivial A := not_subsingleton_iff_nontrivial.mp hnontrivial
  let T := (MulDistribMulAction.toMulAut G A).range
  have hfixed := irreducible_fixed_nontrivial (W := A) T htwo
  obtain ⟨a,hane⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hfixed
  have hfix (g : G) : g • (a:A) = a :=
    a.property ⟨MulDistribMulAction.toMulAut G A g,⟨g,rfl⟩⟩
  let D := (pairing (a:A)).range
  have hinvariant : ∀ g : G, ∀ v : V, v ∈ D → g • v ∈ D := by
    intro g v hv
    obtain ⟨x,rfl⟩ := hv
    refine ⟨g • x,?_⟩
    simpa only [hfix] using hequivariant g (a:A) x
  have hne : D ≠ ⊥ := by
    intro hbot
    have hzero : pairing (a:A) = 1 := MonoidHom.range_eq_bot_iff.mp hbot
    have haone : (a:A) = 1 := hinjective (hzero.trans (map_one pairing).symm)
    exact hane (Subtype.ext haone)
  have htop : D = ⊤ := (hirreducible D hinvariant).resolve_left hne
  have hbound := hsmall (a:A)
  change Nat.card D < Nat.card V at hbound
  rw [htop,Nat.card_congr Subgroup.topEquiv.toEquiv] at hbound
  exact (Nat.lt_irrefl _ hbound)
