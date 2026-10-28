module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Faithful projections from centralizer control

Suppose every nonidentity element of a subgroup `Z` has its centralizer in `M`.
A subgroup `L` not contained in `M` then has trivial centralizer in `Z`.
Consequently a homomorphism on `Z` is injective if its kernel centralizes `L`.
In particular, a projection is faithful when the discarded factor centralizes `L`.

This is the projection argument in Aschbacher--Smith, *The Classification of
Quasithin Groups*, combined manuscript (1 March 2004), Lemma 15.1.29, p. 1103.
The argument needs neither finiteness nor elementary abelianness; the cardinality
conclusion also uses `Nat.card` and does not require a chosen enumeration.
-/

namespace Subgroup

variable {G : Type*} [Group G]

/-- Centralizer control on the nonidentity elements of `Z` makes its centralizer
of any subgroup outside `M` trivial. -/
public theorem inf_centralizer_eq_bot_of_element_centralizers
    (Z L M : Subgroup G)
    (hcontrol : ∀ z ∈ Z, z ≠ 1 → centralizer ({z} : Set G) ≤ M)
    (houtside : ¬ L ≤ M) : Z ⊓ centralizer (L : Set G) = ⊥ := by
  apply bot_unique
  intro z hz
  change z = 1
  by_contra hne
  apply houtside
  intro l hl
  apply hcontrol z hz.1 hne
  exact mem_centralizer_singleton_iff.mpr
    (mem_centralizer_iff.mp hz.2 l hl)

/-- A map on `Z` whose kernel centralizes `L` is faithful under elementwise
centralizer control, provided `L` is not contained in the controlling subgroup. -/
public theorem projection_injective_of_element_centralizers
    {U : Type*} [Group U] (Z L M : Subgroup G) (π : Z →* U)
    (hcontrol : ∀ z ∈ Z, z ≠ 1 → centralizer ({z} : Set G) ≤ M)
    (houtside : ¬ L ≤ M)
    (hkernel : π.ker.map Z.subtype ≤ centralizer (L : Set G)) :
    Function.Injective π := by
  apply π.ker_eq_bot_iff.mp
  apply bot_unique
  intro z hz
  apply Subtype.ext
  have hmem : (z : G) ∈ Z ⊓ centralizer (L : Set G) :=
    ⟨z.property, hkernel (mem_map_of_mem Z.subtype hz)⟩
  rwa [inf_centralizer_eq_bot_of_element_centralizers Z L M hcontrol houtside] at hmem

/-- The original subgroup and the image of a controlled projection have the
same cardinality. In the application the image is a point of order two. -/
public theorem card_projection_range_of_element_centralizers
    {U : Type*} [Group U] (Z L M : Subgroup G) (π : Z →* U)
    (hcontrol : ∀ z ∈ Z, z ≠ 1 → centralizer ({z} : Set G) ≤ M)
    (houtside : ¬ L ≤ M)
    (hkernel : π.ker.map Z.subtype ≤ centralizer (L : Set G)) :
    Nat.card Z = Nat.card π.range := by
  exact (Nat.card_range_of_injective
    (projection_injective_of_element_centralizers Z L M π hcontrol houtside hkernel)).symm

/-- If an element of `Z` is its projected factor times a factor centralizing
`L`, the projection is faithful. This applies to successive projections of a
diagonal subgroup after collecting the discarded central factors. -/
public theorem projection_injective_of_central_factorization
    {U : Type*} [Group U] (Z L M : Subgroup G)
    (π : Z →* U) (ι : U →* G) (c : Z →* G)
    (hfactor : ∀ z : Z, (z : G) = c z * ι (π z))
    (hcentral : c.range ≤ centralizer (L : Set G))
    (hcontrol : ∀ z ∈ Z, z ≠ 1 → centralizer ({z} : Set G) ≤ M)
    (houtside : ¬ L ≤ M) : Function.Injective π := by
  apply projection_injective_of_element_centralizers Z L M π hcontrol houtside
  rintro x ⟨z, hz, rfl⟩
  have hπ : π z = 1 := hz
  have hx : (z : G) = c z := by simp only [hfactor z, hπ, map_one, mul_one]
  change (z : G) ∈ centralizer (L : Set G)
  rw [hx]
  exact hcentral ⟨z, rfl⟩

end Subgroup
