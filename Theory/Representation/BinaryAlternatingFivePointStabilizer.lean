module
public import Theory.Representation.BinaryPermutationAlternatingActions
public import Theory.Representation.BinaryConjugationSection
public import Theory.GroupTheory.PRegularLift
public import Theory.GroupTheory.PrimeOrderLift

/-!
# Cubic stabilizers in the binary deleted A₅ module

Every binary coloring of five letters has a monochromatic triple. A
three-cycle on that triple fixes the coloring and therefore its deleted
module image. The finite lemma checks this on the 32 colorings; the
remaining argument uses the canonical augmentation-to-deleted map.

For an actual subgroup section with trivial kernel, a quotient cubic
lifts through the actor's two-group kernel with the same odd order. The
literal conjugation coordinates then show that the lifted cubic fixes
the original ambient vector.

Source application: Aschbacher–Smith, 10.2.9, ordinary A₇-block branch,
printed p.753 (combined manuscript, 1 March 2004).
-/

public section
open Subgroup
namespace BinaryPermutation

private theorem full_has_cubic : ∀ v : Full (Fin 5),
    ∃ g : alternatingGroup (Fin 5), g ^ 3 = 1 ∧ g ≠ 1 ∧
      representation (Fin 5) g.val v = v := by decide +kernel

/-- Every vector in the four-dimensional deleted A₅ module is fixed by
an element of order three. -/
theorem natural_exists_cubic_fixed (v : natural (Fin 5)) :
    ∃ g : alternatingGroup (Fin 5), orderOf g = 3 ∧
      alternatingNaturalRepresentation (Fin 5) g v = v := by
  let e := coreEquivNatural (Fin 5) (by decide)
  obtain ⟨w,rfl⟩ := e.surjective v
  obtain ⟨g,hg3,hg,hfix⟩ := full_has_cubic w.val
  refine ⟨g,orderOf_eq_prime hg3 hg,?_⟩
  change naturalRepresentation (Fin 5) g.val (e w) = e w
  rw [←coreEquivNatural_equivariant]
  exact congrArg e (Subtype.ext hfix)
end BinaryPermutation

namespace Representation.BinaryConjugationSection
variable {G : Type*} [Group G] [Finite G] {H W : Subgroup G}

/-- A literal deleted-module marking supplies an ambient cubic fixing
each original vector; no Sylow-fixed hypothesis is needed. -/
theorem exists_cubic_point_centralizer
    (q : H →* alternatingGroup (Fin 5)) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker)
    (c : BinaryConjugationSection H W ⊥
      ((BinaryPermutation.alternatingNaturalRepresentation (Fin 5)).comp q))
    (v : G) (hv : v ∈ W) :
    ∃ x : G, x ∈ H ∧ orderOf x = 3 ∧ x ∈ centralizer ({v} : Set G) := by
  obtain ⟨a,ha,hav⟩ := BinaryPermutation.natural_exists_cubic_fixed
    (c.coordinates ⟨v,hv⟩).toAdd
  obtain ⟨x,hxo,hxa⟩ := q.exists_pRegular_lift hq 2 Nat.prime_two a (by rw [ha]; decide)
  have hx3 : orderOf x = 3 :=
    (q.orderOf_map_eq_of_coprime_of_isPGroup_ker hk x
      (Nat.prime_two.coprime_iff_not_dvd.mpr hxo)).symm.trans (hxa ▸ ha)
  have hci : Function.Injective c.coordinates := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [c.kernel_eq,bot_subgroupOf]
  have hfix := c.equivariant x ⟨v,hv⟩
  change (c.coordinates _).toAdd =
    BinaryPermutation.alternatingNaturalRepresentation (Fin 5) (q x)
      (c.coordinates ⟨v,hv⟩).toAdd at hfix
  rw [hxa,hav] at hfix
  have he : (x : G) * v * (x : G)⁻¹ = v :=
    congrArg Subtype.val (hci hfix)
  refine ⟨x,x.property,(orderOf_coe x).trans hx3,?_⟩
  exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he)
end Representation.BinaryConjugationSection
