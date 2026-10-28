module
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Algebra.Group.Equiv.TypeTags
/-!
# Coordinates on intersections of mutually normalizing subgroups

If J and A normalize each other, every commutator belongs to J∩A.
A surjective additive coordinate map therefore sends this intersection onto a
subgroup containing every action difference. In particular, a module with zero
coinvariants is entirely retained on intersection. Relative normalization is
sufficient; neither subgroup is assumed normal in the ambient group.

Source application: Aschbacher–Smith, G.2.5(8), printed pp.335–336.
-/
@[expose] public section
open Subgroup
open scoped commutatorElement
namespace NormalizedIntersection
variable {G V : Type*} [Group G] [AddCommGroup V]
  (J A : Subgroup G) (hJA : J ≤ normalizer (A : Set G))
  (hAJ : A ≤ normalizer (J : Set G))
  (f : A →* Multiplicative V) (hf : Function.Surjective f)
  (ρ : J → V → V)
  (he : ∀ (l : J) (v : A),
    (f ⟨(l : G) * v * (l : G)⁻¹,
      (mem_normalizer_iff.mp (hJA l.property) v).mp v.property⟩).toAdd = ρ l (f v).toAdd)

def restriction : (J ⊓ A : Subgroup G) →* Multiplicative V :=
  f.comp (inclusion inf_le_right)

include hJA hAJ hf he in
theorem difference_mem (l : J) (v : V) :
    ρ l v - v ∈ (restriction J A f).range.toAddSubgroup' := by
  obtain ⟨w, hw⟩ := hf (Multiplicative.ofAdd v)
  have hcomm : ⁅(l : G), (w : G)⁆ ∈ J ⊓ A :=
    (le_inf (le_normalizer_iff_commutator_le_left.mp hAJ)
      (le_normalizer_iff_commutator_le_right.mp hJA))
      (commutator_mem_commutator l.property w.property)
  refine ⟨⟨⁅(l : G), (w : G)⁆, hcomm⟩, ?_⟩
  change f (⟨⁅(l : G), (w : G)⁆, hcomm.2⟩ : A) = Multiplicative.ofAdd _
  have hx : (⟨⁅(l : G), (w : G)⁆, hcomm.2⟩ : A) =
      ⟨(l : G) * w * (l : G)⁻¹,
        (mem_normalizer_iff.mp (hJA l.property) w).mp w.property⟩ * w⁻¹ :=
    Subtype.ext (by rfl)
  rw [hx, map_mul, map_inv]
  apply Multiplicative.toAdd.injective
  simp only [toAdd_mul, toAdd_inv,
    toAdd_ofAdd, ← sub_eq_add_neg]
  rw [he,hw]
  rfl

include hJA hAJ hf he in
theorem surjective_of_differences
    (hfull : ∀ C : AddSubgroup V, (∀ l v, ρ l v - v ∈ C) → C = ⊤) :
    Function.Surjective (restriction J A f) := by
  apply MonoidHom.range_eq_top.mp
  apply Subgroup.toAddSubgroup'.injective
  exact (hfull _ (difference_mem J A hJA hAJ f hf ρ he)).trans
    Subgroup.toAddSubgroup'.map_top.symm
end NormalizedIntersection
