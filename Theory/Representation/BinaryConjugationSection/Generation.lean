module

public import Theory.Representation.BinaryConjugationSection
public import Mathlib.RepresentationTheory.Coinvariants
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Lifting generation and fixed vectors from binary conjugation sections

The displacement span in a literal quotient is the image of ambient
commutators. A supplement to that span therefore lifts to generation modulo
the specified kernel. Likewise a fixed-point-free quotient forces every
centralizing representative into the kernel. These arguments need neither
a splitting of the extension nor vanishing of first cohomology.

The two successive applications in Aschbacher--Smith, 11.5.7, printed p.781,
use the natural and dual sections of the original three-conjugate two-core.
-/

@[expose] public section
namespace Representation.BinaryConjugationSection
open Subgroup
open scoped commutatorElement
variable {G : Type*} [Group G] {H A B : Subgroup G}
  {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
  {ρ : Representation (ZMod 2) H M}
  (s : BinaryConjugationSection H A B ρ)

/-- The image of an ambient subgroup in the specified binary section. -/
def image (C : Subgroup G) : Submodule (ZMod 2) M :=
  AddSubgroup.toZModSubmodule 2
    (Subgroup.toAddSubgroup' ((C.subgroupOf A).map s.coordinates))

theorem mem_image (C : Subgroup G) (v : M) :
    v ∈ s.image C ↔ ∃ a : A, (a : G) ∈ C ∧ (s.coordinates a).toAdd = v := Iff.rfl

theorem image_mono {C D : Subgroup G} (h : C ≤ D) : s.image C ≤ s.image D := by
  rintro v ⟨a, ha, rfl⟩
  exact ⟨a, h ha, rfl⟩

/-- Equality of section coordinates differs by an element of the actual kernel. -/
theorem le_sup_kernel_of_image_top (C : Subgroup G) (hc : s.image C = ⊤) :
    A ≤ C ⊔ B := by
  intro a ha
  obtain ⟨c, hcC, he⟩ := (s.mem_image C _).mp
    (show (s.coordinates ⟨a, ha⟩).toAdd ∈ s.image C by rw [hc]; trivial)
  have hk : ((c⁻¹ * ⟨a, ha⟩ : A) : G) ∈ B := by
    apply (s.coordinates_eq_one_iff _).mp
    rw [map_mul, map_inv, Multiplicative.toAdd.injective he, inv_mul_cancel]
  have hm := (C ⊔ B).mul_mem (mem_sup_left hcC) (mem_sup_right hk)
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left] using hm

/-- Every linear displacement lifts to the ambient subgroup commutator. -/
theorem coinvariants_le_image_commutator (P : Subgroup G) (hPH : P ≤ H) :
    Coinvariants.ker (ρ.comp (inclusion hPH)) ≤ s.image ⁅A, P⁆ := by
  apply Submodule.span_le.mpr
  rintro v ⟨⟨p, w⟩, rfl⟩
  obtain ⟨a, ha⟩ := s.onto (Multiplicative.ofAdd w)
  let b : A := ⟨(p : G) * a * (p : G)⁻¹,
    (mem_normalizer_iff.mp (s.normalized (hPH p.property)) a).mp a.property⟩
  refine (s.mem_image _ _).mpr ⟨b * a⁻¹, ?_, ?_⟩
  · change ⁅(p : G), (a : G)⁆ ∈ ⁅A, P⁆
    rw [commutator_comm A P]
    exact commutator_mem_commutator p.property a.property
  · rw [map_mul, map_inv]
    simp only [toAdd_mul, toAdd_inv, ← sub_eq_add_neg]
    change (s.coordinates b).toAdd - (s.coordinates a).toAdd = _
    rw [show (s.coordinates b).toAdd = ρ (inclusion hPH p) (s.coordinates a).toAdd
      from s.equivariant (inclusion hPH p) a, ha]
    rfl

/-- A supplement to the displacement span generates the group modulo the kernel. -/
theorem le_commutator_sup_of_coinvariants (P C : Subgroup G) (hPH : P ≤ H)
    (hspan : Coinvariants.ker (ρ.comp (inclusion hPH)) ⊔ s.image C = ⊤) :
    A ≤ (⁅A, P⁆ ⊔ C) ⊔ B := by
  apply s.le_sup_kernel_of_image_top
  apply top_unique
  rw [← hspan]
  exact sup_le ((s.coinvariants_le_image_commutator P hPH).trans
    (s.image_mono le_sup_left)) (s.image_mono le_sup_right)

include s in
/-- A fixed-point-free section sends every centralizing representative into its kernel. -/
theorem centralizer_le_kernel (P : Subgroup G) (hPH : P ≤ H)
    (hfixed : ∀ v : M, (∀ p : P, ρ (inclusion hPH p) v = v) → v = 0) :
    A ⊓ centralizer (P : Set G) ≤ B := by
  rintro a ⟨ha, hc⟩
  apply (s.coordinates_eq_one_iff ⟨a, ha⟩).mp
  apply Multiplicative.toAdd.injective
  change (s.coordinates ⟨a, ha⟩).toAdd = 0
  apply hfixed
  intro p
  rw [← s.equivariant (inclusion hPH p) ⟨a, ha⟩]
  congr 2
  apply Subtype.ext
  change (p : G) * a * (p : G)⁻¹ = a
  rw [hc p p.property, mul_inv_cancel_right]

end Representation.BinaryConjugationSection
