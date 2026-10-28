module

public import Theory.Representation.BinaryConjugationSection
public import Theory.GroupTheory.CommutatorPreimage

/-!
# The kernel of a literal binary section action

An actor fixes every coordinate precisely when all its commutators with
the original section group lie in the original denominator. Consequently
the embedded representation kernel is the ambient commutator preimage.
No faithfulness assumption or replacement of the acting group is used.
Source application: Aschbacher--Smith 13.7.4(1), printed pp.936--938.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Representation.BinaryConjugationSection
variable {G : Type*} [Group G] {H A B : Subgroup G}
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) H W} (s : BinaryConjugationSection H A B ρ)

include s

theorem action_mem_ker_iff (h : H) :
    h ∈ ρ.ker ↔ ∀ a ∈ A, ⁅(h : G), a⁆ ∈ B := by
  have hd (a : A) :
      ρ h (s.coordinates a).toAdd = (s.coordinates a).toAdd ↔
        ⁅(h : G), (a : G)⁆ ∈ B := by
    let a' : A := ⟨(h : G) * (a : G) * (h : G)⁻¹,
      (mem_normalizer_iff.mp (s.normalized h.property) a).mp a.property⟩
    have hc := s.coordinates_eq_one_iff (a' * a⁻¹)
    rw [map_mul, map_inv, mul_inv_eq_one] at hc
    rw [← s.equivariant]
    exact hc
  constructor
  · intro hh a ha
    apply (hd ⟨a, ha⟩).mp
    exact congrArg (fun f : Module.End (ZMod 2) W => f (s.coordinates ⟨a, ha⟩).toAdd) hh
  · intro hh
    apply LinearMap.ext
    intro w
    obtain ⟨a, ha⟩ := s.onto (Multiplicative.ofAdd w)
    have hw : (s.coordinates a).toAdd = w := congrArg Multiplicative.toAdd ha
    change ρ h w = w
    rw [← hw]
    exact (hd a).mpr (hh a a.property)

theorem action_kernel_map (hn : H ≤ normalizer (B : Set G)) :
    ρ.ker.map H.subtype = commutatorPreimage H A B := by
  apply le_antisymm
  · apply le_commutatorPreimage (map_subtype_le _)
    apply commutator_le.mpr
    rintro _ ⟨h, hh, rfl⟩ a ha
    exact (s.action_mem_ker_iff h).mp hh a ha
  · intro h hh
    have hH := commutatorPreimage_le H A B hh
    refine ⟨⟨h, hH⟩, (s.action_mem_ker_iff _).mpr ?_, rfl⟩
    intro a ha
    exact commutator_commutatorPreimage_le H A B hn
      (commutator_mem_commutator hh ha)

end Representation.BinaryConjugationSection
