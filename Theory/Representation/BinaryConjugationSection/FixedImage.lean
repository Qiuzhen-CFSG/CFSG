module
public import Theory.Representation.BinaryConjugationSection.QuadraticPair

/-!
# Fixed coordinate images detect original group commutators

If an actor fixes the coordinate image of a subgroup in a literal binary
section, its commutator with that subgroup lies in the section kernel.
The proof uses the given conjugation coordinates and their exact kernel.
Source application: Aschbacher–Smith13.7.16(2), printed p.944.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped commutatorElement

namespace Representation.BinaryConjugationSection
variable {G : Type*} [Group G] {H S E : Subgroup G}
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) H W}

theorem commutator_le_of_imageSpace_fixed
    (c : BinaryConjugationSection H S E ρ) (A B : Subgroup G)
    (hAH : A ≤ H) (hBS : B ≤ S)
    (hf : c.imageSpace B ≤ fixedSpace ρ (A.subgroupOf H)) : ⁅A,B⁆ ≤ E := by
  apply commutator_le.mpr
  intro a ha b hb
  let aH : H := ⟨a,hAH ha⟩
  let bS : S := ⟨b,hBS hb⟩
  let v : S := ⟨a*b*a⁻¹,
    (mem_normalizer_iff.mp (c.normalized aH.property) b).mp bS.property⟩
  have hfix : ρ aH (c.coordinates bS).toAdd = (c.coordinates bS).toAdd :=
    hf ((c.mem_imageSpace_iff B _).mpr ⟨bS,hb,rfl⟩) ⟨aH,ha⟩
  have hcoords : c.coordinates v = c.coordinates bS := by
    apply Multiplicative.toAdd.injective
    exact (c.equivariant aH bS).trans hfix
  apply (c.coordinates_eq_one_iff (v*bS⁻¹)).mp
  rw [map_mul,map_inv,hcoords,mul_inv_cancel]
end Representation.BinaryConjugationSection

