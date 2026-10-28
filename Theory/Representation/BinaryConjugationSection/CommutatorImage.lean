module
public import Theory.Representation.BinaryConjugationSection.QuadraticPair
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# Images of group commutators in binary conjugation sections

The coordinates of a conjugation commutator are the corresponding linear
displacement. Consequently the image of [A,B] is exactly [image(B),A]. This
identifies the literal fixed-layer commutator with its tilde-module image in
Aschbacher–Smith13.7.16(2), printed p.944.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped commutatorElement
namespace Representation.BinaryConjugationSection
variable {G : Type*} [Group G] {H S E : Subgroup G}
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) H W}
  (c : BinaryConjugationSection H S E ρ)

private theorem coordinates_commutator' (a : H) (b : S) :
    (c.coordinates
      ((⟨(a : G)*b*(a : G)⁻¹,
        (mem_normalizer_iff.mp (c.normalized a.property) b).mp b.property⟩ : S)*b⁻¹)).toAdd =
      ρ a (c.coordinates b).toAdd - (c.coordinates b).toAdd := by
  rw [map_mul,map_inv]
  change (c.coordinates ⟨(a : G)*b*(a : G)⁻¹,_⟩).toAdd +
    -(c.coordinates b).toAdd = _
  rw [c.equivariant,sub_eq_add_neg]

theorem imageSpace_commutator (A B : Subgroup G) (hAH : A ≤ H) (hBS : B ≤ S) :
    c.imageSpace ⁅A,B⁆ = subspaceCommutator ρ (c.imageSpace B) (A.subgroupOf H) := by
  let M := subspaceCommutator ρ (c.imageSpace B) (A.subgroupOf H)
  let P₀ := (M.toAddSubgroup.toSubgroup).comap c.coordinates
  let P := P₀.map S.subtype
  have hcomm : ⁅A,B⁆ ≤ P := by
    apply commutator_le.mpr
    intro a ha b hb
    let aH : H := ⟨a,hAH ha⟩
    let bS : S := ⟨b,hBS hb⟩
    let v : S := (⟨a*b*a⁻¹,
      (mem_normalizer_iff.mp (c.normalized aH.property) b).mp bS.property⟩ : S)*bS⁻¹
    refine ⟨v,?_,rfl⟩
    change (c.coordinates v).toAdd ∈ M
    have he := c.coordinates_commutator' aH bS
    change (c.coordinates v).toAdd = _ at he
    rw [he]
    exact Submodule.subset_span ⟨aH,ha,(c.coordinates bS).toAdd,
      (c.mem_imageSpace_iff B _).mpr ⟨bS,hb,rfl⟩,rfl⟩
  apply le_antisymm
  · intro v hv
    obtain ⟨b,hb,rfl⟩ := (c.mem_imageSpace_iff _ v).mp hv
    obtain ⟨z,hz,he⟩ := hcomm hb
    have he' : z = b := Subtype.ext he
    subst z
    exact hz
  · apply Submodule.span_le.mpr
    rintro _ ⟨a,ha,v,hv,rfl⟩
    obtain ⟨b,hb,rfl⟩ := (c.mem_imageSpace_iff B v).mp hv
    let z : S := (⟨(a : G)*b*(a : G)⁻¹,
      (mem_normalizer_iff.mp (c.normalized a.property) b).mp b.property⟩ : S)*b⁻¹
    exact (c.mem_imageSpace_iff _ _).mpr
      ⟨z,commutator_mem_commutator ha hb,c.coordinates_commutator' a b⟩
end Representation.BinaryConjugationSection
