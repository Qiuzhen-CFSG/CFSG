module
public import Theory.GroupTheory.NoncentralChiefRefinement.Homogeneous
public import Theory.GroupTheory.NoncentralChiefRefinement.Transport
public import Theory.Representation.BinaryConjugationSection
public import Theory.Representation.TensorFunctionCoordinates

/-!
# Chief refinement from literal binary tensor sections

An equivariant coordinate map makes both original section endpoints normal
in the actor. A finite basis of the trivial multiplicity space gives actual
relative quotient coordinates. The homogeneous chief-refinement theorem
then supplies one noncentral chief factor per natural summand, retaining
both endpoints and the original conjugation action.

Source application: Aschbacher--Smith, 13.7.10(8), printed p.942.
-/

@[expose] public section
open Subgroup NoncentralChiefRefinement
open scoped TensorProduct
namespace Representation.BinaryConjugationSection
variable {G : Type*} [Group G] {H S E : Subgroup G}
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) H W} (c : BinaryConjugationSection H S E ρ)

def upperChiefNode : NormalNode H :=
  ⟨S.subgroupOf H, normal_subgroupOf_of_le_normalizer c.normalized⟩

include c in
theorem kernel_normal_actor : (E.subgroupOf H).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  apply le_normalizer_iff.mpr
  intro h hh e he
  have heS : e ∈ S := c.kernel_le he
  apply (c.coordinates_eq_one_iff ⟨h*e*h⁻¹, (mem_normalizer_iff.mp (c.normalized hh) e).mp heS⟩).mp
  apply Multiplicative.toAdd.injective
  rw [c.equivariant ⟨h, hh⟩ ⟨e, heS⟩]
  have heq : c.coordinates ⟨e, heS⟩ = 1 := (c.coordinates_eq_one_iff _).mpr he
  rw [heq]
  exact map_zero _

def lowerChiefNode : NormalNode H := ⟨E.subgroupOf H, kernel_normal_actor c⟩

theorem lower_le_upperChiefNode : c.lowerChiefNode ≤ c.upperChiefNode :=
  comap_mono c.kernel_le

variable {M N : Type*} [AddCommGroup M] [Module (ZMod 2) M] [Module.Finite (ZMod 2) M]
  [AddCommGroup N] [Module (ZMod 2) N]
  (τ : Representation (ZMod 2) H N)
  (j : M ⊗[ZMod 2] N ≃ₗ[ZMod 2] W)
  (hj : ∀ a z, j (Representation.tprod (Representation.trivial (ZMod 2) H M) τ a z) = ρ a (j z))

include j hj in
noncomputable def tensorChiefCoordinates :
    SectionCoordinates c.lowerChiefNode c.upperChiefNode τ (Module.finrank (ZMod 2) M) := by
  letI : (S.subgroupOf H).Normal := c.upperChiefNode.property
  let f : (c.upperChiefNode).val →* Multiplicative (Fin (Module.finrank (ZMod 2) M) → N) :=
    (tensorFunctionCoordinates j).toAddEquiv.toMultiplicative.toMonoidHom.comp
      (c.coordinates.comp (subgroupOfEquivOfLe c.section_le).toMonoidHom)
  have hf : Function.Surjective f := (tensorFunctionCoordinates j).surjective.comp
    (c.onto.comp (subgroupOfEquivOfLe c.section_le).surjective)
  have hk : f.ker = (c.lowerChiefNode).val.subgroupOf (c.upperChiefNode).val := by
    ext x
    change tensorFunctionCoordinates j (c.coordinates _).toAdd = 0 ↔ _
    rw [LinearEquiv.map_eq_zero_iff]
    exact c.coordinates_eq_one_iff _
  exact {
    equiv := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
    equivariant := by
      intro a x i
      obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective _ x
      exact (congrArg (fun w => tensorFunctionCoordinates j w i)
        (c.equivariant a ((subgroupOfEquivOfLe c.section_le) b))).trans
        (tensorFunctionCoordinates_equivariant τ ρ j hj a _ i) }

variable [Representation.IsIrreducible τ]

include j hj in
theorem exists_tensor_chief_refinement (hτ : ∃ a v, τ a v ≠ v) :
    ∃ s : ChiefSeries H, s.head = c.lowerChiefNode ∧ s.last = c.upperChiefNode ∧
      s.length = Module.finrank (ZMod 2) M ∧
      s.noncentralTwoCount = Module.finrank (ZMod 2) M := by
  obtain ⟨s, h0, h1, hl, hc, _⟩ := (c.tensorChiefCoordinates τ j hj).exists_chief_refinement
    c.lower_le_upperChiefNode hτ
  exact ⟨s, h0, h1, hl, hc⟩
end Representation.BinaryConjugationSection
