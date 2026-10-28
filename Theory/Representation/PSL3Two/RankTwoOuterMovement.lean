module
public import Theory.Representation.PSL3Two.RankTwoOuterRecognition
public import Theory.Representation.PSL3Two.NaturalDualRootMovement

/-!
# Outer movement in a small binary SL₃(2) section

Every involution is conjugate to the highest-root involution. Its displacement
in the natural–dual pair therefore contains a nonzero pure natural vector.
Every implemented outer automorphism exchanges the two factors and moves that
vector. Intrinsic rank-two recognition transfers this movement to any fully
moved nonzero binary representation whose involution displacement lies in a
subspace of dimension at most two.

Source: Aschbacher–Smith E.2.17, printed p.230. The literal quotient-section
consumer uses only displacement containment, without assuming a marked
natural–dual equivalence or equality of the displacement and seed images.
-/

public section
open Representation Representation.BinaryOffender
namespace BinaryLinearThree.NaturalDual

/-- Every nonidentity involution displacement contains a vector moved by every outer implementation. -/
theorem outer_moves_involution_displacement
    (a : Group) (ha : a ^ 2 = 1) (hne : a ≠ 1)
    (α : MulAut Group) (f : Space ≃ₗ[ZMod 2] Space)
    (hf : ∀ g v, f (action g v) = action (α g) (f v))
    (hα : α ∉ MulAut.innerSubgroup Group) :
    ∃ v ∈ LinearMap.range (action a - LinearMap.id), f v ≠ v := by
  obtain ⟨g,hg⟩ := FourGroupGeometry.FixedSpaces.exists_involution_conjugator a hne
    (by simpa only [pow_two] using ha)
  change a * g = g * RootMovement.root at hg
  obtain ⟨w,hw⟩ := RootMovement.point_mem_moved
  change action RootMovement.root w - w = RootMovement.point at hw
  let v := action g RootMovement.point
  have hv : v ∈ LinearMap.range (action a - LinearMap.id) := by
    refine ⟨action g w,?_⟩
    change action a (action g w) - action g w = v
    rw [←Module.End.mul_apply,←map_mul,hg,map_mul,Module.End.mul_apply,←map_sub,hw]
  have hv0 : v ≠ 0 := by
    intro hh
    apply RootMovement.point_ne_zero
    have he := congrArg (action g⁻¹) hh
    change action g⁻¹ (action g RootMovement.point) = 0 at he
    simpa only [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,
      Module.End.one_apply,map_zero] using he
  have hv2 : v.2 = 0 := by
    change W.dual g 0 = 0
    exact map_zero _
  refine ⟨v,hv,?_⟩
  intro hfix
  have hfirst := (outer_swaps α f hf hα).1 v.1
  have he : (v.1,0) = v := Prod.ext rfl hv2.symm
  rw [he,hfix] at hfirst
  exact hv0 (Prod.ext hfirst hv2)
end BinaryLinearThree.NaturalDual

namespace BinaryLinearThree.RankTwoOuterRecognition
variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
  [FiniteDimensional (ZMod 2) M] [Nontrivial M]

/-- An outer actor moves a vector in any dimension-two subspace containing an involution displacement. -/
theorem exists_moved_in_subspace
    (ρ : Representation (ZMod 2) Group M)
    (hfull : subspaceCommutator ρ ⊤ ⊤ = ⊤)
    (a : Group) (ha : a ^ 2 = 1) (hne : a ≠ 1)
    (B : Submodule (ZMod 2) M)
    (hB : LinearMap.range (ρ a - LinearMap.id) ≤ B)
    (hdim : Module.finrank (ZMod 2) B ≤ 2)
    (α : MulAut Group) (hα : α ∉ MulAut.innerSubgroup Group)
    (f : M ≃ₗ[ZMod 2] M) (hf : ∀ g v, f (ρ g v) = ρ (α g) (f v)) :
    ∃ v ∈ B, f v ≠ v := by
  have hr : fixedCodim ρ (Subgroup.zpowers a) ≤ 2 := by
    rw [fixedCodim_zpowers_eq_displacement_rank]
    exact (Submodule.finrank_mono hB).trans hdim
  obtain ⟨e⟩ := equiv_natural_dual_of_involution_fixedCodim_le_two
    ρ hfull a ha hne hr α hα f hf
  have he (g : Group) (v : M) : e (ρ g v) = NaturalDual.action g (e v) :=
    LinearMap.congr_fun (e.isIntertwining' g) v
  have hes (g : Group) (v : NaturalDual.Space) :
      e.symm (NaturalDual.action g v) = ρ g (e.symm v) :=
    LinearMap.congr_fun (e.symm.isIntertwining' g) v
  let F := e.toLinearEquiv.symm.trans (f.trans e.toLinearEquiv)
  have hF : ∀ g v, F (NaturalDual.action g v) = NaturalDual.action (α g) (F v) := by
    intro g v
    change e (f (e.symm (NaturalDual.action g v))) =
      NaturalDual.action (α g) (e (f (e.symm v)))
    rw [hes,hf,he]
  obtain ⟨v,⟨w,hw⟩,hm⟩ := NaturalDual.outer_moves_involution_displacement a ha hne α F hF hα
  refine ⟨e.symm v,?_,?_⟩
  · apply hB
    refine ⟨e.symm w,?_⟩
    apply e.toLinearEquiv.injective
    change e (ρ a (e.symm w) - e.symm w) = e (e.symm v)
    rw [map_sub,he,e.apply_symm_apply,e.apply_symm_apply]
    exact hw
  · intro hfix
    apply hm
    change e (f (e.symm v)) = v
    rw [hfix,e.apply_symm_apply]
end BinaryLinearThree.RankTwoOuterRecognition
