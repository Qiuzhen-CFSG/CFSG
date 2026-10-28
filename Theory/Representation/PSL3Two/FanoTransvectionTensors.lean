module
public import Theory.Representation.PSL3Two.FanoLocalStructure.Orbits
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Fano-core transvection tensors

An even word on the seven nonzero vectors of a binary three-space determines
its sum of rank-one symmetric tensors. The map is injective, and a point
complement gives the rank-one tensor of that point. Two small kernel-checked
certificates establish these coordinate identities; no group enumeration
is used. An injective embedding in a nondegenerate space transports the
same tensors to faithful displacement operators. An isotropic embedding
makes their composites zero, and their symmetry gives symplectic isometries.
The construction respects the literal SL₃(2) action on the seven points.

These are the coordinates connecting H.5.3's actual permutation core to the
plane two-core in Aschbacher–Smith 13.4.9, printed p.906.
-/

@[expose] public section
open Matrix
namespace BinaryLinearThree.FanoTransvection

def tensor (a : Core) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  fun i j => ∑ p : Point, a.val p * p.val i * p.val j

@[instance_reducible] private def coreDec : DecidablePred (fun a : BinaryPermutation.Full Point => a ∈ BinaryPermutation.core Point) :=
  fun a => inferInstanceAs (Decidable ((∑ p, a p) = 0))
attribute [local instance] coreDec
@[instance_reducible] private def coreFintype : Fintype Core := Subtype.fintype _
attribute [local instance] coreFintype

private theorem tensor_kernel : ∀ a : Core, tensor a = 0 → a = 0 := by
  decide +kernel

theorem tensor_add (a c : Core) : tensor (a + c) = tensor a + tensor c := by
  ext i j
  simp [tensor, add_mul, Finset.sum_add_distrib]

theorem tensor_zero : tensor (0 : Core) = 0 := by
  ext i j
  simp [tensor]

theorem tensor_injective : Function.Injective tensor := by
  intro a c h
  have hz : tensor (a + c) = 0 := by
    rw [tensor_add, h]
    exact ZModModule.add_self _
  have he := tensor_kernel (a + c) hz
  have hh := congrArg (· + c) he
  simpa only [add_assoc, ZModModule.add_self, add_zero, zero_add] using hh

theorem tensor_pointSpike : ∀ (p : Point) (i j : Fin 3),
    tensor (FanoDecomposition.pointSpike p) i j = p.val i * p.val j := by
  simp only [tensor, FanoDecomposition.pointSpike_apply, Pi.single_apply]
  decide +kernel

theorem tensor_symmetric (a : Core) : (tensor a).transpose = tensor a := by
  ext i j
  simp only [transpose_apply,tensor]
  apply Finset.sum_congr rfl
  intro p _
  ring

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

/-- The sum of rank-one displacements associated with the seven points. -/
def displacement (B : LinearMap.BilinForm (ZMod 2) M)
    (b : Vector →ₗ[ZMod 2] M) (a : Core) : Module.End (ZMod 2) M :=
  ∑ p : Point, a.val p • (B.flip (b p.val)).smulRight (b p.val)

theorem displacement_apply (B : LinearMap.BilinForm (ZMod 2) M)
    (b : Vector →ₗ[ZMod 2] M) (a : Core) (x : M) :
    displacement B b a x = b (∑ p : Point, (a.val p * B x (b p.val)) • p.val) := by
  simp [displacement, map_sum, map_smul, smul_smul]

theorem displacement_add (B : LinearMap.BilinForm (ZMod 2) M)
    (b : Vector →ₗ[ZMod 2] M) (a c : Core) :
    displacement B b (a + c) = displacement B b a + displacement B b c := by
  simp [displacement, add_smul, Finset.sum_add_distrib]

theorem displacement_zero (B : LinearMap.BilinForm (ZMod 2) M)
    (b : Vector →ₗ[ZMod 2] M) : displacement B b 0 = 0 := by
  simp [displacement]

theorem displacement_injective [FiniteDimensional (ZMod 2) M]
    (B : LinearMap.BilinForm (ZMod 2) M) (hB : B.Nondegenerate)
    (b : Vector →ₗ[ZMod 2] M) (hb : Function.Injective b) :
    Function.Injective (displacement B b) := by
  intro a c hac
  apply tensor_injective
  ext i j
  obtain ⟨φ, hφ⟩ := LinearMap.dualMap_surjective_of_injective hb
    (LinearMap.proj j : Vector →ₗ[ZMod 2] ZMod 2)
  let x := (B.toDual hB).symm φ
  have hx (v : Vector) : B x (b v) = v j :=
    (B.apply_toDual_symm_apply φ (b v)).trans (LinearMap.congr_fun hφ v)
  have hh := congrArg (fun N : Module.End (ZMod 2) M => N x) hac
  rw [displacement_apply, displacement_apply] at hh
  have hi := congrFun (hb hh) i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hx] at hi
  simpa only [tensor, mul_right_comm] using hi

end BinaryLinearThree.FanoTransvection

namespace BinaryLinearThree.FanoTransvection
variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (B : LinearMap.BilinForm (ZMod 2) M) (b : Vector →ₗ[ZMod 2] M)
    (hb : ∀ v w, B (b v) (b w) = 0)

include hb in
theorem displacement_on_range (a : Core) (v : Vector) : displacement B b a (b v) = 0 := by
  rw [displacement_apply]
  simp only [hb, mul_zero, zero_smul, Finset.sum_const_zero, map_zero]

include hb in
theorem displacement_pair (a c : Core) (x y : M) :
    B (displacement B b a x) (displacement B b c y) = 0 := by
  rw [displacement_apply, displacement_apply, hb]

include hb in
theorem displacement_composite (a c : Core) (x : M) :
    displacement B b a (displacement B b c x) = 0 := by
  rw [displacement_apply B b c, displacement_on_range B b hb]

theorem displacement_selfAdjoint (hB : B.IsAlt) (a : Core) (x y : M) :
    B (displacement B b a x) y = B x (displacement B b a y) := by
  have hsym (u v : M) : B u v = B v u := by
    simpa only [CharTwo.neg_eq] using hB.neg_eq u v
  simp only [displacement, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.smulRight_apply, map_sum, map_smul,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro p _
  change a.val p * (B x (b p.val) * B (b p.val) y) =
    a.val p * (B y (b p.val) * B x (b p.val))
  rw [hsym (b p.val) y]
  ring

include hb in
theorem displacement_preserves (hB : B.IsAlt) (a : Core) (x y : M) :
    B (x + displacement B b a x) (y + displacement B b a y) = B x y := by
  simp only [map_add, LinearMap.add_apply, displacement_pair B b hb, add_zero]
  rw [displacement_selfAdjoint B b hB]
  rw [add_assoc, ZModModule.add_self, add_zero]

end BinaryLinearThree.FanoTransvection
namespace BinaryLinearThree.FanoTransvection

private theorem spike_weighted : ∀ (p : Point) (u : Vector),
    (∑ q : Point, ((FanoDecomposition.pointSpike p).val q * (u ⬝ᵥ q.val)) • q.val) =
      (u ⬝ᵥ p.val) • p.val := by
  simp only [FanoDecomposition.pointSpike_apply, Pi.single_apply]
  decide +kernel

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (B : LinearMap.BilinForm (ZMod 2) M) (b : Vector →ₗ[ZMod 2] M)

theorem displacement_pointSpike (p : Point) (x : M) :
    displacement B b (FanoDecomposition.pointSpike p) x = B x (b p.val) • b p.val := by
  obtain ⟨u,hu⟩ := (dotProductEquiv (ZMod 2) (Fin 3)).surjective (b.dualMap (B x))
  have he (v : Vector) : u ⬝ᵥ v = B x (b v) := LinearMap.congr_fun hu v
  rw [displacement_apply]
  simp_rw [← he]
  rw [spike_weighted,map_smul]

theorem displacement_equivariant (c : M ≃ₗ[ZMod 2] M) (g : Group)
    (hc : ∀ x y, B (c x) (c y) = B x y)
    (hcb : ∀ v : Vector, c (b v) = b (g • v)) (a : Core) (x : M) :
    c (displacement B b a x) = displacement B b (U₂ g a) (c x) := by
  have happ (d : Core) (y : M) : displacement B b d y =
      ∑ p : Point, d.val p • (B y (b p.val) • b p.val) := rfl
  rw [happ,happ,map_sum]
  simp only [map_smul]
  rw [← Equiv.sum_comp (pointPerm g) (fun p : Point =>
    (U₂ g a).val p • (B (c x) (b p.val) • b p.val))]
  apply Finset.sum_congr rfl
  intro p _
  have hcoeff : (U₂ g a).val (pointPerm g p) = a.val p := by
    change a.val ((pointPerm g).symm (pointPerm g p)) = a.val p
    rw [Equiv.symm_apply_apply]
  have hp : b (pointPerm g p).val = c (b p.val) := (hcb p.val).symm
  rw [hcoeff,hp,hc]

end BinaryLinearThree.FanoTransvection
namespace BinaryLinearThree.FanoTransvection
open FanoLocalStructure FanoDecomposition FanoCoreStructure

private theorem spike_weight : ∀ p : Point, (support (pointSpike p)).card = 6 := by
  simp only [support,pointSpike_apply,Pi.single_apply]
  decide +kernel

private theorem line_weight : ∀ l : Matrix.PSL3Two.Fano.Line,
    (support (lineComplement l)).card = 4 := by
  simp only [support,lineComplement_apply]
  decide +kernel

private theorem basis_weight : ∀ b : Fin 3 → Point, IsBasisTriple b →
    (support (pointSpike (b 0) + pointSpike (b 1) + pointSpike (b 2))).card = 4 := by
  simp only [support,Submodule.coe_add,Pi.add_apply,pointSpike_apply,Pi.single_apply]
  decide +kernel

/-- The literal four Fano-core families have weights six, four, two and four. -/
theorem four_families_weights :
    (∀ a ∈ pointComplements, (support a).card = 6) ∧
    (∀ a ∈ lineComplements, (support a).card = 4) ∧
    (∀ a ∈ weightTwo, (support a).card = 2) ∧
    (∀ a ∈ basisComplements, (support a).card = 4) := by
  refine ⟨?_,?_,fun _ ha => ha,?_⟩
  · rintro _ ⟨p,rfl⟩
    exact spike_weight p
  · rintro _ ⟨l,rfl⟩
    exact line_weight l
  · intro a ha
    obtain ⟨b,hb,rfl⟩ := (mem_basisComplements_iff a).mp ha
    exact basis_weight b hb

end BinaryLinearThree.FanoTransvection
