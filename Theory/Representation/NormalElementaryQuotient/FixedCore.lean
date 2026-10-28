module
public import Theory.Representation.NormalElementaryQuotient
public import Theory.GroupTheory.PCoreImageRestriction

/-!
# Fixed-space centralizers and their exact two-cores

Let V be a normal elementary abelian two-subgroup and let q be the literal
centralizer quotient. The pointwise fixer of the q(A)-fixed binary subspace
has preimage C_G(C_V(A)). Surjectivity gives its exact image as well.
When the kernel is a two-group, the prime-core preimage theorem identifies
the whole embedded two-core. Thus equality of a subgroup containing the
kernel with that core is equivalent to equality of its image with the
module fixer's core.

The nonbinary MS application uses A equal to the actual Sylow subgroup and
V=Ω₁(Z(O₂(KR))). The action, subgroup image and quotient kernel are retained.
This is the elementary quotient/core transport in Aschbacher--Smith
C.1.34, printed pp.136--137; it makes no module-classification assertion.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Representation.NormalElementaryQuotient
open BinaryOffender
variable {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]

/-- The pointwise fixer of the actual fixed space, expressed using the
representation's invertible linear operators. -/
def fixedSpaceFixer (ρ : Representation (ZMod 2) H W) (A : Subgroup H) : Subgroup H :=
  ⨅ v : fixedSpace ρ A,
    (MulAction.stabilizer (Module.End (ZMod 2) W)ˣ (v : W)).comap ρ.asGroupHom

theorem mem_fixedSpaceFixer (ρ : Representation (ZMod 2) H W) (A : Subgroup H) (h : H) :
    h ∈ fixedSpaceFixer ρ A ↔ ∀ v ∈ fixedSpace ρ A, ρ h v = v := by
  simp only [fixedSpaceFixer,Subgroup.mem_iInf,Subgroup.mem_comap,
    MulAction.mem_stabilizer_iff,Subtype.forall]
  rfl

variable {G : Type*} [Group G]
variable (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
  (q : G →* H) (hq : Function.Surjective q)
  (hker : q.ker = centralizer (V : Set G))
local notation "ρ" => representation V q hq hker

/-- The model fixed-space fixer has precisely the original centralizer as
preimage, with the subgroup image and action both literal. -/
theorem fixedSpaceFixer_comap (A : Subgroup G) :
    (fixedSpaceFixer ρ (A.map q)).comap q =
      centralizer ((V ⊓ centralizer (A : Set G) : Subgroup G) : Set G) := by
  ext g
  change q g ∈ fixedSpaceFixer ρ (A.map q) ↔ _
  rw [mem_fixedSpaceFixer]
  constructor
  · intro hf x hx
    let v : Additive V := Additive.ofMul ⟨x,hx.1⟩
    have hv : v ∈ fixedSpace ρ (A.map q) :=
      (mem_fixedSpace_image V q hq hker A v).mpr hx.2
    have he := congrArg (fun w : Additive V => (w.toMul : G)) (hf v hv)
    rw [representation_apply] at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro hc v hv
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [representation_apply]
    have he := hc v.toMul ⟨v.toMul.property,
      (mem_fixedSpace_image V q hq hker A v).mp hv⟩
    rw [←he,mul_inv_cancel_right]

/-- Surjectivity identifies the exact image of the original centralizer. -/
theorem centralizer_fixed_image (A : Subgroup G) :
    (centralizer ((V ⊓ centralizer (A : Set G) : Subgroup G) : Set G)).map q =
      fixedSpaceFixer ρ (A.map q) := by
  rw [←fixedSpaceFixer_comap V q hq hker A,map_comap_eq_self]
  rw [q.range_eq_top_of_surjective hq]
  exact le_top

variable [Finite G] [Finite H]

/-- A two-group action kernel preserves the whole embedded core of the
fixed-space fixer, not just one containment. -/
theorem fixedSpaceFixer_core_comap (hk : IsPGroup 2 q.ker) (A : Subgroup G) :
    ((fixedSpaceFixer ρ (A.map q)).pCoreIn 2).comap q =
      (centralizer ((V ⊓ centralizer (A : Set G) : Subgroup G) : Set G)).pCoreIn 2 := by
  have hc := inf_comap_pCoreIn_eq_of_ker_isPGroup 2 q
    (centralizer ((V ⊓ centralizer (A : Set G) : Subgroup G) : Set G)) hk
  rw [centralizer_fixed_image V q hq hker A] at hc
  have hle : ((fixedSpaceFixer ρ (A.map q)).pCoreIn 2).comap q ≤
      centralizer ((V ⊓ centralizer (A : Set G) : Subgroup G) : Set G) := by
    rw [←fixedSpaceFixer_comap V q hq hker A]
    exact comap_mono (pCoreIn_le 2 _)
  rwa [inf_eq_right.mpr hle] at hc

/-- The original radical/core equality is equivalent to its equality in
the faithful fixed-space action. Every kernel element is retained upstairs. -/
theorem radical_eq_fixed_core_iff (hk : IsPGroup 2 q.ker) (A R : Subgroup G)
    (hR : q.ker ≤ R) :
    R = (centralizer ((V ⊓ centralizer (A : Set G) : Subgroup G) : Set G)).pCoreIn 2 ↔
      R.map q = (fixedSpaceFixer ρ (A.map q)).pCoreIn 2 := by
  constructor
  · intro he
    rw [he,←fixedSpaceFixer_core_comap V q hq hker hk A,map_comap_eq_self]
    rw [q.range_eq_top_of_surjective hq]
    exact le_top
  · intro he
    have hc := congrArg (Subgroup.comap q) he
    rwa [comap_map_eq,sup_eq_left.mpr hR,
      fixedSpaceFixer_core_comap V q hq hker hk A] at hc
end Representation.NormalElementaryQuotient
