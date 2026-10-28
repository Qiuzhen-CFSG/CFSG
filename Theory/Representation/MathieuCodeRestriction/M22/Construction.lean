module

public import Theory.Representation.MathieuCodeRestriction
public import Theory.Mathieu.M22.Properties.HexadExtension.Kernel

/-!
# The ten-dimensional native M22 code

Compose the native M22 point-9 stabilizer equivalence with the M23 embedding
in M24. The two fixed coordinates are 0 and 9. Their coordinate-sum pairing
vanishes on the all-ones line, hence defines a functional on the existing
Golay quotient. A certified Golay row makes that functional surjective;
rank-nullity gives its kernel dimension ten. The permutation action preserves
the pairing and restricts to the kernel, with its literal equivariant inclusion.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), H.13.1,
printed p.395 (PDF p.406). Recognition uses actual group and module equivalences.
-/

@[expose] public section

noncomputable section
open Sporadic.Mathieu
open scoped BigOperators Pointwise
namespace MathieuCode

/-- The native M22 inclusion in M23, with distinguished fixed point 9. -/
def m22InM23 : M22 →* M23 :=
  (MulAction.stabilizer M23 (9 : Fin 23)).subtype.comp
    m23EquivM22PointStabilizer.toMonoidHom

/-- The native M22 inclusion in M24 fixes coordinates 0 and 9. -/
def m22Embedding : M22 →* M24 := pointEmbedding.comp m22InM23

theorem m22Embedding_injective : Function.Injective m22Embedding :=
  pointEmbedding_injective.comp (Subtype.val_injective.comp
    m23EquivM22PointStabilizer.injective)

/-- The actual relabelling of the 22 moving coordinates. -/
def m22Coordinates : Fin 22 ↪ Fin 24 :=
  m22M23PointEmbedding.trans m23PointEmbedding

theorem m22Embedding_apply (g : M22) (i : Fin 22) :
    (m22Embedding g : Equiv.Perm (Fin 24)) (m22Coordinates i) =
      m22Coordinates (g • i) := by
  change (pointEmbedding (m22InM23 g) : Equiv.Perm (Fin 24))
    (m23PointEmbedding (m22M23PointMap i)) = _
  rw [pointEmbedding_apply]
  exact congrArg m23PointEmbedding (m22PointStabilizerEquiv_apply g i)

theorem m22Embedding_fixed_zero (g : M22) :
    (m22Embedding g : Equiv.Perm (Fin 24)) 0 = 0 := pointEmbedding_fixed _

theorem m22Embedding_fixed_nine (g : M22) :
    (m22Embedding g : Equiv.Perm (Fin 24)) 9 = 9 := by
  have he : m23PointEmbedding 9 = (9 : Fin 24) := by decide +kernel
  rw [← he]
  change (pointEmbedding (m22InM23 g) : Equiv.Perm (Fin 24)) _ = _
  rw [pointEmbedding_apply]
  exact congrArg m23PointEmbedding (m23EquivM22PointStabilizer g).property

/-- Pairing with the sum of the two distinguished coordinate vectors. -/
def pairOnGolay : golay →ₗ[ZMod 2] ZMod 2 where
  toFun v := v.val 0 + v.val 9
  map_add' v w := by simp only [Submodule.coe_add, Pi.add_apply]; ring
  map_smul' c v := by simp [mul_add]

/-- The pairing descends through the all-ones line. -/
def pairFunctional : Code →ₗ[ZMod 2] ZMod 2 :=
  codeLine.liftQ pairOnGolay (by
    intro v hv
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv
    change v.val 0 + v.val 9 = 0
    change c • BinaryPermutation.allOne (Fin 24) = v.val at hc
    rw [← hc]
    simp [BinaryPermutation.allOne])

@[simp] theorem pairFunctional_mk (v : golay) :
    pairFunctional (codeLine.mkQ v) = v.val 0 + v.val 9 := rfl

/-- The source H.13.1 hyperplane in the eleven-dimensional code. -/
def m22Hyperplane : Submodule (ZMod 2) Code := pairFunctional.ker

abbrev M22Code := m22Hyperplane

@[simp] theorem mem_m22Hyperplane_mk (v : golay) :
    codeLine.mkQ v ∈ m22Hyperplane ↔ v.val 0 + v.val 9 = 0 := Iff.rfl

theorem pairFunctional_surjective : Function.Surjective pairFunctional := by
  have hr : pairFunctional (codeLine.mkQ ⟨row 0, row_mem 0⟩) = 1 := by
    rw [pairFunctional_mk]
    decide +kernel
  intro c
  refine ⟨c • codeLine.mkQ ⟨row 0, row_mem 0⟩, ?_⟩
  rw [map_smul, hr, smul_eq_mul, mul_one]

theorem finrank_m22Code : Module.finrank (ZMod 2) M22Code = 10 := by
  have h := pairFunctional.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr pairFunctional_surjective,
    finrank_top, Module.finrank_self, finrank_code] at h
  change 1 + Module.finrank (ZMod 2) M22Code = 11 at h
  omega

theorem pairFunctional_invariant (g : M22) (v : Code) :
    pairFunctional (codeRepresentation (m22Embedding g) v) = pairFunctional v := by
  induction v using Submodule.Quotient.induction_on with
  | _ v =>
    change pairFunctional (codeRepresentation (m22Embedding g) (codeLine.mkQ v)) =
      pairFunctional (codeLine.mkQ v)
    rw [codeRepresentation_mk, pairFunctional_mk, pairFunctional_mk]
    change v.val ((m22Embedding g).val.symm 0) +
      v.val ((m22Embedding g).val.symm 9) = _
    have h0 := congrArg (m22Embedding g).val.symm (m22Embedding_fixed_zero g)
    have h9 := congrArg (m22Embedding g).val.symm (m22Embedding_fixed_nine g)
    simp only [Equiv.symm_apply_apply] at h0 h9
    rw [← h0, ← h9]

def m22Subrepresentation : Subrepresentation (codeRepresentation.comp m22Embedding) where
  toSubmodule := m22Hyperplane
  apply_mem_toSubmodule g v hv := by
    change pairFunctional (codeRepresentation (m22Embedding g) v) = 0
    rw [pairFunctional_invariant]
    exact hv

/-- The native action on the actual ten-dimensional code hyperplane. -/
def m22CodeRepresentation : Representation (ZMod 2) M22 M22Code :=
  m22Subrepresentation.toRepresentation

/-- The literal inclusion into the eleven-dimensional M24 code. -/
def m22CodeInclusion : M22Code →ₗ[ZMod 2] Code := m22Hyperplane.subtype

theorem m22CodeInclusion_injective : Function.Injective m22CodeInclusion :=
  Subtype.val_injective

@[simp] theorem m22CodeInclusion_equivariant (g : M22) (v : M22Code) :
    m22CodeInclusion (m22CodeRepresentation g v) =
      codeRepresentation (m22Embedding g) (m22CodeInclusion v) := rfl

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- Recognition requires a group isomorphism and an intertwining linear equivalence. -/
def IsM22Code (ρ : Representation (ZMod 2) G V) : Prop :=
  ∃ e : G ≃* M22, ∃ E : V ≃ₗ[ZMod 2] M22Code,
    ∀ g v, E (ρ g v) = m22CodeRepresentation (e g) (E v)

theorem isM22Code : IsM22Code m22CodeRepresentation :=
  ⟨MulEquiv.refl _, LinearEquiv.refl _ _, fun _ _ => rfl⟩

/-- Every recognized code has the source dimension. -/
theorem IsM22Code.finrank {ρ : Representation (ZMod 2) G V} (hρ : IsM22Code ρ) :
    Module.finrank (ZMod 2) V = 10 := by
  obtain ⟨_, E, _⟩ := hρ
  exact E.finrank_eq.trans finrank_m22Code

end MathieuCode
