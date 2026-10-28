module

public import Theory.AtlasPort.OtherSporadic.Codes.HexacodeAutomorphismPackage
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# Binary hexacode action and full-weight scalar planes

The actual monomial stabilizer of the hexacode acts faithfully on its
six-dimensional binary vector space. The coordinate-kernel generator
satisfies `z² + z + 1 = 0` on that space and fixes only zero. A scalar plane
is a two-dimensional binary subspace stable under this specific generator.

We single out the scalar planes whose nonzero words all have Hamming
weight six, and construct one explicitly from the systematic word with
initial coordinates `(a,a,b)`. Its binary coordinates prove dimension two,
scalar invariance and full weight by finite calculations.

These definitions provide concrete targets for the exceptional action
and definite-plane recognition on printed p.1155 of Aschbacher–Smith,
*The Classification of Quasithin Groups* (combined manuscript, 1 March
2004). This module does not identify the source plane with this family.
The underlying code and automorphisms are the existing licensed ATLAS
ports under `Theory.AtlasPort.OtherSporadic.Codes`.
-/

@[expose] public section

open Atlas.Codes

namespace Representation.Hexacode

/-- The literal action on the code, expressed as a binary representation. -/
def action : Representation (ZMod 2) HexAutomorphisms hexacode :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp hexAction

/-- Faithfulness survives forgetting the inverses of the linear automorphisms. -/
theorem action_injective : Function.Injective action := by
  intro g h he
  apply hexAction_injective
  apply LinearEquiv.toLinearMap_injective
  exact he

/-- The coordinate-kernel generator acts as a primitive cubic scalar. -/
theorem scalar_quadratic (w : hexacode) :
    action hexZ (action hexZ w) + action hexZ w + w = 0 := by
  apply Subtype.ext
  funext i
  have h : ∀ (i : HexIndex) (u : K),
      (if i.2 = 0 then localKappa else localKappa⁻¹)
          ((if i.2 = 0 then localKappa else localKappa⁻¹) u) +
        (if i.2 = 0 then localKappa else localKappa⁻¹) u + u = 0 := by decide
  exact h i (w.val i)

/-- The primitive cubic scalar has no nonzero fixed vector. -/
theorem scalar_fixed_iff (w : hexacode) : action hexZ w = w ↔ w = 0 := by
  constructor
  · intro hw
    have h := scalar_quadratic w
    rw [hw, hw] at h
    have hh : w + w = 0 := by
      apply Subtype.ext
      funext i
      exact Prod.ext (bit_self_add _) (bit_self_add _)
    rwa [hh, zero_add] at h
  · rintro rfl
    exact map_zero _

/-- A scalar plane all of whose three nonzero words have weight six. -/
def IsFullWeightScalarPlane (P : Submodule (ZMod 2) hexacode) : Prop :=
  Module.finrank (ZMod 2) P = 2 ∧
  hexZ ∈ BinaryOffender.subspaceStabilizer action P ∧
  ∀ w : P, w ≠ 0 → hammingNorm (w.val : HexWord) = 6

/-- An explicit full-weight codeword in the existing systematic coordinates. -/
def fullWeightWord : hexacode :=
  ⟨systematicEncoder ![a, a, b], systematic_mem _⟩

/-- Binary coordinates on the span of the word and its scalar translate. -/
def fullWeightPlaneEncoder : (Bit × Bit) →ₗ[Bit] hexacode where
  toFun r := r.1 • fullWeightWord + r.2 • hexAction hexZ fullWeightWord
  map_add' := by intros; simp only [Prod.fst_add, Prod.snd_add, add_smul]; abel
  map_smul' := by intros; simp only [Prod.smul_fst, Prod.smul_snd, smul_add,
    smul_smul, smul_eq_mul, RingHom.id_apply]

/-- The specified scalar plane, as an actual subspace of the hexacode. -/
def fullWeightPlane : Submodule Bit hexacode := fullWeightPlaneEncoder.range

/-- The first code coordinate recovers both binary coefficients. -/
theorem fullWeightPlaneEncoder_injective : Function.Injective fullWeightPlaneEncoder := by
  intro r s h
  have he := congrArg (fun w : hexacode => w.val (hexPos 0)) h
  have hc : ∀ t : Bit × Bit, (fullWeightPlaneEncoder t).val (hexPos 0) = t := by decide
  rw [hc, hc] at he
  exact he

/-- The specified plane has binary dimension two. -/
theorem fullWeightPlane_finrank : Module.finrank Bit fullWeightPlane = 2 := by
  rw [fullWeightPlane, LinearMap.finrank_range_of_inj fullWeightPlaneEncoder_injective]
  simp [Module.finrank_prod]

/-- The cubic scalar cycles the three nonzero coefficient pairs. -/
theorem fullWeightPlaneEncoder_rotate (r : Bit × Bit) :
    action hexZ (fullWeightPlaneEncoder r) = fullWeightPlaneEncoder (r.2, r.1 + r.2) := by
  apply Subtype.ext
  funext i
  revert r i
  decide

/-- The specified plane is stabilized by the actual coordinate kernel. -/
theorem fullWeightPlane_scalar_stable :
    hexZ ∈ BinaryOffender.subspaceStabilizer action fullWeightPlane := by
  intro w
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨(r.1 + r.2, r.1), ?_⟩
    apply (hexAction hexZ).injective
    change action hexZ (fullWeightPlaneEncoder (r.1 + r.2, r.1)) = action hexZ w
    rw [fullWeightPlaneEncoder_rotate]
    have hr' : r.1 + r.2 + r.1 = r.2 := by
      rw [add_right_comm, bit_self_add, zero_add]
    rw [hr']
    exact hr
  · rintro ⟨r, rfl⟩
    exact ⟨(r.2, r.1 + r.2), (fullWeightPlaneEncoder_rotate r).symm⟩

/-- All three nonzero vectors in the specified plane have weight six. -/
theorem fullWeightPlane_full_weight (w : fullWeightPlane) (hw : w ≠ 0) :
    hammingNorm (w.val : HexWord) = 6 := by
  obtain ⟨r, hr⟩ := w.property
  have hn : r ≠ 0 := by
    intro h
    apply hw
    apply Subtype.ext
    rw [← hr, h, map_zero]
    rfl
  rw [← hr]
  have ht : ∀ r : Bit × Bit, r ≠ 0 →
      hammingNorm (fullWeightPlaneEncoder r : HexWord) = 6 := by decide
  exact ht r hn

/-- The required concrete plane family is nonempty. -/
theorem fullWeightPlane_isFullWeightScalarPlane : IsFullWeightScalarPlane fullWeightPlane :=
  ⟨fullWeightPlane_finrank, fullWeightPlane_scalar_stable, fullWeightPlane_full_weight⟩

end Representation.Hexacode
