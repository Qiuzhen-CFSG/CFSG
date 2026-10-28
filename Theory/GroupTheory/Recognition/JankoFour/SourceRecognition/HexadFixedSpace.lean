module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.InvariantPoint.Native
public import Theory.GroupTheory.SylowKernelCore
public import Theory.Mathieu.M22.Properties.HexadExtension

/-!
# Native hexad fixed spaces in the full James action

Use the literal full matrix extension and its degree-22 design action.
For each hexad, take the fixed space of the embedded two-core of its full
stabilizer. Conjugation transports this two-core and its fixed space by the
same matrix. Hexad transitivity therefore reduces cardinality and total
singularity to the single standard hexad, without changing column conventions.

This is the native interface for the E₁ construction in Aschbacher–Segev,
The uniqueness of groups of type J4, Invent. Math. 105 (1991), (4.6),
p.598, DOI 10.1007/BF01232280. The standard fixed-space calculation is a
separate input; this module does not assert its dimension or singularity.
-/

@[expose] public section
noncomputable section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
open Sporadic.Mathieu M22TripleCover M22TripleCover.Ambient InvariantPoint
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Janko4.InvolutionCentralizers.First.QuotientExtension

/-- The actual full native matrix stabilizer of a design hexad. -/
def nativeHexadStabilizer (B : Finset (Fin 22)) : Subgroup actionGroup :=
  (MulAction.stabilizer (Equiv.Perm (Fin 22)) B).comap pointAction

/-- The fixed space of its whole two-core, in the original column convention. -/
def nativeHexadFixedSpace (B : Finset (Fin 22)) : Submodule (ZMod 2) BinarySpace where
  carrier := {v | ∀ g ∈ (nativeHexadStabilizer B).pCoreIn 2, binaryAction g v = v}
  zero_mem' := by intro g hg; exact map_zero _
  add_mem' := by intro u v hu hv g hg; rw [map_add,hu g hg,hv g hg]
  smul_mem' := by intro a u hu g hg; rw [map_smul,hu g hg]

/-- The full native stabilizers are conjugate under the actual matrix action. -/
theorem nativeHexadStabilizer_map_conj (g : actionGroup) (B : Finset (Fin 22)) :
    (nativeHexadStabilizer B).map (MulAut.conj g).toMonoidHom =
      nativeHexadStabilizer (pointAction g • B) := by
  ext k
  rw [mem_map_equiv]
  change pointAction (g⁻¹*k*g) • B = B ↔
    pointAction k • (pointAction g • B) = pointAction g • B
  rw [map_mul,map_mul,map_inv,mul_smul,mul_smul]
  exact inv_smul_eq_iff

/-- The embedded native two-cores transport with the same conjugator. -/
theorem nativeHexadTwoCore_map_conj (g : actionGroup) (B : Finset (Fin 22)) :
    ((nativeHexadStabilizer B).pCoreIn 2).map (MulAut.conj g).toMonoidHom =
      (nativeHexadStabilizer (pointAction g • B)).pCoreIn 2 := by
  rw [map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective,
    nativeHexadStabilizer_map_conj]

/-- The column action carries the fixed space to the conjugate hexad fixed space. -/
theorem nativeHexadFixedSpace_transport (g : actionGroup) (B : Finset (Fin 22))
    (v : BinarySpace) (hv : v ∈ nativeHexadFixedSpace B) :
    binaryAction g v ∈ nativeHexadFixedSpace (pointAction g • B) := by
  intro k hk
  obtain ⟨j,hj,rfl⟩ := (nativeHexadTwoCore_map_conj g B).ge hk
  change binaryAction (g*j*g⁻¹) (binaryAction g v) = binaryAction g v
  rw [←Module.End.mul_apply,←map_mul]
  simp only [mul_assoc,inv_mul_cancel,mul_one]
  rw [map_mul,Module.End.mul_apply,hv j hj]

/-- Linear transport uses the same matrix and actual two-core, with no abstract marking. -/
def nativeHexadFixedSpaceEquiv (g : actionGroup) (B : Finset (Fin 22)) :
    nativeHexadFixedSpace B ≃ₗ[ZMod 2] nativeHexadFixedSpace (pointAction g • B) :=
  { (binaryAction g).restrict (nativeHexadFixedSpace_transport g B) with
    invFun := fun v => ⟨binaryAction g⁻¹ v.val,by
      have hh := nativeHexadFixedSpace_transport g⁻¹ (pointAction g • B) v.val v.property
      rw [map_inv,inv_smul_smul] at hh
      exact hh⟩
    left_inv := by
      intro v
      apply Subtype.ext
      change (binaryAction g⁻¹ * binaryAction g) v.val = v.val
      rw [←map_mul,inv_mul_cancel,map_one]
      rfl
    right_inv := by
      intro v
      apply Subtype.ext
      change (binaryAction g * binaryAction g⁻¹) v.val = v.val
      rw [←map_mul,mul_inv_cancel,map_one]
      rfl }

/-- A triple-cover element carries the standard hexad to any native hexad. -/
theorem nativeHexad_transporter {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    ∃ g : M22TripleCover, pointAction (coverInclusion g) • m22Hexad123 = B := by
  obtain ⟨g,hg⟩ := exists_smul_m22Hexad123_eq hB
  obtain ⟨a,ha⟩ := M22TripleCover.Uniqueness.quotientMap_surjective g
  refine ⟨a,?_⟩
  rw [pointAction_cover]
  change (M22TripleCover.Uniqueness.quotientMap a).val • m22Hexad123 = B
  rw [ha]
  exact hg

/-- Only the standard native hexad requires a coordinate calculation. -/
theorem nativeHexadFixedSpace_data_of_standard
    (hc : Nat.card (nativeHexadFixedSpace m22Hexad123)=64)
    (hs : ∀ v ∈ nativeHexadFixedSpace m22Hexad123, Unitary.quadraticForm v=0)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    Nat.card (nativeHexadFixedSpace B)=64 ∧
      ∀ v ∈ nativeHexadFixedSpace B, Unitary.quadraticForm v=0 := by
  obtain ⟨g,hg⟩ := nativeHexad_transporter hB
  let f := nativeHexadFixedSpaceEquiv (coverInclusion g) m22Hexad123
  have he : Nat.card (nativeHexadFixedSpace m22Hexad123) =
      Nat.card (nativeHexadFixedSpace B) := by
    rw [←hg]
    exact Nat.card_congr f.toEquiv
  refine ⟨he.symm.trans hc,?_⟩
  intro v hv
  have hv' : v ∈ nativeHexadFixedSpace (pointAction (coverInclusion g) • m22Hexad123) := by
    rwa [hg]
  obtain ⟨u,hu⟩ := f.surjective ⟨v,hv'⟩
  have huv : M22TripleCover.binaryRepresentation g u.val = v := congrArg Subtype.val hu
  rw [←huv,Unitary.quadraticForm_invariant]
  exact hs u.val u.property


end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
end
