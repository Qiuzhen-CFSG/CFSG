module

public import Theory.SpecificGroups.ReeTwo.ParabolicLinearAction.Basic
public import Mathlib.LinearAlgebra.StdBasis
public import Theory.SpecificGroups.ReeTwo.CoreParabolicOmega

/-!
# Core conjugation is exactly the binary translation subgroup

Conjugating a tail vector by a core element changes only the last coordinate,
by the pairing between its first four tail coordinates and the four head
coordinates detected by the derived centralizer. Conversely, a point-stabilizer
kernel element fixes those four coordinates. Its values on the corresponding
basis vectors give an explicit core preimage. The unused middle coordinate is
chosen so that this preimage also lies in the characteristic omega subgroup.
Thus both cores have the entire displacement kernel as their actual image.

Source: Aschbacher--Smith, Lemma 14.2.21, printed p.989, and Aschbacher (1982),
Section 3, calculated in the verified Shinoda root-coordinate model.
-/

@[expose] public section

open Subgroup Theory.LinearAlgebra.BinaryFivePointStabilizer
namespace ReeTwo.Centralizer

/-- The exact core conjugation formula in the ordered derived coordinates. -/
theorem derivedLinearAction_core (x : Core) (v : DerivedSpace) :
    derivedLinearAction (SemidirectProduct.inl x) v =
      ![v 0, v 1, v 2, v 3,
        v 4 + x.b4 * v 0 + x.b3 * v 1 + x.b1 * v 2 + x.b0 * v 3] := by
  let w : DerivedSpace := ![v 0, v 1, v 2, v 3,
    v 4 + x.b4 * v 0 + x.b3 * v 1 + x.b1 * v 2 + x.b0 * v 3]
  have hc : derivedAction (SemidirectProduct.inl x)
      (Core.derivedCoordinates.symm (Multiplicative.ofAdd v)) =
        Core.derivedCoordinates.symm (Multiplicative.ofAdd w) := by
    apply Subtype.ext
    change x * (Core.derivedCoordinates.symm (Multiplicative.ofAdd v) : Core) * x⁻¹ =
      (Core.derivedCoordinates.symm (Multiplicative.ofAdd w) : Core)
    apply (mul_inv_eq_iff_eq_mul).mpr
    change Core.mul x ⟨0,0,0,0,0,v 0,v 1,v 2,v 3,v 4⟩ =
      Core.mul ⟨0,0,0,0,0,v 0,v 1,v 2,v 3,
        v 4 + x.b4 * v 0 + x.b3 * v 1 + x.b1 * v 2 + x.b0 * v 3⟩ x
    apply Core.ext <;> simp [Core.mul] <;> ring_nf
    reduce_mod_char
  rw [derivedLinearAction_apply, hc, Core.derivedCoordinates.apply_symm_apply]
  rfl

/-- Core conjugation acts trivially modulo the marked line. -/
theorem markedRepresentation_core_mem_kernel (x : Core) :
    markedRepresentation (SemidirectProduct.inl x) ∈ kernel markedVector := by
  apply (mem_kernel_iff _ _).mpr
  intro v
  change derivedLinearAction (SemidirectProduct.inl x) v - v ∈ line markedVector
  rw [derivedLinearAction_core]
  apply Submodule.mem_span_singleton.mpr
  refine ⟨x.b4 * v 0 + x.b3 * v 1 + x.b1 * v 2 + x.b0 * v 3, ?_⟩
  funext i
  fin_cases i <;> simp [markedVector]
  ring

private theorem kernel_preserves_head (g : stabilizer markedVector)
    (hg : g ∈ kernel markedVector) (v : DerivedSpace) (i : Fin 4) :
    g.val v i.castSucc = v i.castSucc := by
  obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp ((mem_kernel_iff _ _).mp hg v)
  have hi := congrFun ha i.castSucc
  have hz : markedVector i.castSucc = 0 := by fin_cases i <;> rfl
  change a * markedVector i.castSucc = g.val v i.castSucc - v i.castSucc at hi
  rw [hz, mul_zero] at hi
  exact sub_eq_zero.mp hi.symm

/-- A specified core preimage, read from the last coordinates of four basis images.
The middle coordinate puts it in the characteristic index-two core as well. -/
def kernelCoreRepresentative (g : stabilizer markedVector) : Core :=
  ⟨(g.val (Pi.single 3 1)) 4, (g.val (Pi.single 2 1)) 4,
   (g.val (Pi.single 2 1)) 4 + (g.val (Pi.single 1 1)) 4,
   (g.val (Pi.single 1 1)) 4, (g.val (Pi.single 0 1)) 4, 0,0,0,0,0⟩

/-- Every displacement-kernel element is realized by its specified core preimage. -/
theorem markedRepresentation_kernel_preimage (g : stabilizer markedVector)
    (hg : g ∈ kernel markedVector) :
    markedRepresentation (SemidirectProduct.inl (kernelCoreRepresentative g)) = g := by
  apply Subtype.ext
  apply (Pi.basisFun (ZMod 2) (Fin 5)).ext'
  intro i
  rw [Pi.basisFun_apply]
  change derivedLinearAction (SemidirectProduct.inl (kernelCoreRepresentative g))
    (Pi.single i 1) = g.val (Pi.single i 1)
  rw [derivedLinearAction_core]
  funext j
  fin_cases j
  · exact (kernel_preserves_head g hg (Pi.single i 1) 0).symm
  · exact (kernel_preserves_head g hg (Pi.single i 1) 1).symm
  · exact (kernel_preserves_head g hg (Pi.single i 1) 2).symm
  · exact (kernel_preserves_head g hg (Pi.single i 1) 3).symm
  · fin_cases i <;> simp [kernelCoreRepresentative]
    have hm : Pi.single (4 : Fin 5) (1 : ZMod 2) = markedVector := by
      ext j
      fin_cases j <;> decide
    rw [hm, g.property]
    rfl

/-- The specified preimage lies in the characteristic omega subgroup. -/
theorem kernelCoreRepresentative_mem_omega (g : stabilizer markedVector) :
    kernelCoreRepresentative g ∈ omega₁ Core (p := 2) := by
  rw [← Core.binaryCharacter_ker_eq_omega]
  change Core.binaryCharacter (kernelCoreRepresentative g) = 1
  apply congrArg Multiplicative.ofAdd
  change (g.val (Pi.single 2 1)) 4 +
    ((g.val (Pi.single 2 1)) 4 + (g.val (Pi.single 1 1)) 4) +
    (g.val (Pi.single 1 1)) 4 = 0
  ring_nf
  reduce_mod_char

/-- The full core maps onto the actual point-stabilizer displacement kernel. -/
theorem core_markedRepresentation_image : core.map markedRepresentation = kernel markedVector := by
  apply le_antisymm
  · rintro _ ⟨g,⟨x,rfl⟩,rfl⟩
    exact markedRepresentation_core_mem_kernel x
  · intro g hg
    exact ⟨SemidirectProduct.inl (kernelCoreRepresentative g),
      ⟨kernelCoreRepresentative g,rfl⟩,markedRepresentation_kernel_preimage g hg⟩

/-- The characteristic index-two core has the same full translation image. -/
theorem omega_markedRepresentation_image :
    ((omega₁ Core (p := 2)).map (SemidirectProduct.inl : Core →* Centralizer)).map
      markedRepresentation = kernel markedVector := by
  apply le_antisymm
  · rintro _ ⟨g,⟨x,_,rfl⟩,rfl⟩
    exact markedRepresentation_core_mem_kernel x
  · intro g hg
    exact ⟨SemidirectProduct.inl (kernelCoreRepresentative g),
      mem_map_of_mem _ (kernelCoreRepresentative_mem_omega g),
      markedRepresentation_kernel_preimage g hg⟩

/-- Under the faithful quotient representation, the actual Q/F is exactly the kernel. -/
theorem core_quotient_markedRepresentation_image :
    (core.map (QuotientGroup.mk' (centralizer (derived : Set Centralizer)))).map
      faithfulMarkedRepresentation = kernel markedVector := by
  rw [Subgroup.map_map]
  exact core_markedRepresentation_image

end ReeTwo.Centralizer
