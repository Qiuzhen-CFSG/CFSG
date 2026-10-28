module

public import Theory.SpecificGroups.ReeTwo.ParabolicLinearAction.Translations

/-!
# Restricting the marked Ree action to the character kernels

For a subgroup L, the action kernel is the relative subgroup C_H(E) ∩ L.
The induced quotient representation remains injective. If L contains the
embedded characteristic omega subgroup, the core intersection still maps
onto the whole translation kernel, by the explicit preimages constructed in
`Translations`. All three specified binary-character kernels satisfy this
containment, giving their quotient images without an ambient identification.

When E lies in L, the action kernel is also explicitly identified with the
centralizer of E inside L. Normality and quotients are therefore relative to
L throughout.

Source: the local linear calculation in Aschbacher--Smith, Lemma 14.2.21,
printed p.989, and Aschbacher (1982), Section 3. These are intrinsic results
about the specified character kernels, not identifications with Tits subgroups.
-/

public section

open Subgroup Theory.LinearAlgebra.BinaryFivePointStabilizer
namespace ReeTwo.Centralizer

/-- The relative derived centralizer, as a subgroup of the restricted actor. -/
abbrev derivedCentralizerIn (L : Subgroup Centralizer) : Subgroup L :=
  (centralizer (derived : Set Centralizer)).subgroupOf L

/-- Restricting the actor intersects its actual action kernel with that actor. -/
theorem restrictedMarkedRepresentation_ker (L : Subgroup Centralizer) :
    (markedRepresentation.comp L.subtype).ker = derivedCentralizerIn L := by
  rw [← MonoidHom.comap_ker, markedRepresentation_ker]
  rfl

/-- The actual faithful quotient representation for any restricted actor. -/
def restrictedFaithfulMarkedRepresentation (L : Subgroup Centralizer) :
    L ⧸ derivedCentralizerIn L →* stabilizer markedVector :=
  QuotientGroup.lift _ (markedRepresentation.comp L.subtype)
    (le_of_eq (restrictedMarkedRepresentation_ker L).symm)

/-- The quotient representation retains the original action formula. -/
theorem restrictedFaithfulMarkedRepresentation_mk (L : Subgroup Centralizer) (g : L) :
    restrictedFaithfulMarkedRepresentation L (QuotientGroup.mk' _ g) =
      markedRepresentation g := by rfl

/-- Faithfulness follows from the computed relative kernel. -/
theorem restrictedFaithfulMarkedRepresentation_injective (L : Subgroup Centralizer) :
    Function.Injective (restrictedFaithfulMarkedRepresentation L) :=
  (QuotientGroup.injective_lift_iff _ _ _).mpr (restrictedMarkedRepresentation_ker L).symm

/-- If the derived subgroup is contained in L, this is precisely its centralizer in L. -/
theorem derivedCentralizerIn_eq_centralizer (L : Subgroup Centralizer) (hL : derived ≤ L) :
    derivedCentralizerIn L = centralizer (derived.subgroupOf L : Set L) := by
  ext g
  change (g : Centralizer) ∈ centralizer (derived : Set Centralizer) ↔ _
  rw [mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro h x hx
    apply Subtype.ext
    exact h x hx
  · intro h x hx
    exact congrArg Subtype.val (h ⟨x,hL hx⟩ hx)

/-- The relative action kernel lies in the relative core. -/
theorem derivedCentralizerIn_le_core (L : Subgroup Centralizer) :
    derivedCentralizerIn L ≤ core.subgroupOf L := by
  intro g hg
  exact derivedCentralizer_le_core hg

/-- The relative core still has the full translation image when it contains omega. -/
theorem restricted_core_markedRepresentation_image (L : Subgroup Centralizer)
    (hL : (omega₁ Core (p := 2)).map
      (SemidirectProduct.inl : Core →* Centralizer) ≤ L) :
    (core.subgroupOf L).map (markedRepresentation.comp L.subtype) = kernel markedVector := by
  apply le_antisymm
  · rintro _ ⟨g,hg,rfl⟩
    obtain ⟨x,hx⟩ := hg
    change markedRepresentation (g : Centralizer) ∈ _
    change SemidirectProduct.inl x = (g : Centralizer) at hx
    rw [← hx]
    exact markedRepresentation_core_mem_kernel x
  · intro g hg
    let x := kernelCoreRepresentative g
    have hxL : (SemidirectProduct.inl x : Centralizer) ∈ L :=
      hL (mem_map_of_mem _ (kernelCoreRepresentative_mem_omega g))
    refine ⟨⟨SemidirectProduct.inl x,hxL⟩, ⟨x,rfl⟩, ?_⟩
    exact markedRepresentation_kernel_preimage g hg

/-- The faithful quotient map identifies the relative Q/F with the translation kernel. -/
theorem restricted_core_quotient_markedRepresentation_image (L : Subgroup Centralizer)
    (hL : (omega₁ Core (p := 2)).map
      (SemidirectProduct.inl : Core →* Centralizer) ≤ L) :
    ((core.subgroupOf L).map (QuotientGroup.mk' (derivedCentralizerIn L))).map
      (restrictedFaithfulMarkedRepresentation L) = kernel markedVector := by
  rw [Subgroup.map_map]
  exact restricted_core_markedRepresentation_image L hL

/-- The parity kernel contains the embedded characteristic omega subgroup. -/
theorem omega_le_parity_kernel : (omega₁ Core (p := 2)).map
    (SemidirectProduct.inl : Core →* Centralizer) ≤ character.ker := by
  rintro _ ⟨x,_,rfl⟩
  change character (SemidirectProduct.inl x) = 1
  simp [character]

/-- The core-character kernel contains the embedded characteristic omega subgroup. -/
theorem omega_le_coreCharacter_kernel : (omega₁ Core (p := 2)).map
    (SemidirectProduct.inl : Core →* Centralizer) ≤ coreCharacter.ker := by
  rintro _ ⟨x,hx,rfl⟩
  change Core.binaryCharacter x = 1
  exact (show x ∈ Core.binaryCharacter.ker from Core.binaryCharacter_ker_eq_omega.symm ▸ hx)

/-- The mixed-character kernel contains the embedded characteristic omega subgroup. -/
theorem omega_le_mixedCharacter_kernel : (omega₁ Core (p := 2)).map
    (SemidirectProduct.inl : Core →* Centralizer) ≤ mixedCharacter.ker := by
  intro x hx
  have hp := omega_le_parity_kernel hx
  have hc := omega_le_coreCharacter_kernel hx
  change character x = 1 at hp
  change coreCharacter x = 1 at hc
  change mixedCharacter x = 1
  simp [mixedCharacter,hp,hc]

/-- All three specified character kernels have the full translation quotient image. -/
theorem character_kernel_core_quotient_image
    (χ : Centralizer →* FiveFour.Cyclic 2)
    (hχ : χ = character ∨ χ = coreCharacter ∨ χ = mixedCharacter) :
    ((core.subgroupOf χ.ker).map (QuotientGroup.mk' (derivedCentralizerIn χ.ker))).map
      (restrictedFaithfulMarkedRepresentation χ.ker) = kernel markedVector := by
  apply restricted_core_quotient_markedRepresentation_image
  rcases hχ with rfl | rfl | rfl
  · exact omega_le_parity_kernel
  · exact omega_le_coreCharacter_kernel
  · exact omega_le_mixedCharacter_kernel

end ReeTwo.Centralizer
