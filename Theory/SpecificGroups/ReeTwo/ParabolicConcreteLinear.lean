module
public import Theory.SpecificGroups.ReeTwo.ParabolicConcreteStructure

/-!
# Marked linear actions of the actual first parabolics

Conjugation on the derived subgroup is written in the verified five binary
root coordinates. The coordinate embedding is onto the actual E and sends
the marked vector to the source central involution. The action kernels are
the actual centralizers F. The faithful quotient representations identify
Q/F with the whole translation subgroup of the point stabilizer, using the
explicit coordinate representatives, not recognition by cardinality.

Source: Aschbacher--Smith 14.2.21, p.989; Aschbacher (1982), Section 3.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.LinearAlgebra.BinaryFivePointStabilizer
namespace ReeTwo.ParabolicConcrete
open Centralizer Centralizer.IndexTwo ParabolicMarkedComparison
open Tits.ExceptionalParabolics

/-- Derived coordinates in the actual full-Ree parabolic. -/
def reeDerivedEmbedding : Multiplicative DerivedSpace →* FullRee.first :=
  Verified.firstEquiv.toMonoidHom.comp derivedEmbedding

/-- The same derived coordinates in the mixed kernel selected by the Tits comparison. -/
def mixedDerivedEmbedding : Multiplicative DerivedSpace →* mixedLocal :=
  derivedEmbedding.codRestrict mixedLocal (by
    intro v
    exact derived_le_omega.trans (omega_le_kernel mixedCharacter (Or.inr rfl))
      (derivedEmbedding_range ▸ (show derivedEmbedding v ∈ derivedEmbedding.range from ⟨v,rfl⟩)))

def titsDerivedEmbedding : Multiplicative DerivedSpace →* Tits.ExceptionalParabolics.first :=
  Verified.titsFirstEquiv.toMonoidHom.comp mixedDerivedEmbedding

theorem reeDerivedEmbedding_range : reeDerivedEmbedding.range = reeE := by
  rw [reeDerivedEmbedding, MonoidHom.range_comp, derivedEmbedding_range, reeE_eq]

theorem titsDerivedEmbedding_range : titsDerivedEmbedding.range = titsE := by
  rw [titsDerivedEmbedding, MonoidHom.range_comp]
  have h : mixedDerivedEmbedding.range = derived.subgroupOf mixedLocal := by
    ext x
    constructor
    · rintro ⟨v,rfl⟩
      exact derivedEmbedding_range ▸ (show derivedEmbedding v ∈ derivedEmbedding.range from ⟨v,rfl⟩)
    · intro hx
      obtain ⟨v,hv⟩ := derivedEmbedding_range.symm ▸ hx
      exact ⟨v,Subtype.ext hv⟩
  rw [h, titsE_eq]

theorem reeDerivedEmbedding_injective : Function.Injective reeDerivedEmbedding :=
  Verified.firstEquiv.injective.comp derivedEmbedding_injective

theorem titsDerivedEmbedding_injective : Function.Injective titsDerivedEmbedding := by
  intro x y h
  exact derivedEmbedding_injective (congrArg Subtype.val (Verified.titsFirstEquiv.injective h))

/-- The marked vector is the source's last root, in the actual full-Ree carrier. -/
theorem reeDerivedEmbedding_mark :
    (reeDerivedEmbedding (Multiplicative.ofAdd markedVector) : ReeF4.Model 0) = Ambient.root 9 := by
  change Verified.localMap (derivedEmbedding (Multiplicative.ofAdd markedVector)) = _
  rw [derivedEmbedding_mark, Verified.localMap_root]

/-- The marked vector is the source's distinguished Atlas involution in Tits. -/
theorem titsDerivedEmbedding_mark :
    (titsDerivedEmbedding (Multiplicative.ofAdd markedVector) : Tits.Atlas1600Group) =
      Tits.atlas1600R5 := Verified.titsFirstEquiv_last_root

def reeRepresentation : FullRee.first →* stabilizer markedVector :=
  markedRepresentation.comp Verified.firstEquiv.symm.toMonoidHom

def titsRepresentation : Tits.ExceptionalParabolics.first →* stabilizer markedVector :=
  (markedRepresentation.comp mixedLocal.subtype).comp Verified.titsFirstEquiv.symm.toMonoidHom

/-- The full-Ree representation is exactly conjugation on the embedded E. -/
theorem reeRepresentation_conjugation (g : FullRee.first) (v : DerivedSpace) :
    reeDerivedEmbedding (Multiplicative.ofAdd ((reeRepresentation g).val v)) =
      g * reeDerivedEmbedding (Multiplicative.ofAdd v) * g⁻¹ := by
  obtain ⟨x,rfl⟩ := Verified.firstEquiv.surjective g
  change Verified.firstEquiv (derivedEmbedding
    (Multiplicative.ofAdd (derivedLinearAction
      (Verified.firstEquiv.symm (Verified.firstEquiv x)) v))) = _
  rw [Verified.firstEquiv.symm_apply_apply, derivedEmbedding_action, map_mul, map_mul, map_inv]
  rfl

/-- The Tits representation is exactly conjugation on its embedded E. -/
theorem titsRepresentation_conjugation (g : Tits.ExceptionalParabolics.first) (v : DerivedSpace) :
    titsDerivedEmbedding (Multiplicative.ofAdd ((titsRepresentation g).val v)) =
      g * titsDerivedEmbedding (Multiplicative.ofAdd v) * g⁻¹ := by
  obtain ⟨x,rfl⟩ := Verified.titsFirstEquiv.surjective g
  change Verified.titsFirstEquiv (mixedDerivedEmbedding _) =
    Verified.titsFirstEquiv x * Verified.titsFirstEquiv (mixedDerivedEmbedding _) *
      (Verified.titsFirstEquiv x)⁻¹
  rw [← map_inv, ← map_mul, ← map_mul]
  apply congrArg Verified.titsFirstEquiv
  apply Subtype.ext
  change derivedEmbedding (Multiplicative.ofAdd (derivedLinearAction
    (Verified.titsFirstEquiv.symm (Verified.titsFirstEquiv x)) v)) = _
  rw [Verified.titsFirstEquiv.symm_apply_apply]
  exact derivedEmbedding_action x v

theorem reeRepresentation_ker : reeRepresentation.ker = reeF := by
  rw [reeRepresentation, ← MonoidHom.comap_ker, markedRepresentation_ker]
  exact (Subgroup.map_equiv_eq_comap_symm Verified.firstEquiv _).symm.trans reeF_eq

theorem titsRepresentation_ker : titsRepresentation.ker = titsF := by
  rw [titsRepresentation, ← MonoidHom.comap_ker, restrictedMarkedRepresentation_ker]
  exact (Subgroup.map_equiv_eq_comap_symm Verified.titsFirstEquiv _).symm.trans titsF_eq

/-- The actual quotient H/F acts faithfully in the stabilizer of the marked vector. -/
def reeFaithfulRepresentation : (FullRee.first ⧸ reeF) →* stabilizer markedVector :=
  QuotientGroup.lift _ reeRepresentation (by rw [reeRepresentation_ker])

def titsFaithfulRepresentation : (Tits.ExceptionalParabolics.first ⧸ titsF) →*
    stabilizer markedVector :=
  QuotientGroup.lift _ titsRepresentation (by rw [titsRepresentation_ker])

@[simp] theorem reeFaithfulRepresentation_mk (g : FullRee.first) :
    reeFaithfulRepresentation (QuotientGroup.mk' _ g) = reeRepresentation g := rfl

@[simp] theorem titsFaithfulRepresentation_mk (g : Tits.ExceptionalParabolics.first) :
    titsFaithfulRepresentation (QuotientGroup.mk' _ g) = titsRepresentation g := rfl

theorem reeFaithfulRepresentation_injective : Function.Injective reeFaithfulRepresentation :=
  (QuotientGroup.injective_lift_iff _ _ _).mpr reeRepresentation_ker.symm

theorem titsFaithfulRepresentation_injective : Function.Injective titsFaithfulRepresentation :=
  (QuotientGroup.injective_lift_iff _ _ _).mpr titsRepresentation_ker.symm

/-- The core image is the complete translation subgroup, via the verified coordinate preimages. -/
theorem ree_core_representation_image : reeQ.map reeRepresentation = kernel markedVector := by
  rw [reeQ, ← Verified.firstEquiv_core, Subgroup.map_map]
  have h : reeRepresentation.comp Verified.firstEquiv.toMonoidHom = markedRepresentation := by
    apply MonoidHom.ext
    intro g
    exact congrArg markedRepresentation (Verified.firstEquiv.symm_apply_apply g)
  rw [h]
  exact core_markedRepresentation_image

theorem tits_core_representation_image : titsQ.map titsRepresentation = kernel markedVector := by
  rw [titsQ, ← Verified.titsFirstEquiv_core, Subgroup.map_map]
  have h : titsRepresentation.comp Verified.titsFirstEquiv.toMonoidHom =
      markedRepresentation.comp mixedLocal.subtype := by
    apply MonoidHom.ext
    intro g
    exact congrArg (fun x : mixedLocal => markedRepresentation x)
      (Verified.titsFirstEquiv.symm_apply_apply g)
  rw [h]
  exact restricted_core_markedRepresentation_image mixedLocal omega_le_mixedCharacter_kernel

theorem ree_translation_image :
    (reeQ.map (QuotientGroup.mk' reeF)).map reeFaithfulRepresentation = kernel markedVector := by
  rw [Subgroup.map_map]
  exact ree_core_representation_image

theorem tits_translation_image :
    (titsQ.map (QuotientGroup.mk' titsF)).map titsFaithfulRepresentation = kernel markedVector := by
  rw [Subgroup.map_map]
  exact tits_core_representation_image

theorem ree_core_image_eq_pCore :
    (reeQ.map (QuotientGroup.mk' reeF)).map reeFaithfulRepresentation =
      pCore 2 (stabilizer markedVector) := by
  rw [pCore_eq_kernel markedVector markedVector_ne_zero derivedSpace_finrank]
  exact ree_translation_image

theorem tits_core_image_eq_pCore :
    (titsQ.map (QuotientGroup.mk' titsF)).map titsFaithfulRepresentation =
      pCore 2 (stabilizer markedVector) := by
  rw [pCore_eq_kernel markedVector markedVector_ne_zero derivedSpace_finrank]
  exact tits_translation_image

end ReeTwo.ParabolicConcrete
