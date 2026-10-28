module
public import Theory.Representation.BinaryOffender.CubicCenterSections
public import Theory.Representation.BinaryOffender.Homogeneous.TypeSelection
public import Theory.Representation.BinaryOffender.ActionImage

/-!
# Homogeneous constituents detecting a cubic center

If the actual image of a binary actor is quasisimple with center of order
three, a homogeneous Irr⁺ constituent detects its full action kernel.
Choose a center-faithful constituent in the image and lift through the
literal action map. Type-preserving homogeneous selection retains its
central-quotient kernel, hence also detects every actor fixing the chosen
space pointwise.

This is the A.1.42 selection used in the kernel comparison of
Aschbacher--Smith 13.4.5(4), printed p.898. The application to the original
reduced module is in FixedCoreSource/Amalgam/CoveredSelection.
-/

public section
open Subgroup Theory.GroupTheory Representation
namespace Representation.BinaryOffender
open Homogeneous
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

/-- Homogeneous selection preserves detection of the actual action kernel. -/
theorem exists_homogeneous_detecting_cubic_image
    (K P : Subgroup G) (hPK : P ≤ normalizer (K : Set G)) (hP : IsPGroup 2 P)
    [IsQuasisimple (actionSubgroup ρ K)]
    (hc : Nat.card (center (actionSubgroup ρ K)) = 3) :
    ∃ J : Submodule (ZMod 2) V, IsIrrPlusWith ρ K P J ∧
      ∀ k : K, (∀ v ∈ J, ρ k v = v) → ρ k = 1 := by
  let σ := imageRepresentation ρ
  let f := actionHom ρ
  let Kq := actionSubgroup ρ K
  obtain ⟨I,hi,hfaith⟩ := exists_faithful_isIrrPlus_of_cubic_center σ Kq
    ((imageRepresentation_injective ρ).comp Kq.subtype_injective) hc
  have hI : IsIrrPlus ρ K I := by
    have hh := IsIrrPlus.map_embedding ρ σ f (LinearMap.id : V →ₗ[ZMod 2] V)
      Function.injective_id (fun _ _ => rfl) K I hi
    simpa only [Submodule.map_id] using hh
  obtain ⟨J,_,hJ,e,he⟩ := exists_isIrrPlusWith_le_orbitSpan_sameModule ρ hPK hP hI
  refine ⟨J,hJ,?_⟩
  intro k hk
  have hJfix : (quotientImage ρ K J hJ.invariant).toRepresentation k = 1 := by
    apply LinearMap.ext
    rintro ⟨v,w,hw,rfl⟩
    apply Subtype.ext
    change (fixedSpace ρ K).mkQ (ρ k w) = (fixedSpace ρ K).mkQ w
    rw [hk w hw]
  have hIfix : (quotientImage ρ K I hI.choose).toRepresentation k = 1 := by
    apply LinearMap.ext
    intro v
    apply e.injective
    rw [he,hJfix]
    rfl
  have hcentral : centralQuotientRepresentation ρ K I hI.choose k = 1 := by
    apply LinearMap.ext
    intro v
    apply (centralQuotientImageEquiv ρ K I).injective
    rw [centralQuotientImageEquiv_equivariant,hIfix]
    rfl
  have hq : centralQuotientRepresentation σ Kq I hi.choose (f.subgroupMap K k) = 1 := by
    apply (centralSectionRepresentation_ker_iff σ Kq Kq I hi.choose Kq.le_normalizer _).mpr
    intro v hv
    have hh := (centralSectionRepresentation_ker_iff ρ K K I hI.choose K.le_normalizer k).mp
      hcentral v hv
    change σ (f k) v - v ∈ fixedSpace σ (actionSubgroup ρ K)
    rw [fixedSpace_actionSubgroup]
    exact hh
  have hf : f.subgroupMap K k = 1 := hfaith (hq.trans (map_one _).symm)
  have hf' : f k = 1 := congrArg Subtype.val hf
  exact congrArg σ hf'
end Representation.BinaryOffender
