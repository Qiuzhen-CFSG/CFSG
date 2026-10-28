module

public import Theory.GroupTheory.ReducedNormal.SubspaceEquiv
public import Theory.Representation.BinaryOffender.Homogeneous.Embedding
public import Theory.Representation.BinaryOffender.Homogeneous.OrbitConsequences
public import Mathlib.RepresentationTheory.Intertwining

/-!
# Orbit seeds on the actual ambient subgroup

An Irr⁺ seed and its generating orbit retain their properties when the
module is written as its actual subgroup of G. Applying D.3.4 to these
coordinates and transporting through the original quotient projection
proves semisimplicity on the literal group centralizer quotient.

Source: Aschbacher–Smith, Lemma 3.2.2(3), combined manuscript of
1 March 2004, printed p.579.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
namespace Theory.GroupTheory.ReducedNormal
variable {G : Type*} [Group G] (H : Subgroup G)
  (W : Submodule (ZMod 2) (Additive (ModuleGroup H)))

/-- The actual seed inside the subgroup coordinates. -/
noncomputable def imageSeed (I : Submodule (ZMod 2) (Additive (ModuleGroup H))) :
    Submodule (ZMod 2) (Additive (subspaceImage H W)) :=
  (I.comap W.subtype).map (subspaceEquiv H W).toLinearMap

/-- Irr⁺ is unchanged when the orbit module is written as its literal subgroup. -/
theorem imageSeed_isIrrPlus
    (hW : (⊤ : Subgroup H) ≤ subspaceStabilizer (representation H) W)
    {X : Subgroup H} {I : Submodule (ZMod 2) (Additive (ModuleGroup H))}
    (hI : IsIrrPlus (representation H) X I) (hIW : I ≤ W) :
    IsIrrPlus (subspaceRepresentation H W hW) X (imageSeed H W I) := by
  let τ : Representation (ZMod 2) H W := (subspaceSubrepresentation H W hW).toRepresentation
  have hi : IsIrrPlus τ X (I.comap W.subtype) := by
    apply hI.of_intertwining (representation H) τ (MonoidHom.id X)
      Function.surjective_id W.subtype W.subtype_injective (fun _ _ => rfl)
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hIW]
  have hm := hi.map_equivariant_embedding τ (subspaceRepresentation H W hW)
    (MonoidHom.id H) (subspaceEquiv H W).toLinearMap
    (subspaceEquiv_equivariant H W hW) (subspaceEquiv H W).injective
  simpa only [Subgroup.map_id, imageSeed] using hm

/-- The seed's full orbit fills the literal subgroup module. -/
theorem imageSeed_orbitSpan_eq_top
    (hW : (⊤ : Subgroup H) ≤ subspaceStabilizer (representation H) W)
    (I : Submodule (ZMod 2) (Additive (ModuleGroup H)))
    (hgen : orbitSpan (representation H) ⊤ I = W) :
    orbitSpan (subspaceRepresentation H W hW) ⊤ (imageSeed H W I) = ⊤ := by
  let τ : Representation (ZMod 2) H W := (subspaceSubrepresentation H W hW).toRepresentation
  have hIW : I ≤ W := hgen ▸ le_orbitSpan (representation H) ⊤ I
  have hr : orbitSpan τ ⊤ (I.comap W.subtype) = ⊤ := by
    apply Submodule.map_injective_of_injective W.subtype_injective
    rw [orbitSpan_map_equivariant τ (representation H) (MonoidHom.id H) W.subtype
      (fun _ _ => rfl), Subgroup.map_id, Submodule.map_comap_subtype,
      inf_eq_right.mpr hIW, hgen, Submodule.map_top, Submodule.range_subtype]
  have hm := orbitSpan_map_equivariant τ (subspaceRepresentation H W hW)
    (MonoidHom.id H) (subspaceEquiv H W).toLinearMap
    (subspaceEquiv_equivariant H W hW) ⊤ (I.comap W.subtype)
  rw [Subgroup.map_id, hr, Submodule.map_top,
    LinearMap.range_eq_top.mpr (subspaceEquiv H W).surjective] at hm
  exact hm.symm

private theorem semisimple_of_equivariant_equiv
    {D V U : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup U] [Module (ZMod 2) U]
    {ρ : Representation (ZMod 2) D V} {σ : Representation (ZMod 2) D U}
    (e : V ≃ₗ[ZMod 2] U) (he : ∀ g v, e (ρ g v) = σ g (e v))
    (hs : Representation.IsSemisimpleRepresentation ρ) :
    Representation.IsSemisimpleRepresentation σ := by
  let a : ρ.IntertwiningMap σ := ⟨e.toLinearMap, fun g => LinearMap.ext (he g)⟩
  let b := Representation.IntertwiningMap.equivLinearMapAsModule ρ σ a
  have hb : Function.Bijective b := e.bijective
  apply (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule σ).mpr
  apply (LinearEquiv.ofBijective b hb).isSemisimpleModule_iff.mp
  exact (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mp hs

/-- The source semisimplicity assertion on the literal group centralizer quotient. -/
theorem centralizerQuotient_semisimple
    (hW : (⊤ : Subgroup H) ≤ subspaceStabilizer (representation H) W)
    (X : Subgroup G) (hXH : X ≤ H) [(X.subgroupOf H).Normal]
    {I : Submodule (ZMod 2) (Additive (ModuleGroup H))}
    (hI : IsIrrPlus (representation H) (X.subgroupOf H) I)
    (hgen : orbitSpan (representation H) ⊤ I = W) :
    Representation.IsSemisimpleRepresentation
      (centralizerQuotientRepresentation H W hW X hXH) := by
  have hi := imageSeed_isIrrPlus H W hW hI (hgen ▸ le_orbitSpan _ ⊤ I)
  have hg := imageSeed_orbitSpan_eq_top H W hW I hgen
  have hs := fixedQuotient_semisimple_of_orbitSpan_eq_top
    (subspaceRepresentation H W hW) (by rw [normalizer_eq_top]) hi hg
  apply semisimple_of_equivariant_equiv (fixedSpaceQuotientEquiv H W hW X hXH) _ hs
  intro g v
  change _ = (fixedSpaceQuotientEquiv H W hW X hXH)
    ((fixedQuotientRepresentation (subspaceRepresentation H W hW) (X.subgroupOf H)) g
      ((fixedSpaceQuotientEquiv H W hW X hXH).symm
      (fixedSpaceQuotientEquiv H W hW X hXH v)))
  rw [LinearEquiv.symm_apply_apply]

end Theory.GroupTheory.ReducedNormal
