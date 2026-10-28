module

public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.M11Exclusion.Actors
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.M11Exclusion.Inputs
public import Theory.Representation.Quotient

/-!
# Assembly of the M11 degree-window exclusion

The source cubic actor has rank two and codimension four. After removing the
central cover and recognizing the component's degree-at-most-twelve module,
the marked point-module geometry contradicts that codimension. The recognition
is pulled back along the literal component isomorphism, so the geometry sees
the original ambient group and its normal component.

All three outstanding inputs are explicit below. This conditional assembly is
not the unconditional `boundedSourceExclusion_m11` source theorem.
Source: Aschbacher--Smith K.4, printed p.457, citing Guralnick--Malle,
Classification of 2F-modules I, Theorem 6.6 and Table 6.7.
-/

public section
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue
open Theory.GroupTheory Subgroup Representation.BinaryOffender
open _root_.Sporadic.Mathieu Representation.MathieuSmall.M12Recognition
universe u v

/-- The M11 window is excluded once its actual central covers, low-degree
representations and marked point geometry have been determined independently. -/
theorem boundedSourceExclusion_m11_of_inputs
    (hcover : ∀ {L : Type u} [Group L] [Finite L] [IsQuasisimple L],
      (L ⧸ center L ≃* M11) → center L = ⊥)
    (hrecognition : M11Exclusion.SmallDegreeRecognition.{v})
    (hgeometry : M11Exclusion.RankTwoPointGeometry.{u,v}) :
    BoundedSourceExclusion.{u,v} .m11 12 := by
  intro G V _ _ _ _ _ ρ h he hd
  obtain ⟨e⟩ := he
  let L := generalizedFitting G
  let := h.quasisimple
  have hZ : center L = ⊥ := hcover e
  let c : L ≃* M11 :=
    ((QuotientGroup.quotientBot (G := L)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans e
  let σ : Representation (ZMod 2) M11 V :=
    (ρ.comp L.subtype).comp c.symm.toMonoidHom
  have hf : Function.Injective σ :=
    h.faithful.comp (Subtype.val_injective.comp c.symm.injective)
  have hi : σ.IsIrreducible :=
    (Representation.irreducible_comp_surjective_iff c.symm.toMonoidHom c.symm.surjective
      (ρ.comp L.subtype)).mpr h.irreducible
  obtain ⟨E⟩ := hrecognition σ hf hi hd
  have hmarked : Nonempty (Representation.Equiv (ρ.comp L.subtype)
      (pointRepresentation.comp c.toMonoidHom)) := by
    refine ⟨.mk E.toLinearEquiv ?_⟩
    intro l
    simpa only [σ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply] using E.isIntertwining' (c l)
  obtain ⟨A, hA, _, hr, ha, hAL, _⟩ := m11_cubic_actor ρ h e
  have hb := hgeometry ρ L c h.faithful hmarked A hA hr hAL
  omega

end CFSG.Quasithin.ChapterK.SporadicCatalogue
