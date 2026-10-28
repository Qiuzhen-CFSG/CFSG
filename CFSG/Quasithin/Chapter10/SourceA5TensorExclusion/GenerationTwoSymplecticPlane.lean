module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticNatural

/-!
# Constructing the original plane model from a marked parabolic quotient

The original full-module natural quotient and its kernel placement are now
proved. A surjection to the literal plane-local group, compatible with the
original A5 marking and with the whole intrinsic block as kernel, therefore
supplies every field of OriginalPlaneModel. No natural-module or kernel
placement callback is required. Whole-block recognition and construction of
the marked parabolic quotient remain with qt-d-tensor-sp4-plane; this is a
conditional assembly step, not a proof of 9.3.10.

Source: Aschbacher--Smith 9.3.10 and the final paragraph of 9.3,
printed pp.734--735.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ClassicalOrthogonal.FourPlusMatrix
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  {m : SourceA5TensorModel D e}

/-- All original-plane fields follow from the marked parabolic quotient;
the full-module quotient and its kernel bound are constructed here. -/
theorem originalPlaneModel_of_block_marked_quotient (c : m.GenerationTwoOvergroup)
    (hblock : ChapterC.IsSp4FourBlock (pResidual 2 c.M))
    (q : L →* planeLocal (F := Binary.F)) (hq : Function.Surjective q)
    (hk : q.ker = (((ChapterC.blockU (pResidual 2 c.M)).map
      (pResidual 2 c.M).subtype).map c.M.subtype).subgroupOf L)
    (hmark : ∀ l : L, Plane.quotientMap (q l) =
      m.firstMarking (e (QuotientGroup.mk' (pCore 2 L) l))) :
    Nonempty (OriginalPlaneModel D) := by
  obtain ⟨p,hp,hpk,he⟩ := m.exists_fullModule_natural_quotient
  apply originalPlaneModel_of_block_maps c hblock q hq hk p hp
  · rw [hpk]
    exact comap_mono (comap_mono c.tensorPlane_le_blockU)
  · let := fullModule_component_normal (D := D)
    intro l v
    rw [hmark l]
    exact he l v

/-- The remaining plane recognition supplies the actual surjection, its
entire kernel, and compatibility with the original A5 marking. The natural
quotient is constructed above and is not an additional premise. -/
@[expose] def SymplecticMarkedPlaneQuotient (m : SourceA5TensorModel D e) : Prop :=
  ∀ c : m.GenerationTwoOvergroup,
    ((pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃*
      Matrix.symplecticGroup (Fin 2) ChapterB.QuasisimpleSource.BinaryField.four.Carrier) →
    ChapterC.IsSp4FourBlock (pResidual 2 c.M) →
    ∃ q : L →* planeLocal (F := Binary.F), Function.Surjective q ∧
      q.ker = (((ChapterC.blockU (pResidual 2 c.M)).map
        (pResidual 2 c.M).subtype).map c.M.subtype).subgroupOf L ∧
      ∀ l : L, Plane.quotientMap (q l) =
        m.firstMarking (e (QuotientGroup.mk' (pCore 2 L) l))

theorem symplecticPlaneFromBlock_of_marked_quotient
    (hquot : m.SymplecticMarkedPlaneQuotient) : m.SymplecticPlaneFromBlock := by
  intro c eK hblock
  obtain ⟨q,hq,hk,hmark⟩ := hquot c eK hblock
  exact originalPlaneModel_of_block_marked_quotient c hblock q hq hk hmark

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
