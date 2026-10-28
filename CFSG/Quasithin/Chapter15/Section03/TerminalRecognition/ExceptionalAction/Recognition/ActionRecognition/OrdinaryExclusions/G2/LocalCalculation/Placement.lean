module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.G2.LocalCalculation.MarkedFactor
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.G2.LocalCalculation.Placement.Automorphisms
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.G2.LocalCalculation.Placement.AlignedPair
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.G2.LocalCalculation.Placement.SecondCore
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.G2.LocalCalculation.Placement.ReversedPair

/-!
# Marking the first residual under arbitrary offender isomorphisms

The local residual identity transports through the actual core projection.
Once its first local group has been placed on the first model parabolic,
cardinality identifies the offender image as the full or derived model, as
appropriate. Comparing the induced isomorphism with an arbitrary supplied one
and applying automorphism invariance gives the exact required subgroup marking.

The source-pair theorem in AlignedPair leaves two orientations. ReversedPair
excludes the reversed orientation using the relative Thompson normalization
and source commutator identities. This gives unconditional recognition for
every supplied offender isomorphism, independently of the quotient isomorphism
used to align the source pair. The strict core inequality alone does not select
the orientation, as SecondCore proves. No action recognition, fixed-space bound,
or representation classification is assumed here.

Source: Aschbacher–Smith, final proof of 15.3.1, printed p.1155.
-/

public section

open Subgroup Atlas.G2 Atlas.G2.BinaryParabolicPair
open Representation.BinaryOffender

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.G2.LocalCalculation.Placement

variable {H : Type*} [Group H] [Finite H] {V : Subgroup H}
  [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)

omit [Finite H] in
private theorem full_image_top (e : coreQuotient H ≃* (Model (ZMod 2))) (f : d.offenderGroup ≃* (Model (ZMod 2))) :
    d.offenderGroup.map e.toMonoidHom = ⊤ := by
  apply (card_eq_iff_eq_top _).mp
  rw [card_map_of_injective e.injective]
  exact Nat.card_congr f.toEquiv

private theorem derived_image (e : coreQuotient H ≃* (Model (ZMod 2))) (f : d.offenderGroup ≃* DerivedModel) :
    d.offenderGroup.map e.toMonoidHom = DerivedModel := by
  rcases offenderImage_eq_derived_or_top d e with h | h
  · exact h
  · have hc : Nat.card d.offenderGroup = Nat.card (Model (ZMod 2)) := by
      rw [← card_map_of_injective (K := d.offenderGroup) (f := e.toMonoidHom) e.injective]
      exact (card_eq_iff_eq_top _).mpr h
    have hd : Nat.card d.offenderGroup = 6048 := by
      rw [Nat.card_congr f.toEquiv, DerivedModel, commutator_eq_longRootClosure,
        BinaryException.card_H]
    rw [hd, OrderChecks.binary_order] at hc
    contradiction

private theorem marked_eq_K (e : coreQuotient H ≃* (Model (ZMod 2)))
    (hP : (d.G1.map coreProjection).map e.toMonoidHom = firstParabolic) :
    ((markedFactor d).map d.offenderGroup.subtype).map e.toMonoidHom = ResidualAction.K := by
  rw [markedFactor_map_eq_residual, map_embedded_pResidual, hP,
    ResidualAction.first_residual]

/-- Once the first local image is the standard first parabolic, every full-model
isomorphism of the offender group gives the required conjugacy marking. -/
theorem full_marking_of_first_parabolic (e : coreQuotient H ≃* (Model (ZMod 2)))
    (hP : (d.G1.map coreProjection).map e.toMonoidHom = firstParabolic)
    (f : d.offenderGroup ≃* (Model (ZMod 2))) :
    ∃ g : (Model (ZMod 2)), (markedFactor d).map f.toMonoidHom = ResidualAction.K.map (MulAut.conj g).toMonoidHom := by
  let k : d.offenderGroup ≃* (Model (ZMod 2)) :=
    (d.offenderGroup.equivMapOfInjective e.toMonoidHom e.injective).trans
      ((MulEquiv.subgroupCongr (full_image_top d e f)).trans Subgroup.topEquiv)
  have hk : k.toMonoidHom = e.toMonoidHom.comp d.offenderGroup.subtype := by
    apply MonoidHom.ext
    intro x
    rfl
  have hL : (markedFactor d).map k.toMonoidHom = ResidualAction.K := by
    rw [hk, ← map_map]
    exact marked_eq_K d e hP
  let b : MulAut (Model (ZMod 2)) := k.symm.trans f
  have hb : b.toMonoidHom.comp k.toMonoidHom = f.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    change f (k.symm (k x)) = f x
    rw [k.symm_apply_apply]
  obtain ⟨g,hg⟩ := full_automorphism_marking b
  refine ⟨g, ?_⟩
  rw [← hb, ← map_map, hL, hg]

/-- The corresponding marking for every derived-model isomorphism, with the
literal derived-subgroup inclusion retained in the conclusion. -/
theorem derived_marking_of_first_parabolic (e : coreQuotient H ≃* (Model (ZMod 2)))
    (hP : (d.G1.map coreProjection).map e.toMonoidHom = firstParabolic)
    (f : d.offenderGroup ≃* DerivedModel) :
    ∃ g : (Model (ZMod 2)), ((markedFactor d).map f.toMonoidHom).map DerivedModel.subtype =
      ResidualAction.K.map (MulAut.conj g).toMonoidHom := by
  let k : d.offenderGroup ≃* DerivedModel :=
    (d.offenderGroup.equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr (derived_image d e f))
  have hk : DerivedModel.subtype.comp k.toMonoidHom =
      e.toMonoidHom.comp d.offenderGroup.subtype := by
    apply MonoidHom.ext
    intro x
    rfl
  have hL : (markedFactor d).map k.toMonoidHom = ResidualAction.K.subgroupOf DerivedModel := by
    apply map_injective DerivedModel.subtype_injective
    rw [map_map, hk, ← map_map, marked_eq_K d e hP,
      map_subgroupOf_eq_of_le ResidualAction.K_le_derived]
  let b : MulAut DerivedModel := k.symm.trans f
  have hb : b.toMonoidHom.comp k.toMonoidHom = f.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    change f (k.symm (k x)) = f x
    rw [k.symm_apply_apply]
  obtain ⟨g,hg⟩ := derived_automorphism_marking b
  refine ⟨g.val, ?_⟩
  rw [← hb, ← map_map, hL, hg, map_map]
  have hconj : DerivedModel.subtype.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj g.val).toMonoidHom.comp DerivedModel.subtype := rfl
  rw [hconj, ← map_map, map_subgroupOf_eq_of_le ResidualAction.K_le_derived]

/-- Under every full-model isomorphism of the actual offender group, the marked
first factor is conjugate to the standard first-parabolic two-residual. The
source pair supplies the required parabolic placement. -/
theorem full_marking (e0 : coreQuotient H ≃* Model (ZMod 2))
    (f : d.offenderGroup ≃* Model (ZMod 2)) :
    ∃ g : Model (ZMod 2), (markedFactor d).map f.toMonoidHom =
      ResidualAction.K.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨e, _hT, h₁, _h₂⟩ := aligned_source_pair_standard d e0
  exact full_marking_of_first_parabolic d e h₁ f

/-- The corresponding recognition under every derived-model isomorphism,
retaining the literal inclusion of the derived subgroup into the full model. -/
theorem derived_marking (e0 : coreQuotient H ≃* Model (ZMod 2))
    (f : d.offenderGroup ≃* commutator (Model (ZMod 2))) :
    ∃ g : Model (ZMod 2), ((markedFactor d).map f.toMonoidHom).map
      (commutator (Model (ZMod 2))).subtype =
        ResidualAction.K.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨e, _hT, h₁, _h₂⟩ := aligned_source_pair_standard d e0
  exact derived_marking_of_first_parabolic d e h₁ f

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.G2.LocalCalculation.Placement
