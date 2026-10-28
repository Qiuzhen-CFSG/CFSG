module

public import Theory.Mathieu.M22.ChapterHLocalClassification.HexadAction.Restriction
public import Theory.Mathieu.M22.ChapterHLocalClassification.HexadAction.SymplecticComparison.Representation

/-!
# Conditional natural-module comparison for the native M22 hexad action

A preserved nondegenerate alternating form on the inherited octad four-space
identifies the faithful outer hexad action with the deleted six-letter module.
The general comparison constructs the necessary automorphism alpha of S₆.
Here the new outer quotient marking is explicitly
`alpha ∘ sixRelabeling.permCongrHom ∘ outerQuotientEquiv`.
Its restriction, composed with the original inner marking, gives the compatible
A₆ action via `symmetricAction_alternating`. Both equations are also proved for
the literal intrinsic quotients and stabilizers.

Source: Aschbacher–Smith H.14.3(3), printed p.397. This module proves the
conditional comparison, not the existence of the invariant form. The latter
and the final source-theorem assembly remain separate obligations.
-/

public section

open MathieuCode MathieuCode.Hexad.CocodeAction.SixPointModel
namespace Sporadic.Mathieu.M22ChapterH.Hexad.Action.SymplecticComparison
noncomputable section

/-- A fixed relabeling of the actual hexad coordinates, using their proved cardinality. -/
@[expose] def sixRelabeling : H ≃ Fin 6 := Fintype.equivFinOfCardEq card_H

/-- The native action, with only its coordinate labels changed. -/
def relabeledAction : Equiv.Perm (Fin 6) →* (Space ≃ₗ[ZMod 2] Space) :=
  symmetricAction.comp sixRelabeling.permCongrHom.symm.toMonoidHom

theorem relabeledAction_injective : Function.Injective relabeledAction :=
  symmetricAction_injective.comp sixRelabeling.permCongrHom.symm.injective

@[simp] theorem relabeledAction_relabel (s : Equiv.Perm H) :
    relabeledAction (sixRelabeling.permCongrHom s) = symmetricAction s := by
  change symmetricAction (sixRelabeling.permCongrHom.symm (sixRelabeling.permCongrHom s)) = _
  rw [MulEquiv.symm_apply_apply]

variable (B : LinearMap.BilinForm (ZMod 2) Space)
    (ha : B.IsAlt) (hn : B.Nondegenerate)
    (hp : ∀ s v w, B (symmetricAction s v) (symmetricAction s w) = B v w)

include hp in
private theorem relabeledAction_preserves (s : Equiv.Perm (Fin 6)) (v w : Space) :
    B (relabeledAction s v) (relabeledAction s w) = B v w :=
  hp (sixRelabeling.permCongrHom.symm s) v w

/-- The actual automorphism supplied by the faithful symplectic comparison. -/
def markingAutomorphism : Equiv.Perm (Fin 6) ≃* Equiv.Perm (Fin 6) :=
  HexadSymplecticComparison.automorphism relabeledAction B ha hn
    (relabeledAction_preserves B hp) relabeledAction_injective

/-- The inherited four-space in the actual deleted permutation-module coordinates. -/
def naturalCoordinates : Space ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6) :=
  HexadSymplecticComparison.naturalEquiv B ha hn

/-- The new quotient marking is alpha after relabeling after the original marking. -/
@[expose] def outerNaturalMarking : (Outer ⧸ pCore 2 Outer) ≃* Equiv.Perm (Fin 6) :=
  outerQuotientEquiv.trans
    (sixRelabeling.permCongrHom.trans (markingAutomorphism B ha hn hp))

@[simp] theorem outerNaturalMarking_apply (q : Outer ⧸ pCore 2 Outer) :
    outerNaturalMarking B ha hn hp q =
      markingAutomorphism B ha hn hp (sixRelabeling.permCongrHom (outerQuotientEquiv q)) := rfl

/-- The same automorphism restricts to A6; it is not an independently chosen marking. -/
def innerNaturalMarking : (Inner ⧸ pCore 2 Inner) ≃* alternatingGroup (Fin 6) :=
  innerQuotientEquiv.trans (sixRelabeling.altCongrHom.trans
    (HexadSymplecticComparison.alternatingAutomorphism (markingAutomorphism B ha hn hp)))

@[simp] theorem innerNaturalMarking_coe (q : Inner ⧸ pCore 2 Inner) :
    (innerNaturalMarking B ha hn hp q).val =
      markingAutomorphism B ha hn hp
        (sixRelabeling.permCongrHom (innerQuotientEquiv q).val) := by
  change (HexadSymplecticComparison.alternatingAutomorphism _
    (sixRelabeling.altCongrHom (innerQuotientEquiv q))).val = _
  rw [HexadSymplecticComparison.alternatingAutomorphism_coe, Equiv.altCongrHom_apply_coe]
  rfl

theorem markingAutomorphism_preserves_alternating :
    (alternatingGroup (Fin 6)).map (markingAutomorphism B ha hn hp).toMonoidHom =
      alternatingGroup (Fin 6) :=
  HexadSymplecticComparison.automorphism_map_alternating _

/-- Conditional natural-module comparison for the native six-coordinate outer action. -/
theorem symmetricAction_natural (s : Equiv.Perm H) (v : Space) :
    naturalCoordinates B ha hn (symmetricAction s v) =
      BinaryPermutation.naturalRepresentation (Fin 6)
        (markingAutomorphism B ha hn hp (sixRelabeling.permCongrHom s))
        (naturalCoordinates B ha hn v) := by
  have he := HexadSymplecticComparison.naturalEquiv_action relabeledAction B ha hn
    (relabeledAction_preserves B hp) relabeledAction_injective
    (sixRelabeling.permCongrHom s) v
  rw [relabeledAction_relabel] at he
  exact he

/-- Restriction along the actual inclusion A6(H) ≤ S6(H), with the same coordinates. -/
theorem alternatingAction_natural (s : alternatingGroup H) (v : Space) :
    naturalCoordinates B ha hn (alternatingAction s v) =
      BinaryPermutation.naturalRepresentation (Fin 6)
        (HexadSymplecticComparison.alternatingAutomorphism (markingAutomorphism B ha hn hp)
          (sixRelabeling.altCongrHom s)).val (naturalCoordinates B ha hn v) := by
  rw [HexadSymplecticComparison.alternatingAutomorphism_coe, Equiv.altCongrHom_apply_coe]
  rw [← symmetricAction_alternating]
  exact symmetricAction_natural B ha hn hp s.val v

/-- The comparison on the original outer intrinsic quotient. -/
theorem outerQuotientAction_natural (q : Outer ⧸ pCore 2 Outer) (v : Space) :
    naturalCoordinates B ha hn (outerQuotientAction q v) =
      BinaryPermutation.naturalRepresentation (Fin 6) (outerNaturalMarking B ha hn hp q)
        (naturalCoordinates B ha hn v) := by
  have he := symmetricAction_natural B ha hn hp (outerQuotientEquiv q) v
  change naturalCoordinates B ha hn
    (outerQuotientAction (outerQuotientEquiv.symm (outerQuotientEquiv q)) v) = _ at he
  rw [MulEquiv.symm_apply_apply] at he
  exact he

/-- The comparison on the original inner intrinsic quotient. -/
theorem innerQuotientAction_natural (q : Inner ⧸ pCore 2 Inner) (v : Space) :
    naturalCoordinates B ha hn (innerQuotientAction q v) =
      BinaryPermutation.naturalRepresentation (Fin 6) (innerNaturalMarking B ha hn hp q).val
        (naturalCoordinates B ha hn v) := by
  have he := alternatingAction_natural B ha hn hp (innerQuotientEquiv q) v
  change naturalCoordinates B ha hn
    (innerQuotientAction (innerQuotientEquiv.symm (innerQuotientEquiv q)) v) = _ at he
  rw [MulEquiv.symm_apply_apply] at he
  exact he

/-- The natural-module equation for the literal outer stabilizer action. -/
theorem outerLinearAction_natural (g : Outer) (v : Space) :
    naturalCoordinates B ha hn (outerLinearAction g v) =
      BinaryPermutation.naturalRepresentation (Fin 6)
        (outerNaturalMarking B ha hn hp (QuotientGroup.mk g)) (naturalCoordinates B ha hn v) :=
  outerQuotientAction_natural B ha hn hp (QuotientGroup.mk g) v

/-- The natural-module equation for the literal inner stabilizer action. -/
theorem innerLinearAction_natural (g : Inner) (v : Space) :
    naturalCoordinates B ha hn (innerLinearAction g v) =
      BinaryPermutation.naturalRepresentation (Fin 6)
        (innerNaturalMarking B ha hn hp (QuotientGroup.mk g)).val (naturalCoordinates B ha hn v) :=
  innerQuotientAction_natural B ha hn hp (QuotientGroup.mk g) v

/-- The two new markings still agree under the original inclusion in the pair overgroup. -/
theorem naturalMarkings_compatible (g : Inner) :
    outerNaturalMarking B ha hn hp (QuotientGroup.mk (innerToOuter g)) =
      (innerNaturalMarking B ha hn hp (QuotientGroup.mk g)).val := by
  rw [outerNaturalMarking_apply, innerNaturalMarking_coe,
    outerQuotientEquiv_mk, innerQuotientEquiv_mk]
  rfl

end
end Sporadic.Mathieu.M22ChapterH.Hexad.Action.SymplecticComparison
