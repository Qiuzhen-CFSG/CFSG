module

public import Theory.Representation.HexacodeAction.FullWeightVectorNonsplit
public import Theory.Representation.HexacodeAction.TerminalIrreducible
public import Theory.Representation.SpecialLinearRestriction
public import Theory.Representation.SL2FourNaturalOrbits.SelfDual
public import BenderSuzuki.External.Huppert.II.theorem_6_14

/-!
# The natural quotient at an actual full-weight hexacode vector

The vector stabilizer fixes its field line pointwise and acts on the literal
quotient by that line. The quotient has field dimension two. Simplicity of
the actual A₅ stabilizer makes its kernel trivial or total; total kernel
would put every displacement in the field line, contradicting full
commutator generation. Perfectness gives determinant one, and order sixty
makes the resulting SL₂(4) embedding surjective.

The field coordinates and their restriction to the binary field intertwine
the original quotient action, with its original projection preserved.
Source: Aschbacher–Smith, 12.7.4(2), printed pp.839–840. The hexacode and
operators retain their ATLAS attribution; see LICENSES/ATLAS.txt.
-/

public noncomputable section
open Atlas.Codes Subgroup
namespace Representation.Hexacode
open BinaryOffender

/-- The actual field-linear action on the quotient by the fixed vector's
field line. No quotient coordinates are chosen in this definition. -/
@[expose] def fullWeightVectorQuotientAction (v : hexacode) :
    Representation F (fullWeightVectorStabilizer v) (hexacode ⧸ Submodule.span F {v}) := by
  let P : Subrepresentation
      (evenFieldRepresentation.comp (fullWeightVectorStabilizer v).subtype) := {
    toSubmodule := Submodule.span F {v}
    apply_mem_toSubmodule := by
      intro g w hw
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hw
      change evenFieldAction g.val (r • v) ∈ Submodule.span F {v}
      rw [map_smul, show evenFieldAction g.val v = v from g.property]
      exact Submodule.smul_mem _ r (Submodule.mem_span_singleton_self v) }
  exact P.quotientRepresentation

/-- The quotient representation preserves the literal projection of each
original hexacode vector. -/
@[simp] theorem fullWeightVectorQuotientAction_mk (v : hexacode)
    (g : fullWeightVectorStabilizer v) (w : hexacode) :
    fullWeightVectorQuotientAction v g ((Submodule.span F {v}).mkQ w) =
      (Submodule.span F {v}).mkQ (evenFieldAction g.val w) := rfl

private theorem quotient_finrank (v : hexacode) (hv : v ≠ 0) :
    Module.finrank F (hexacode ⧸ Submodule.span F {v}) = 2 := by
  have h := (Submodule.span F {v}).finrank_quotient_add_finrank
  rw [finrank_span_singleton hv, field_finrank] at h
  omega

/-- The whole-module commutator theorem excludes the trivial quotient
action; simplicity of the actual A₅ stabilizer then gives faithfulness. -/
theorem fullWeightVectorQuotientAction_injective (v : hexacode) (hv : v ≠ 0)
    (hP : IsFullWeightScalarPlane ((Submodule.span F {v}).restrictScalars Bit)) :
    Function.Injective (fullWeightVectorQuotientAction v) := by
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (fullWeightVectorStabilizer v) :=
    (fullWeightVectorStabilizerEquiv v hv hP).isSimpleGroup
  rcases (MonoidHom.normal_ker (fullWeightVectorQuotientAction v)).eq_bot_or_eq_top with hb | ht
  · exact (fullWeightVectorQuotientAction v).ker_eq_bot_iff.mp hb
  have hweight : hammingNorm v.val = 6 :=
    hP.2.2 ⟨v, Submodule.mem_span_singleton_self v⟩ (fun h => hv (congrArg Subtype.val h))
  have hle : subspaceCommutator evenAction ⊤ (fullWeightVectorStabilizer v) ≤
      (Submodule.span F {v}).restrictScalars Bit := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, hg, w, _, rfl⟩
    apply (Submodule.Quotient.mk_eq_zero (Submodule.span F {v})).mp
    change (Submodule.span F {v}).mkQ (evenFieldAction g w - w) = 0
    rw [map_sub, ← fullWeightVectorQuotientAction_mk v ⟨g, hg⟩]
    have he : fullWeightVectorQuotientAction v ⟨g, hg⟩ = 1 :=
      show (⟨g, hg⟩ : fullWeightVectorStabilizer v) ∈
        (fullWeightVectorQuotientAction v).ker from ht ▸ mem_top _
    rw [he, Module.End.one_apply, sub_self]
  have htop : Submodule.span F {v} = ⊤ := by
    apply top_unique
    intro w _
    exact hle (by rw [fullWeightVectorStabilizer_commutator v hweight]; trivial)
  have hd := finrank_span_singleton (K := F) hv
  rw [htop, finrank_top, field_finrank] at hd
  omega

/-- The original quotient is the full natural SL₂(4) module, with a common
field-linear coordinate map and action-induced group marking. -/
theorem fullWeightVectorQuotient_natural (v : hexacode) (hv : v ≠ 0)
    (hP : IsFullWeightScalarPlane ((Submodule.span F {v}).restrictScalars Bit)) :
    ∃ (e : fullWeightVectorStabilizer v ≃* Matrix.SpecialLinearGroup (Fin 2) F)
      (a : (hexacode ⧸ Submodule.span F {v}) ≃ₗ[F] (Fin 2 → F)),
      ∀ g w, a (fullWeightVectorQuotientAction v g w) = specialLinearNatural 2 (e g) (a w) := by
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect (fullWeightVectorStabilizer v) :=
    Group.IsPerfect.ofSurjective (f := (fullWeightVectorStabilizerEquiv v hv hP).symm.toMonoidHom)
      (fullWeightVectorStabilizerEquiv v hv hP).symm.surjective
  obtain ⟨f, a, hf, ha⟩ := exists_specialLinear_restriction (fullWeightVectorQuotientAction v)
    (fullWeightVectorQuotientAction_injective v hv hP)
    (det_eq_one_of_perfect _) (quotient_finrank v hv)
  have hcard : Nat.card (fullWeightVectorStabilizer v) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [fullWeightVectorStabilizer_card v hv hP,
      BenderSuzuki.External.huppert614_card_specialLinearGroup,
      Nat.card_eq_fintype_card, field_card]
    norm_num
  exact ⟨MulEquiv.ofBijective f ((Nat.bijective_iff_injective_and_card f).mpr ⟨hf, hcard⟩), a, ha⟩

/-- Restriction of the same field coordinates gives the binary natural
module on the unchanged quotient and original vector-stabilizer actor. -/
theorem fullWeightVectorQuotient_binary_natural (v : hexacode) (hv : v ≠ 0)
    (hP : IsFullWeightScalarPlane ((Submodule.span F {v}).restrictScalars Bit)) :
    ∃ (e : fullWeightVectorStabilizer v ≃* SL2FourNatural.SL)
      (a : (hexacode ⧸ Submodule.span F {v}) ≃ₗ[Bit] SL2FourNatural.V),
      ∀ g w, a (fullWeightVectorQuotientAction v g w) =
        SL2FourNatural.naturalRepresentation (e g) (a w) := by
  obtain ⟨e, a, ha⟩ := fullWeightVectorQuotient_natural v hv hP
  exact ⟨e, a.restrictScalars Bit, ha⟩

end Representation.Hexacode
