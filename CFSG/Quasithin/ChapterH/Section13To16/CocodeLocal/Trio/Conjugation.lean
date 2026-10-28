module

public import CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal.Trio.TopAction
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Trio.ConjugationTools

/-!
# Transport of the native trio flag

Conjugation by an actual M24 element identifies the intrinsic stabilizers,
their two-cores and their solvable residuals. Its cocode operator restricts
to the fixed and pair spaces and descends to the literal middle quotient.
The resulting linear equivalences intertwine the native actions.

Source: Aschbacher–Smith H.15.6, printed p.401, and the marking preceding
H.14.1, printed p.396. The middle section is V₉/V₃, correcting the printed V₉/V.
-/

@[expose] public section
open Representation.BinaryOffender
open MathieuCode Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open scoped Pointwise
namespace CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal
noncomputable section

lemma trioKernel_map (T U : Trio) (g : M24) (hg : g • T.parts = U.parts) :
    (trioKernel T).map (MulAut.conj g).toMonoidHom = trioKernel U := by
  let E := trioStabilizerTransport T U g hg
  change ((pCore 2 (trioStabilizer T)).map (trioStabilizer T).subtype).map _ =
    (pCore 2 (trioStabilizer U)).map (trioStabilizer U).subtype
  rw [← pCore_map_iso 2 E, Subgroup.map_map, Subgroup.map_map]
  congr 1

lemma trioResidual_map (T U : Trio) (g : M24) (hg : g • T.parts = U.parts) :
    (trioResidual T).map (MulAut.conj g).toMonoidHom = trioResidual U := by
  let E := trioStabilizerTransport T U g hg
  unfold trioResidual
  rw [← Subgroup.map_solvableResidual_eq E.toMonoidHom E.surjective,
    Subgroup.map_map, Subgroup.map_map]
  congr 1

lemma trioFixedSpace_map (T U : Trio) (g : M24) (hg : g • T.parts = U.parts) :
    (trioFixedSpace T).map (cocodeRepresentation g) = trioFixedSpace U := by
  change (fixedSpace cocodeRepresentation (trioKernel T)).map _ =
    fixedSpace cocodeRepresentation (trioKernel U)
  rw [fixedSpace_map_conj, trioKernel_map T U g hg]

/-- The ambient cocode automorphism restricts to the intrinsic fixed spaces. -/
def trioFixedTransport (T U : Trio) (g : M24) (hg : g • T.parts = U.parts) :
    trioFixedSpace T ≃ₗ[ZMod 2] trioFixedSpace U :=
  (LinearMap.GeneralLinearGroup.toLinearEquiv (cocodeRepresentation.asGroupHom g)).ofSubmodules
    _ _ (trioFixedSpace_map T U g hg)

def trioPairTransport (T U : Trio) (g : M24) (hg : g • T.parts = U.parts) :
    trioPairSpace T ≃ₗ[ZMod 2] trioPairSpace U :=
  (LinearMap.GeneralLinearGroup.toLinearEquiv (cocodeRepresentation.asGroupHom g)).ofSubmodules
    _ _ (trioPairSpace_map T U g hg)

lemma trio_action_transport (T U : Trio) (g : M24) (hg : g • T.parts = U.parts)
    (h : trioStabilizer T) (v : Cocode) :
    cocodeRepresentation g (trioRepresentation T h v) =
      trioRepresentation U (trioStabilizerTransport T U g hg h) (cocodeRepresentation g v) := by
  have he : (trioStabilizerTransport T U g hg h).val = g * h.val * g⁻¹ :=
    MulAction.stabilizerEquivStabilizer_apply hg.symm h
  change cocodeRepresentation g (cocodeRepresentation h.val v) =
    cocodeRepresentation (trioStabilizerTransport T U g hg h).val (cocodeRepresentation g v)
  rw [he, map_mul, map_mul]
  simp only [Module.End.mul_apply, cocodeRepresentation.inv_self_apply]

lemma trioFixedTransport_equivariant (T U : Trio) (g : M24) (hg : g • T.parts = U.parts)
    (h : trioStabilizer T) (v : trioFixedSpace T) :
    trioFixedTransport T U g hg ((trioFixedSubrepresentation T).toRepresentation h v) =
      (trioFixedSubrepresentation U).toRepresentation (trioStabilizerTransport T U g hg h)
        (trioFixedTransport T U g hg v) := by
  apply Subtype.ext
  exact trio_action_transport T U g hg h v

lemma trioPairTransport_equivariant (T U : Trio) (g : M24) (hg : g • T.parts = U.parts)
    (h : trioStabilizer T) (v : trioPairSpace T) :
    trioPairTransport T U g hg ((trioPairSubrepresentation T).toRepresentation h v) =
      (trioPairSubrepresentation U).toRepresentation (trioStabilizerTransport T U g hg h)
        (trioPairTransport T U g hg v) := by
  apply Subtype.ext
  exact trio_action_transport T U g hg h v

lemma trioSectionKernel_map (T U : Trio) (g : M24) (hg : g • T.parts = U.parts) :
    ((trioFixedSpace T).comap (trioPairSpace T).subtype).map
      (trioPairTransport T U g hg).toLinearMap =
      (trioFixedSpace U).comap (trioPairSpace U).subtype := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    change cocodeRepresentation g v.val ∈ trioFixedSpace U
    rw [← trioFixedSpace_map T U g hg]
    exact ⟨v.val, hv, rfl⟩
  · intro v hv
    obtain ⟨w, rfl⟩ := (trioPairTransport T U g hg).surjective v
    refine ⟨w, ?_, rfl⟩
    change cocodeRepresentation g w.val ∈ trioFixedSpace U at hv
    rw [← trioFixedSpace_map T U g hg] at hv
    obtain ⟨z, hz, he⟩ := hv
    have he' : z = w.val :=
      (LinearMap.GeneralLinearGroup.toLinearEquiv (cocodeRepresentation.asGroupHom g)).injective he
    change w.val ∈ trioFixedSpace T
    exact he' ▸ hz

/-- Transport of the literal middle quotient, not an abstract factor tag. -/
def trioSectionTransport (T U : Trio) (g : M24) (hg : g • T.parts = U.parts) :
    TrioSection T ≃ₗ[ZMod 2] TrioSection U :=
  Submodule.Quotient.equiv _ _ (trioPairTransport T U g hg) (trioSectionKernel_map T U g hg)

lemma trioSectionTransport_equivariant (T U : Trio) (g : M24) (hg : g • T.parts = U.parts)
    (h : trioStabilizer T) (v : TrioSection T) :
    trioSectionTransport T U g hg (trioSectionRepresentation T h v) =
      trioSectionRepresentation U (trioStabilizerTransport T U g hg h)
        (trioSectionTransport T U g hg v) := by
  induction v using Submodule.Quotient.induction_on with | _ v =>
  change (trioSectionKernel U).toSubmodule.mkQ
      (trioPairTransport T U g hg ((trioPairSubrepresentation T).toRepresentation h v)) =
    (trioSectionKernel U).toSubmodule.mkQ
      ((trioPairSubrepresentation U).toRepresentation (trioStabilizerTransport T U g hg h)
        (trioPairTransport T U g hg v))
  rw [trioPairTransport_equivariant]
end
end CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal
