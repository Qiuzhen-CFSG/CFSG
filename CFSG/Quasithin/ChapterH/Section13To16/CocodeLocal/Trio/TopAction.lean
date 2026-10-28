module
public import CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal.Trio.TopAction.Standard
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Trio.Transport

/-!
# The full top-quotient action for every native trio

An actual M24 element carries the standard trio to any prescribed native
trio. Its cocode action carries the geometric pair spaces to one another,
and hence gives an equivalence of the literal top quotients. This equivalence
intertwines the actions under conjugation of the actual stabilizers. The full
standard GL₂(2) action consequently transports to every trio.

Source: Aschbacher–Smith H.15.6(2), printed p.401, top-quotient clause, and
the native marking preceding H.14.1, printed p.396. This module proves the
top-action clause; fixed-space and tensor assertions have separate owners.
-/

@[expose] public section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open MathieuCode
open scoped Pointwise
namespace CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal
noncomputable section

lemma trioPairSpace_transport (T U : Trio) (g : M24) (hg : g • T.parts = U.parts)
    {v : Cocode} (hv : v ∈ trioPairSpace T) : cocodeRepresentation g v ∈ trioPairSpace U := by
  have hle : trioPairSpace T ≤ (trioPairSpace U).comap (cocodeRepresentation g) := by
    refine iSup_le fun B => iSup_le fun hB => Submodule.span_le.mpr ?_
    rintro _ ⟨P,hP,rfl⟩
    change cocodeRepresentation g (pairVector P) ∈ trioPairSpace U
    rw [pairVector_equivariant]
    have hBg : g • B ∈ U.parts := by
      rw [← hg]
      exact Finset.smul_mem_smul_finset hB
    exact Submodule.mem_iSup_of_mem (g • B) (Submodule.mem_iSup_of_mem hBg
      (pairVector_mem_supportedPairSpace (mapPair g P) (Finset.smul_finset_subset_smul_finset hP)))
  exact hle hv

lemma trioPairSpace_map (T U : Trio) (g : M24) (hg : g • T.parts = U.parts) :
    (trioPairSpace T).map (cocodeRepresentation g) = trioPairSpace U := by
  apply le_antisymm
  · rintro _ ⟨v,hv,rfl⟩
    exact trioPairSpace_transport T U g hg hv
  · intro v hv
    refine ⟨cocodeRepresentation g⁻¹ v, trioPairSpace_transport U T g⁻¹ ?_ hv,
      cocodeRepresentation.self_inv_apply g v⟩
    rw [← hg, inv_smul_smul]

/-- Conjugation by the given native transporter identifies the actual stabilizers. -/
def trioStabilizerTransport (T U : Trio) (g : M24) (hg : g • T.parts = U.parts) :
    trioStabilizer T ≃* trioStabilizer U :=
  MulAction.stabilizerEquivStabilizer hg.symm

/-- The native cocode action transports the literal geometric top quotients. -/
def trioTopTransport (T U : Trio) (g : M24) (hg : g • T.parts = U.parts) :
    (Cocode ⧸ trioPairSpace T) ≃ₗ[ZMod 2] (Cocode ⧸ trioPairSpace U) :=
  Submodule.Quotient.equiv _ _
    (LinearMap.GeneralLinearGroup.toLinearEquiv (cocodeRepresentation.asGroupHom g))
    (trioPairSpace_map T U g hg)

lemma trioTopTransport_equivariant (T U : Trio) (g : M24) (hg : g • T.parts = U.parts)
    (h : trioStabilizer T) (v : Cocode ⧸ trioPairSpace T) :
    trioTopTransport T U g hg (trioTopRepresentation T h v) =
      trioTopRepresentation U (trioStabilizerTransport T U g hg h)
        (trioTopTransport T U g hg v) := by
  induction v using Submodule.Quotient.induction_on with | _ v =>
  change (trioPairSpace U).mkQ (cocodeRepresentation g (cocodeRepresentation h.val v)) =
    (trioPairSpace U).mkQ (cocodeRepresentation
      (trioStabilizerTransport T U g hg h).val (cocodeRepresentation g v))
  have he : (trioStabilizerTransport T U g hg h).val = g * h.val * g⁻¹ :=
    MulAction.stabilizerEquivStabilizer_apply hg.symm h
  rw [he, map_mul, map_mul]
  simp only [Module.End.mul_apply, cocodeRepresentation.inv_self_apply]

lemma trioTop_surjective_of_transport (T U : Trio) (g : M24) (hg : g • T.parts = U.parts)
    (hs : Function.Surjective (trioTopRepresentation T).asGroupHom) :
    Function.Surjective (trioTopRepresentation U).asGroupHom := by
  let E := LinearMap.GeneralLinearGroup.congrLinearEquiv (trioTopTransport T U g hg)
  intro f
  obtain ⟨h,hh⟩ := hs (E.symm f)
  refine ⟨trioStabilizerTransport T U g hg h, ?_⟩
  have he : E ((trioTopRepresentation T).asGroupHom h) =
      (trioTopRepresentation U).asGroupHom (trioStabilizerTransport T U g hg h) := by
    apply Units.ext
    apply LinearMap.ext
    intro v
    change trioTopTransport T U g hg (trioTopRepresentation T h
        ((trioTopTransport T U g hg).symm v)) = _
    rw [trioTopTransport_equivariant, LinearEquiv.apply_symm_apply]
    rfl
  rw [← he, hh, MulEquiv.apply_symm_apply]

/-- The conjugating element acts on the literal octad partition. -/
theorem trio_exists_smul_standard (T : Trio) :
    ∃ g : M24, g • standardTrio.parts = T.parts :=
  TrioCalculation.exists_smul_standardTrio T

/-- Every linear automorphism of the literal top quotient is induced by a
native trio-stabilizer element (the top clause of H.15.6(2)). -/
theorem trioTopRepresentation_surjective (T : Trio) :
    Function.Surjective (trioTopRepresentation T).asGroupHom := by
  obtain ⟨g,hg⟩ := trio_exists_smul_standard T
  exact trioTop_surjective_of_transport standardTrio T g hg TrioTop.standard_surjective

end
end CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal
