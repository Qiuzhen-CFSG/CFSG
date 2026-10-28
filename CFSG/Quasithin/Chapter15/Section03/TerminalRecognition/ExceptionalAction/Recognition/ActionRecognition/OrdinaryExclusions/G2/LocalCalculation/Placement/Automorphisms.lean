module

public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.ResidualAction
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.MarkedRestriction
public import Theory.AtlasPort.LinearGroups.G2.LieBinaryCompatibility
public import Theory.AtlasPort.LinearGroups.G2.SylowParabolicInvariance
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# Automorphism transport of the marked binary G₂ residual

Sylow conjugacy reduces an arbitrary automorphism of the derived model to one
fixing the standard Sylow subgroup. The intrinsic parabolic-invariance theorem
then fixes the first parabolic and its literal two-residual. Restriction to the
characteristic derived subgroup handles automorphisms of the full model.
No automorphism classification or representation classification is used.

This supplies the arbitrary-isomorphism step in the marked-core argument of
Aschbacher–Smith, final proof of 15.3.1, printed p.1155. The concrete root model
and parabolic-invariance calculations come from the licensed ATLAS port through
the imports; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section

open Subgroup Atlas.G2 Atlas.G2.BinaryParabolicPair
open scoped Pointwise

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.G2.LocalCalculation.Placement

private theorem derived_K_eq_residual : ResidualAction.K.subgroupOf DerivedModel =
    (pResidual 2 derivedFirst).map derivedFirst.subtype := by
  apply map_injective DerivedModel.subtype_injective
  rw [map_subgroupOf_eq_of_le ResidualAction.K_le_derived,
    ResidualAction.derived_residual]

private lemma conjugate_of_sylow_invariance {A : Type*} [Group A] [Finite A]
    (S : Sylow 2 A) (L : Subgroup A)
    (hinv : ∀ c : MulAut A, (S : Subgroup A).map c.toMonoidHom = S →
      L.map c.toMonoidHom = L) (b : MulAut A) :
    ∃ g : A, L.map b.toMonoidHom = L.map (MulAut.conj g).toMonoidHom := by
  let T := S.mapSurjective (f := b.toMonoidHom) b.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq A T S
  let c : MulAut A := b.trans (MulAut.conj g)
  have hc : c.toMonoidHom = (MulAut.conj g).toMonoidHom.comp b.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    rfl
  have hs : (S : Subgroup A).map c.toMonoidHom = S := by
    have hh := congrArg (fun U : Sylow 2 A => (U : Subgroup A)) hg
    change ((S : Subgroup A).map b.toMonoidHom).map
      (MulAut.conj g).toMonoidHom = S at hh
    rwa [hc, ← map_map]
  have hL := hinv c hs
  refine ⟨g⁻¹, ?_⟩
  have hh := congrArg (map (MulAut.conj g⁻¹).toMonoidHom) hL
  have he : (MulAut.conj g⁻¹).toMonoidHom.comp c.toMonoidHom = b.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    change g⁻¹ * (g * b x * g⁻¹) * (g⁻¹)⁻¹ = b x
    group
  rwa [map_map, he] at hh

/-- Every automorphism of the derived model preserves the first residual up to conjugacy. -/
theorem derived_automorphism_marking (b : MulAut DerivedModel) :
    ∃ g : DerivedModel, (ResidualAction.K.subgroupOf DerivedModel).map b.toMonoidHom =
      (ResidualAction.K.subgroupOf DerivedModel).map (MulAut.conj g).toMonoidHom := by
  apply conjugate_of_sylow_invariance derivedSylow (ResidualAction.K.subgroupOf DerivedModel) ?_ b
  intro c hc
  have hU : (unipotent.subgroupOf DerivedModel).map c.toMonoidHom = unipotent.subgroupOf DerivedModel := by
    simpa only [derivedSylow_eq] using hc
  have hP : derivedFirst.map c.toMonoidHom = derivedFirst := by
    have h := (SylowParabolicInvariance.restricted_parabolics_invariant c hU).1
    simpa only [LieParabolicSetup.parabolic₁_binary, derivedFirst, DerivedModel] using h
  rw [derived_K_eq_residual, map_embedded_pResidual, hP]

/-- Restriction to the characteristic derived subgroup gives the same result in the full model. -/
theorem full_automorphism_marking (b : MulAut (Model (ZMod 2))) :
    ∃ g : (Model (ZMod 2)), ResidualAction.K.map b.toMonoidHom = ResidualAction.K.map (MulAut.conj g).toMonoidHom := by
  let c : MulAut DerivedModel := MulAut.characteristic DerivedModel b
  obtain ⟨g,hg⟩ := derived_automorphism_marking c
  refine ⟨g.val, ?_⟩
  have hh := congrArg (map DerivedModel.subtype) hg
  have hleft : DerivedModel.subtype.comp c.toMonoidHom = b.toMonoidHom.comp DerivedModel.subtype := rfl
  have hright : DerivedModel.subtype.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj g.val).toMonoidHom.comp DerivedModel.subtype := rfl
  rw [map_map, map_map, hleft, hright, ← map_map, ← map_map,
    map_subgroupOf_eq_of_le ResidualAction.K_le_derived] at hh
  exact hh

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.G2.LocalCalculation.Placement
