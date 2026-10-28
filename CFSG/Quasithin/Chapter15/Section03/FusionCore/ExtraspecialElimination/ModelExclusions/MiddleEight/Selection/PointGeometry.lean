module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.MiddleEight.Inputs
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.MiddleEight.Selection.Coordinates
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.MiddleEight.Selection.PointGeometry.InverseSimilarity
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.BinaryGeneration.StarSetup
public import Theory.Representation.BinaryOffender.InvariantAction

/-!
# Excluding the natural branches in the marked S₈ extension

The literal component commutator is already a subrepresentation of H*.
Relative normality of L* makes its fixed space H*-invariant as well, so
H* acts on the actual central quotient appearing in B.5.1. Both the moved
space and its central quotient therefore inherit inverse similarity from
the given equivalence H* ≃ S₈.

The explicit SL₄(2) calculation in `InverseSimilarity` contradicts a
natural quotient or any positive number of repeated naturals. This proves
the two exclusions required by coordinate selection using the given
extension, with no central splitting, cohomology assumption, or selected
natural-plus-dual coordinates. The point-stabilizer index is not needed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.49, printed p.1145; B.5.1(1i,1iv), pp.99–103.
-/

@[expose] public section

open Subgroup Representation
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.MiddleEight.Selection
open ComponentReduction.ModelReduction PointGeometry

section Extension
variable {K V : Type*} [Group K] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) K V) (L : Subgroup K) [L.Normal]
    (U : Subrepresentation ρ)
    (hU : U.toSubmodule = Coinvariants.ker (ρ.comp L.subtype))
    (s : MovedSection (ρ.comp L.subtype) ⊤)

private noncomputable def extendedSpace : Subrepresentation ρ where
  toSubmodule := s.space.toSubmodule
  apply_mem_toSubmodule g v hv := by
    rw [movedSection_space_eq ρ L U hU s] at hv ⊢
    exact U.apply_mem_toSubmodule g hv

private noncomputable def extendedCentral : Subrepresentation (extendedSpace ρ L U hU s).toRepresentation where
  toSubmodule := s.central.toSubmodule
  apply_mem_toSubmodule g v hv := by
    have heq : s.central.toSubmodule =
        BinaryOffender.fixedSpace (extendedSpace ρ L U hU s).toRepresentation L := by
      rw [s.central_eq]
      ext v
      change (∀ l : (⊤ : Subgroup L), s.space.toRepresentation l v = v) ↔
        ∀ l : L, (extendedSpace ρ L U hU s).toRepresentation l v = v
      exact ⟨fun h l => h ⟨l, mem_top l⟩, fun h l => h l⟩
    rw [heq] at hv ⊢
    exact (BinaryOffender.fixedSpace_stable_of_normal _ L (mem_top g) v).2 hv

end Extension

universe u
variable {G : Type u} [Group G] [Finite G]
  {κ : GroupClass.{u}} {H M Y V Y₀ L ZS Z A : Subgroup G} {T : Sylow 2 G}
  [IsElementaryAbelian 2 (localSpan ZS H)]
  (d : BorelInner.SourceSetup κ H M Y V Y₀ L ZS Z A T)
  (r : ReducedLocalData H M L Y₀ T)
  (m : BinaryGeometry.MiddleNodeEight (starImage H L) (componentParabolic H L Y₀ T))
  {Vγ : Subgroup G} (p : PointData d Vγ)
  (c : QuasisimpleSourceConclusion (d.action.representation.comp (starImage H L).subtype) ⊤)

omit [Finite G] in
include r m p in
/-- The actual S₈ extension excludes the natural central quotient in
B.5.1(1i). The central submodule is retained throughout. -/
theorem not_natural_quotient :
    ¬ Nonempty (ActionEquiv
      (c.sectionData.action.comp (⊤ : Subgroup (starImage H L)).subtype)
      (linearNatural BinaryField.two 4)) := by
  rintro ⟨f⟩
  let := BinaryGeneration.star_component_normal r
  let τ := (extendedCentral d.action.representation (starImage H L) p.space
    p.component_space c.sectionData).quotientRepresentation
  have hτ : τ.comp ((starImage H L).subtype.comp (⊤ : Subgroup (starImage H L)).subtype) =
      c.sectionData.action.comp (⊤ : Subgroup (starImage H L)).subtype := by
    ext g v
    rfl
  have hs := inverseSimilar_of_symmetric_extension τ
    ((starImage H L).subtype.comp (⊤ : Subgroup (starImage H L)).subtype) m.extension
  rw [hτ] at hs
  exact natural_not_inverseSimilar (inverseSimilar_transport f hs)

omit [Finite G] in
include m p in
/-- The actual S₈ extension excludes every positive multiplicity of the
same natural module, in particular the one-to-three copies of B.5.1(1iv). -/
theorem not_repeated_natural (k : ℕ) (hk : 0 < k) :
    ¬ IsRepeatedLinearNatural
      (c.sectionData.space.toRepresentation.comp (⊤ : Subgroup (starImage H L)).subtype)
      BinaryField.two 4 k := by
  rintro ⟨f⟩
  let τ := (extendedSpace d.action.representation (starImage H L) p.space
    p.component_space c.sectionData).toRepresentation
  have hτ : τ.comp ((starImage H L).subtype.comp (⊤ : Subgroup (starImage H L)).subtype) =
      c.sectionData.space.toRepresentation.comp (⊤ : Subgroup (starImage H L)).subtype := by
    ext g v
    rfl
  have hs := inverseSimilar_of_symmetric_extension τ
    ((starImage H L).subtype.comp (⊤ : Subgroup (starImage H L)).subtype) m.extension
  rw [hτ] at hs
  exact repeated_not_inverseSimilar k hk (inverseSimilar_transport f hs)


end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.MiddleEight.Selection
