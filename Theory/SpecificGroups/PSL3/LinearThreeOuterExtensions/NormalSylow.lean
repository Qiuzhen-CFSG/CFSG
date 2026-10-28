module

public import Theory.SpecificGroups.PSL3.LinearThreeOuterExtensions.Locals
public import Theory.SpecificGroups.SL2.NormalSylowFieldAction
public import Theory.GroupTheory.NormalSylowQuotientAction
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Relative normal Sylows act inwardly on the two linear-three local quotients

Use the literal local subgroup L in the automorphism extension, its
intersection Sⱼ = S ∩ L, and Bⱼ = N_L(Sⱼ) mapped back to the extension.
The original quotient map followed by `localQuotientEquiv` maps Sⱼ onto
a Sylow of SL₂ and maps Bⱼ onto that Sylow's full normalizer.

Relative normality of S in SBⱼ makes all normalizer displacements lie in
the quotient Sylow. The rank-one torus calculation then kills the original
ambient coefficient field automorphism. Transporting back along the same
quotient identification proves innerness of the actual quotient action.

`HasLocalActorFormula` is the sole additional calculation premise: each
actor is inner times the coefficient action, with the coefficient recovered
from the original ambient actor. It allows arbitrary field parts and does
not assume innerness. The separate local core calculation must supply it
in the source assembly. Both point and line factors are covered by `point`.
The implication holds for every finite field of characteristic two, hence
in particular for the source range q = 2ⁿ with n > 1.

Source: Aschbacher--Smith F.1.12, printed p.264 (PDF p.275).
This conditional implication is not the complete F.1.12 assembly.
-/

@[expose] public section

open scoped MatrixGroups
open Matrix Subgroup
namespace Matrix.PSL3.LinearThree.OuterExtensions.NormalSylow
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
variable (E : Subgroup (MulAut PSL(3,F))) (hinner : MulAut.innerSubgroup PSL(3,F) ≤ E)

/-- The original local quotient map followed by its actual SL₂ identification. -/
noncomputable def localBlockProjection (point : Bool) : localIn F E hinner point →* SL(2,F) :=
  (localQuotientEquiv F E hinner point).toMonoidHom.comp (QuotientGroup.mk' _)

theorem localBlockProjection_surjective (point : Bool) :
    Function.Surjective (localBlockProjection F E hinner point) :=
  (localQuotientEquiv F E hinner point).surjective.comp (QuotientGroup.mk'_surjective _)

/-- Compatibility with conjugation in the original extension. -/
theorem localBlockProjection_action (point : Bool)
    (a : normalizer (localIn F E hinner point : Set E)) (x : localIn F E hinner point) :
    localBlockAction F E hinner point a (localBlockProjection F E hinner point x) =
      localBlockProjection F E hinner point ((localIn F E hinner point).normalizerMonoidHom a x) := by
  change localQuotientEquiv F E hinner point
    (localQuotientAction F E hinner point a
      ((localQuotientEquiv F E hinner point).symm
        (localQuotientEquiv F E hinner point (QuotientGroup.mk' _ x)))) = _
  rw [MulEquiv.symm_apply_apply, localQuotientAction_mk]
  rfl

omit [CharP F 2] in
/-- The intersection is Sylow in the actual embedded local factor. -/
theorem localIntersection_isSylow (S : Sylow 2 E) (point : Bool)
    (hSL : (S : Subgroup E) ≤ normalizer (localIn F E hinner point : Set E)) :
    ∃ P : Sylow 2 (localIn F E hinner point),
      (P : Subgroup _) = localIntersection F E hinner S point :=
  Subgroup.NormalSylowQuotientAction.intersection_sylow S _ hSL

/-- The actual intersection and its relative normalizer project to a Sylow
and its full normalizer in the same determinant-one block. -/
theorem localBorel_quotient (S : Sylow 2 E) (point : Bool)
    (hSL : (S : Subgroup E) ≤ normalizer (localIn F E hinner point : Set E)) :
    ∃ P : Sylow 2 SL(2,F),
      (P : Subgroup SL(2,F)) = (localIntersection F E hinner S point).map
        (localBlockProjection F E hinner point) ∧
      ((localBorel F E hinner S point).subgroupOf (localIn F E hinner point)).map
        (localBlockProjection F E hinner point) = normalizer (P : Set SL(2,F)) := by
  obtain ⟨R, hR⟩ := localIntersection_isSylow F E hinner S point hSL
  refine ⟨R.mapSurjective (localBlockProjection_surjective F E hinner point), ?_, ?_⟩
  · change (R : Subgroup (localIn F E hinner point)).map _ = _
    rw [hR]
  · change (((normalizer (localIntersection F E hinner S point : Set _)).map
        (localIn F E hinner point).subtype).comap
        (localIn F E hinner point).subtype).map _ = _
    rw [Subgroup.comap_map_eq_self_of_injective Subtype.val_injective, ← hR]
    exact R.normalizer_map_surjective _ (localBlockProjection_surjective F E hinner point)

/-- The sole calculation input retains the original ambient field coefficient. -/
def HasLocalActorFormula (hlinear : E ≤ ExtensionBorel.linearField F)
    (S : Sylow 2 E) (point : Bool)
    (hSL : (S : Subgroup E) ≤ normalizer (localIn F E hinner point : Set E)) : Prop :=
  ∀ s : S, ∃ g : SL(2,F),
    localBlockAction F E hinner point ⟨s, hSL s.property⟩ =
      MulAut.conj g * Atlas.RankOneFieldAutomorphisms.slFieldAction
        (coefficient F ⟨s.val.val, hlinear s.val.property⟩)

/-- Relative normality forces the coefficient of each original ambient actor to be trivial. -/
theorem local_coefficient_eq_one_of_normal
    (hlinear : E ≤ ExtensionBorel.linearField F) (S : Sylow 2 E) (point : Bool)
    (hSL : (S : Subgroup E) ≤ normalizer (localIn F E hinner point : Set E))
    (hn : ((S : Subgroup E).subgroupOf ((S : Subgroup E) ⊔
      localBorel F E hinner S point)).Normal)
    (hformula : HasLocalActorFormula F E hinner hlinear S point hSL) (s : S) :
    coefficient F ⟨s.val.val, hlinear s.val.property⟩ = 1 := by
  obtain ⟨P, _, hP⟩ := Subgroup.NormalSylowQuotientAction.quotient_displacements S
    (localIn F E hinner point) hSL hn (localBlockProjection F E hinner point)
    (localBlockProjection_surjective F E hinner point)
    (fun s => localBlockAction F E hinner point ⟨s, hSL s.property⟩)
    (fun s x => localBlockProjection_action F E hinner point _ x)
  obtain ⟨g, hg⟩ := hformula s
  have hp := hP s
  rw [hg] at hp
  exact Atlas.RankOneFieldAutomorphisms.NormalSylow.sl_field_eq_one_of_normalizer_displacements F P g _ hp.1 hp.2

/-- For either local factor, S normal in SBⱼ forces its literal quotient action to be inner. -/
theorem localQuotientAction_inner_of_normal
    (hlinear : E ≤ ExtensionBorel.linearField F) (S : Sylow 2 E) (point : Bool)
    (hSL : (S : Subgroup E) ≤ normalizer (localIn F E hinner point : Set E))
    (hn : ((S : Subgroup E).subgroupOf ((S : Subgroup E) ⊔
      localBorel F E hinner S point)).Normal)
    (hformula : HasLocalActorFormula F E hinner hlinear S point hSL) :
    ((localQuotientAction F E hinner point).comp (Subgroup.inclusion hSL)).range ≤
      MulAut.innerSubgroup (localIn F E hinner point ⧸ pCore 2 (localIn F E hinner point)) := by
  rintro _ ⟨s, rfl⟩
  obtain ⟨g, hg⟩ := hformula s
  rw [local_coefficient_eq_one_of_normal F E hinner hlinear S point hSL hn hformula s,
    map_one, mul_one] at hg
  have hi := (MulAut.congr_inner_iff (localQuotientEquiv F E hinner point)
    (localQuotientAction F E hinner point ⟨s, hSL s.property⟩)).mp ⟨g, hg⟩
  obtain ⟨x, hx⟩ := hi
  exact ⟨x, hx.symm⟩
end Matrix.PSL3.LinearThree.OuterExtensions.NormalSylow
