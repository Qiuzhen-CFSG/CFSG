module

public import Theory.Mathieu.SchurMultipliers.PartialInversionSource
public import Theory.Mathieu.M12.ValueBoundParabolics.CentralCovers
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.ReadyCoverCases

/-!
# The M₁₁, M₁₂ and M₂₃ ordinary component cases of A.3.6

For M₁₁ and M₂₃, partial inversion makes every finite perfect central kernel
a two-group. For M₁₂, the proved central-cover theorem gives trivial center
directly when O₂(L)=1. Thus in all three cases the ordinary component's
original central-quotient map is an isomorphism. This supplies the simple
branch of A.3.6, and the shared quasisimple theorem supplies all common
Fitting, radical and quotient clauses.

The arbitrary two-primary universal multiplier calculations remain separate,
in particular for the M₂₃ cover application in Chapter 15.

Source: Aschbacher–Smith A.3.6, printed pp.43–46, and I.1.1–I.1.3,
printed pp.407–408.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory PerfectCentralCovering
namespace CFSG.Quasithin.ChapterA.SQTKStructure.MathieuOddCoverCases
open Chapter1.Section02 Chapter1.Section02.LocalModels
open Sporadic.Mathieu
open Sporadic.Mathieu.SchurMultipliers.PartialInversionSource

private def quotientCover {L S : Type*} [Group L] [Group S] [Group.IsPerfect L]
    (e : L ⧸ center L ≃* S) : Cover L S where
  toMonoidHom := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  surjective := e.surjective.comp (QuotientGroup.mk'_surjective _)
  isPerfect := inferInstance
  ker_le_center := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']

private theorem injective_of_two_kernel {E S : Type*}
    [Group E] [Finite E] [Group S] (f : Cover E S)
    (hker : IsPGroup 2 f.toMonoidHom.ker) (hcore : pCore 2 E = ⊥) :
    Function.Injective f.toMonoidHom := by
  apply f.toMonoidHom.ker_eq_bot_iff.mp
  apply bot_unique
  rw [← hcore]
  exact le_sSup ⟨inferInstance, hker⟩

/-- The original M₁₁ central-quotient map is injective when the ordinary
component has trivial two-core. -/
theorem m11_quotient_injective {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
    (hcore : pCore 2 L = ⊥) (e : L ⧸ center L ≃* M11) :
    Function.Injective (e.toMonoidHom.comp (QuotientGroup.mk' (center L))) :=
  injective_of_two_kernel (quotientCover e)
    (m11_cover_kernel_isTwoGroup (quotientCover e)) hcore

/-- The original M₂₃ central-quotient map is injective when the ordinary
component has trivial two-core. -/
theorem m23_quotient_injective {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
    (hcore : pCore 2 L = ⊥) (e : L ⧸ center L ≃* M23) :
    Function.Injective (e.toMonoidHom.comp (QuotientGroup.mk' (center L))) :=
  injective_of_two_kernel (quotientCover e)
    (m23_cover_kernel_isTwoGroup (quotientCover e)) hcore

private theorem simple_conclusion {X S : Type*} [Group X] [Finite X]
    [Group S] [Finite S] [IsSimpleGroup S]
    (L : Subgroup X) (hL : IsComponent X L)
    (j : L ≃* S) (hmodel : TheoremCModel L) (heven : 2 ∣ Nat.card S) :
    A36Conclusion L := by
  let : IsQuasisimple L := hL.2
  let : IsSimpleGroup L := j.isSimpleGroup
  have hz : center L = ⊥ := by
    rcases (inferInstance : (center L).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exact (Group.IsPerfect.not_isMulCommutative L (center_eq_top_iff.mp ht)).elim
  exact ⟨.simple hL inferInstance hmodel,
    ReadyCoverCases.common_of_quasisimple
      ((Nat.card_congr j.toEquiv).symm ▸ heven)
      (Or.inl (by rw [hz]; simp))⟩

/-- The full A.3.6 conclusion, including every common clause, for the
actual M₁₁ central quotient of an ordinary component with trivial two-core. -/
theorem a36_m11 {X : Type*} [Group X] [Finite X]
    (L : Subgroup X) (hL : IsComponent X L) (hcore : pCore 2 L = ⊥)
    (e : L ⧸ center L ≃* M11) : A36Conclusion L := by
  let : IsQuasisimple L := hL.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : IsSimpleGroup M11 := e.symm.isSimpleGroup
  let j : L ≃* M11 := MulEquiv.ofBijective (quotientCover e).toMonoidHom
    ⟨m11_quotient_injective hcore e, (quotientCover e).surjective⟩
  exact simple_conclusion L hL j
    (.sporadic .m11 (by intro h; cases h) ⟨j⟩) (by rw [m11_order]; norm_num)

/-- The full A.3.6 conclusion for the actual M₁₂ central quotient of an
ordinary component with trivial two-core, using the proved M₁₂ center theorem. -/
theorem a36_m12 {X : Type*} [Group X] [Finite X]
    (L : Subgroup X) (hL : IsComponent X L) (hcore : pCore 2 L = ⊥)
    (e : L ⧸ center L ≃* M12) : A36Conclusion L := by
  let : IsQuasisimple L := hL.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : IsSimpleGroup M12 := e.symm.isSimpleGroup
  have hz : center L = ⊥ :=
    M12SmallPair.ValueBoundParabolics.CentralCovers.center_eq_bot hcore e
  let f := quotientCover e
  have hk : f.toMonoidHom.ker = ⊥ := by
    change (e.toMonoidHom.comp (QuotientGroup.mk' (center L))).ker = ⊥
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk', hz]
  let j : L ≃* M12 := MulEquiv.ofBijective f.toMonoidHom
    ⟨f.toMonoidHom.ker_eq_bot_iff.mp hk, f.surjective⟩
  exact simple_conclusion L hL j
    (.sporadic .m12 (by intro h; cases h) ⟨j⟩) (by rw [m12_order]; norm_num)

/-- The full A.3.6 conclusion, including every common clause, for the
actual M₂₃ central quotient of an ordinary component with trivial two-core. -/
theorem a36_m23 {X : Type*} [Group X] [Finite X]
    (L : Subgroup X) (hL : IsComponent X L) (hcore : pCore 2 L = ⊥)
    (e : L ⧸ center L ≃* M23) : A36Conclusion L := by
  let : IsQuasisimple L := hL.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : IsSimpleGroup M23 := e.symm.isSimpleGroup
  let j : L ≃* M23 := MulEquiv.ofBijective (quotientCover e).toMonoidHom
    ⟨m23_quotient_injective hcore e, (quotientCover e).surjective⟩
  exact simple_conclusion L hL j
    (.sporadic .m23 (by intro h; cases h) ⟨j⟩) (by rw [m23_order]; norm_num)

end CFSG.Quasithin.ChapterA.SQTKStructure.MathieuOddCoverCases
