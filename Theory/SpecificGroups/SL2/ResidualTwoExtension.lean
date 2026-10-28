module
public import GorensteinWalter.SL2ProjectiveCover
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleRadicalTwoExtension
public import Theory.GroupTheory.SolvableResidual.TwoSupplement
public import Theory.GroupTheory.PResidual.FiniteImage
/-!
# Radical quotients of groups with an SL₂ residual

Suppose the solvable residual is an actual SL₂(F), with |F| odd and greater
than three, and equals the two-residual. Its central quotient is PSL₂(F).
The radical of the ambient group is a two-group, and the image of the
residual is the simple generalized Fitting subgroup of the radical quotient.
Every Sylow two-subgroup supplements that simple subgroup. This argument
uses the actual central quotient and does not assume that the extension splits.

Source: standard quasisimple two-extension theory; Aschbacher--Smith
A.3.21(a), p.55, and the involution-centralizer application in E.1.14(7), p.214.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.SL2.ResidualTwoExtension
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]

omit [Finite G] in
/-- Transfer quasisimplicity through the specified SL₂ isomorphism. -/
theorem quasisimple_of_equiv (hlarge : 3 < Nat.card F)
    (e : G ≃* Matrix.SpecialLinearGroup (Fin 2) F) : IsQuasisimple G := by
  let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) :=
    GorensteinWalter.sl2_isPerfect_of_card_gt_three F hlarge
  let : IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) F) :=
    ⟨Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)⟩
  exact IsQuasisimple.of_mulEquiv e.symm

/-- The solvable radical quotient is the actual projective special linear group. -/
noncomputable def radicalQuotientEquiv (hlarge : 3 < Nat.card F)
    (e : G ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    G ⧸ solvableRadical G ≃* GorensteinWalter.PSL2 F := by
  let : IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) F) :=
    quasisimple_of_equiv hlarge (MulEquiv.refl _)
  let : Group.IsSolvable (center (Matrix.SpecialLinearGroup (Fin 2) F)) :=
    Group.isSolvable_of_comm (fun a b => Subtype.ext (mem_center_iff.mp b.property a))
  have hc : solvableRadical (Matrix.SpecialLinearGroup (Fin 2) F) =
      center (Matrix.SpecialLinearGroup (Fin 2) F) :=
    le_antisymm IsQuasisimple.solvableRadical_le_center
      (le_solvableRadical _ inferInstance inferInstance)
  exact (QuotientGroup.congr _ _ e (map_solvableRadical_equiv e)).trans
    (QuotientGroup.quotientMulEquivOfEq hc)

/-- The actual radical quotient and its simple socle, without any splitting assumption. -/
theorem radical_quotient_structure
    (hodd : Odd (Nat.card F)) (hlarge : 3 < Nat.card F)
    (e : solvableResidual G ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hres : pResidual 2 G = solvableResidual G) :
    IsPGroup 2 (solvableRadical G) ∧
      IsSimpleGroup (generalizedFitting (G ⧸ solvableRadical G)) ∧
      Nonempty (generalizedFitting (G ⧸ solvableRadical G) ≃* GorensteinWalter.PSL2 F) ∧
      ∀ S : Sylow 2 (G ⧸ solvableRadical G),
        generalizedFitting (G ⧸ solvableRadical G) ⊔ (S : Subgroup _) = ⊤ := by
  let D := solvableResidual G
  let : IsQuasisimple D := quasisimple_of_equiv hlarge e
  let : IsSimpleGroup (D ⧸ solvableRadical D) := quasisimple_radicalQuotient_isSimple D
  let : Group.IsPerfect (D ⧸ solvableRadical D) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have ha : ¬ IsMulCommutative (D ⧸ solvableRadical D) :=
    Group.IsPerfect.not_isMulCommutative _
  have hq : IsPGroup 2 (G ⧸ D) :=
    (isPGroup_quotient_pResidual (G := G) 2).of_equiv
      (QuotientGroup.quotientMulEquivOfEq hres)
  have hzSL : IsPGroup 2 (center (Matrix.SpecialLinearGroup (Fin 2) F)) :=
    (GorensteinWalter.sl2ProjectiveProjection_ker_isPGroup F hodd).of_equiv
      (MulEquiv.subgroupCongr (GorensteinWalter.sl2ProjectiveProjection_ker F))
  have hz : IsPGroup 2 (center D) := hzSL.of_equiv (centerCongr e).symm
  exact ⟨radical_isTwoGroup_of_quasisimple_two_quotient D hz hq,
    radicalTwoExtension_fitting_simple D ha hq,
    ⟨(radicalTwoExtensionFittingEquiv D ha hq).trans (radicalQuotientEquiv hlarge e)⟩,
    radicalTwoExtension_fitting_sup_sylow D ha hq⟩
end Theory.SpecificGroups.SL2.ResidualTwoExtension
