module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.Index.SimpleComponentEscape
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.Exterior.Residual

/-!
# The exterior-five endpoint in the equality row

The literal residual KI lies in Mc. Its exterior-five quotient is
C₃ × SL₃(2). Solvable cubic closure passes from Mc to KI and through
its two-core kernel, whereas the embedded simple SL₃(2) factor has
nonsolvable cubic closure. This excludes the endpoint without any
identity between KI, Kc and the residual of Mc.

Source: Aschbacher--Smith 15.2.23(d), printed p.1117, refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open Section01 TerminalLinear
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B : Subgroup G}
variable {h : ChosenSmallSource T M Mc V}

/-- The marked exterior quotient cannot be a two-core section of Mc. -/
theorem ResidualInput.no_linear_three_product_section_in_partner_of_eq
    (r : ResidualInput h H B) (he : partnerSpan H Mc = residual H)
    (R : Subgroup G) (hR : R ≤ Mc)
    (e : (R ⧸ pCore 2 R) ≃* (alternatingGroup (Fin 3) × SL(3,ZMod 2))) : False := by
  have hs := solvable_cubic_closure_of_injective (inclusion hR)
    (inclusion_injective hR) (r.cubic_closure_solvable_of_eq he)
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 R))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hprod := solvable_cubic_closure_of_two_kernel f hf hk hs
  let j : SL(3,ZMod 2) →* (alternatingGroup (Fin 3) × SL(3,ZMod 2)) :=
    MonoidHom.inr _ _
  have hj : Function.Injective j := by
    intro x y heq
    exact congrArg Prod.snd heq
  let : IsSimpleGroup Matrix.PSL3Two.PSL :=
    Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)
  let : IsSimpleGroup SL(3,ZMod 2) := Matrix.PSL3Two.equiv.isSimpleGroup
  let : Group.IsPerfect SL(3,ZMod 2) := Atlas.sl_perfect 3 (by decide)
  have hd : 3 ∣ Nat.card SL(3,ZMod 2) := by
    rw [Nat.card_congr Matrix.PSL3Two.equiv.toEquiv,Matrix.PSL3Two.card_PSL]
    decide
  exact cubic_closure_not_solvable_of_simple hd
    (solvable_cubic_closure_of_injective j hj hprod)

/-- Apply the obstruction to the literal KI of the original offender plane. -/
theorem ResidualInput.original_KI_not_exterior_quotient_of_eq
    (r : ResidualInput h H B) (he : partnerSpan H Mc = residual H)
    (X : Subgroup G)
    (e : (KI X ⁅V,B⁆ ⧸ pCore 2 (KI X ⁅V,B⁆)) ≃*
      (alternatingGroup (Fin 3) × SL(3,ZMod 2))) : False := by
  have hKI : KI X ⁅V,B⁆ ≤ Mc :=
    (show KI X ⁅V,B⁆ ≤ M1 X ⁅V,B⁆ from map_subtype_le _).trans
      (inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans r.plane_normalizer))
  exact r.no_linear_three_product_section_in_partner_of_eq he _ hKI e

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
