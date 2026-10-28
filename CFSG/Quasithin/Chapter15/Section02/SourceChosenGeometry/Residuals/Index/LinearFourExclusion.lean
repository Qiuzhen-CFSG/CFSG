module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.Index.MathieuExclusion
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.Recognition
public import Theory.GroupTheory.CubicClosureSimple
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Direct exclusion of the equality-row repeated-natural endpoint

The equality row gives solvable cubic closure in Mc. Any subgroup of Mc
with two-core quotient SL₄(2) would pass that property to SL₄(2), which
is perfect, simple and cubically generated. Thus such a section cannot
occur. The actual KI is contained in the full centralizer of the original
plane, so its terminal SL₄(2) quotient is excluded without identifying
KI with Kc or O^{3′}(Mc).

The final application consumes the existing original-U recognition in
the binary branch. Its earlier geometric packet remains explicit; the
terminal contradiction no longer uses that packet's residual identity.

Source: Aschbacher--Smith, 15.2.23(a), printed p.1117,
refs/quasithin.pdf. The imported SL₄(2)--A₈ comparison retains its ATLAS
attribution and license.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 ChosenGeometry TerminalLinear PlaneUniquenessPreceding
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B I X : Subgroup G}
variable {h : ChosenSmallSource T M Mc V}

namespace ChosenGeometry

/-- No subgroup of the equality-row partner has the actual SL₄(2)
two-core quotient. No perfectness of the subgroup itself is needed. -/
theorem ResidualInput.no_linear_four_section_in_partner_of_eq
    (r : ResidualInput h H B) (he : partnerSpan H Mc = residual H)
    (R : Subgroup G) (hR : R ≤ Mc)
    (e : (R ⧸ pCore 2 R) ≃* SL(4,ZMod 2)) : False := by
  have hs := solvable_cubic_closure_of_injective (inclusion hR)
    (inclusion_injective hR) (r.cubic_closure_solvable_of_eq he)
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 R))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  let eA := Atlas.Order20160A8.sl4TwoEquivPSL.trans
    Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8
  let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup SL(4,ZMod 2) := eA.isSimpleGroup
  let : Group.IsPerfect SL(4,ZMod 2) := Atlas.sl_perfect 4 (by decide)
  have hd : 3 ∣ Nat.card SL(4,ZMod 2) := by
    rw [Atlas.Order20160A8.sl4Two_card]
    decide
  exact cubic_closure_not_solvable_of_simple hd
    (solvable_cubic_closure_of_two_kernel f hf hk hs)

/-- The literal residual KI of the original plane centralizer cannot have
the terminal SL₄(2) quotient. The plane normalizer supplies its placement
in Mc without any partner-residual or KI = Kc identity. -/
theorem ResidualInput.original_KI_not_linear_four_of_eq
    (r : ResidualInput h H B) (he : partnerSpan H Mc = residual H)
    (X : Subgroup G)
    (e : (KI X ⁅V,B⁆ ⧸ pCore 2 (KI X ⁅V,B⁆)) ≃* SL(4,ZMod 2)) : False := by
  have hKI : KI X ⁅V,B⁆ ≤ Mc :=
    (show KI X ⁅V,B⁆ ≤ M1 X ⁅V,B⁆ from map_subtype_le _).trans
      (inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans r.plane_normalizer))
  exact r.no_linear_four_section_in_partner_of_eq he _ hKI e

/-- The original repeated-natural binary endpoint is impossible in the
equality row. Recognition provides KI/O₂(KI), so the source argument needs
neither KI = Kc nor the later small-action seed construction. -/
theorem ResidualInput.binary_repeatedNatural_false_of_eq
    (r : ResidualInput h H B) (he : partnerSpan H Mc = residual H)
    (d : PlaneUniquenessPreceding h H ⁅V,B⁆)
    (hI : PlaneEscapes Mc ⁅V,B⁆ I) (hfit : generalizedFitting I = pCore 2 I)
    (hn : I ≤ normalizer (X : Set G)) (hout : ¬ X ≤ Mc)
    {n : ℕ} (b : BinaryBranch M I X n)
    (hX : X = (primeToResidual 3 I).map I.subtype)
    (hKX : (pResidual 2 H).map H.subtype ≤ X)
    (hpair : Nonempty ((KS H T ⁅V,B⁆ ⧸ pCore 2 (KS H T ⁅V,B⁆)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
    (hirr : IsSmallActionIrreducible (T : Subgroup G) (smallActionK H)) : False := by
  let := U_elementary d hI hfit b.source.component.1
  obtain ⟨⟨e⟩,_⟩ :=
    remaining_repeatedNatural_of_binaryBranch d hI hfit hn hout b hX hKX hpair hirr
  exact r.original_KI_not_linear_four_of_eq he X e

end ChosenGeometry
end CFSG.Quasithin.Chapter15.Section02
