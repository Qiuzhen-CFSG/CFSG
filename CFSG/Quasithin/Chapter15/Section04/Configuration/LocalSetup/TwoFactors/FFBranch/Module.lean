module

public import CFSG.Quasithin.ChapterB.Section01.QuasisimpleSections.Group
public import Stellmacher.CentralizerQuotientRepresentation
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Theory.GroupTheory.NormalClosureCentralizerCore
public import Theory.GroupTheory.PCoreSurjective

/-!
# The genuine internal module in the mixed characteristic-two branch

Work intrinsically in the generated group `I`. If `C_I(Z)` is its specified
Sylow two-subgroup and `F*(I) = O₂(I)`, self-centralization of `F*` puts `Z`
in `O₂(I)`. Normal closure then constructs the elementary abelian subgroup
`Vᵢ = ⟨Zᴵ⟩`. Its centralizer is exactly `O₂(I)`, and its conjugation quotient
has trivial two-core. These are the defining conditions of the source `R₂`
family, not a dimension bound. This specialized proof supplies the part of
B.2.14 needed here without assuming its conclusions.

The representation is actual conjugation descended through `I/O₂(I)`.
For a factor `Y = [Y,J(Tᵢ)]` moving `Z`, the Thompson subgroup escapes the
kernel. A maximum elementary abelian subgroup then gives an actual offender.
Neither an FF hypothesis nor a recognition conclusion is assumed.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, 15.4.18, printed p.1163; B.2.11–14, pp.77–78.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch
open Subgroup Theory.GroupTheory
open Representation.BinaryOffender Representation.NormalElementaryQuotient
open scoped IsMulCommutative
variable {H : Type*} [Group H] [Finite H]

/-- The normal closure `Vᵢ = ⟨Zᴵ⟩`, inside the actual generated group. -/
abbrev moduleClosure (Z : Subgroup H) : Subgroup H := normalClosure (Z : Set H)
/-- The quotient by the intrinsic two-core. -/
abbrev coreQuotient (H : Type*) [Group H] := H ⧸ pCore 2 H

/-- The actual quotient homomorphism. -/
def coreProjection : H →* coreQuotient H := QuotientGroup.mk' (pCore 2 H)

/-- Self-centralization of `F*` puts the seed inside the two-core. -/
theorem seed_le_twoCore (P : Sylow 2 H) (Z : Subgroup H)
    (hC : centralizer (Z : Set H) = (P : Subgroup H))
    (hF : generalizedFitting H = pCore 2 H) : Z ≤ pCore 2 H := by
  have hQC : pCore 2 H ≤ centralizer (Z : Set H) := by
    rw [hC]
    exact pCore_isPGroup.le_sylow_of_normal P
  have hself : centralizer (pCore 2 H : Set H) ≤ pCore 2 H := by
    rw [← hF]
    exact ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le
  exact (le_centralizer_iff.mp hQC).trans hself

/-- Normality of the core contains every conjugate of the seed. -/
theorem moduleClosure_le_twoCore (P : Sylow 2 H) (Z : Subgroup H)
    (hC : centralizer (Z : Set H) = (P : Subgroup H))
    (hF : generalizedFitting H = pCore 2 H) : moduleClosure Z ≤ pCore 2 H :=
  normalClosure_le_normal (seed_le_twoCore P Z hC hF)

omit [Finite H] in
/-- The kernel of the normal-closure action is exactly the two-core. -/
theorem moduleClosure_centralizer (P : Sylow 2 H) (Z : Subgroup H)
    (hC : centralizer (Z : Set H) = (P : Subgroup H)) :
    centralizer (moduleClosure Z : Set H) = pCore 2 H :=
  centralizer_normalClosure_eq_pCore_of_eq_sylow P Z hC

/-- The normal closure is elementary abelian, proved from the branch hypothesis. -/
theorem moduleClosure_elementary (P : Sylow 2 H) (Z : Subgroup H)
    [IsElementaryAbelian 2 Z]
    (hC : centralizer (Z : Set H) = (P : Subgroup H))
    (hF : generalizedFitting H = pCore 2 H) : IsElementaryAbelian 2 (moduleClosure Z) := by
  have hVC : moduleClosure Z ≤ centralizer (pCore 2 H : Set H) := by
    apply normalClosure_le_normal
    apply le_centralizer_iff.mp
    rw [hC]
    exact pCore_isPGroup.le_sylow_of_normal P
  let _ : IsMulCommutative (moduleClosure Z) :=
    le_centralizer_iff_isMulCommutative.mp
      (hVC.trans (centralizer_le (moduleClosure_le_twoCore P Z hC hF)))
  exact IsElementaryAbelian.normalClosure_of_isMulCommutative Z

/-- Factoring out the two-core leaves no normal two-subgroup. -/
theorem coreQuotient_twoCore : pCore 2 (coreQuotient H) = ⊥ := by
  have hker : IsPGroup 2 (coreProjection (H := H)).ker := by
    rw [coreProjection, QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hc := (coreProjection (H := H)).comap_pCore_of_ker_isPGroup
    (QuotientGroup.mk'_surjective _) hker
  apply comap_injective (QuotientGroup.mk'_surjective (pCore 2 H))
  change (pCore 2 (coreQuotient H)).comap (coreProjection (H := H)) =
    (coreProjection (H := H)).ker
  rw [hc, coreProjection, QuotientGroup.ker_mk']

/-- The quotient condition in Definition B.2.11 for the actual normal closure. -/
theorem moduleClosure_reduced (P : Sylow 2 H) (Z : Subgroup H)
    (hC : centralizer (Z : Set H) = (P : Subgroup H)) :
    pCore 2 (H ⧸ centralizer (moduleClosure Z : Set H)) = ⊥ := by
  let e := QuotientGroup.quotientMulEquivOfEq (moduleClosure_centralizer P Z hC)
  have he := pCore_map_iso 2 e
  rw [coreQuotient_twoCore] at he
  exact ((pCore 2 (H ⧸ centralizer (moduleClosure Z : Set H))).map_eq_bot_iff_of_injective e.injective).mp he

variable (P : Sylow 2 H) (Z : Subgroup H)
    [IsElementaryAbelian 2 (moduleClosure Z)]
    (hC : centralizer (Z : Set H) = (P : Subgroup H))

/-- The faithful binary representation on the actual elementary normal closure. -/
noncomputable def quotientAction :
    Representation (ZMod 2) (coreQuotient H) (Additive (moduleClosure Z)) :=
  representation (moduleClosure Z) coreProjection (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (moduleClosure_centralizer P Z hC).symm)

omit [Finite H] in
/-- The descended linear action agrees with multiplication in `I`. -/
theorem quotientAction_apply (g : H) (v : Additive (moduleClosure Z)) :
    ((quotientAction P Z hC (coreProjection g) v).toMul : H) =
      g * (v.toMul : H) * g⁻¹ :=
  representation_apply (moduleClosure Z) coreProjection (QuotientGroup.mk'_surjective _) _ g v

omit [Finite H] in
/-- No nonidentity element of the quotient acts trivially. -/
theorem quotientAction_injective : Function.Injective (quotientAction P Z hC) :=
  representation_injective (moduleClosure Z) coreProjection (QuotientGroup.mk'_surjective _) _

omit [Finite H] [IsElementaryAbelian 2 (moduleClosure Z)] in
include hC in
/-- Any factor moving the seed escapes the action kernel. -/
theorem factor_not_le_twoCore (Y : Subgroup H) (hZY : ⁅Z, Y⁆ ≠ ⊥) :
    ¬ Y ≤ pCore 2 H := by
  intro hY
  apply hZY
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply le_centralizer_iff.mp
  exact hY.trans (by rw [hC]; exact pCore_isPGroup.le_sylow_of_normal P)

omit [Finite H] [IsElementaryAbelian 2 (moduleClosure Z)] in
include hC in
/-- The factor commutator identity forces the Thompson subgroup to act. -/
theorem thompson_not_le_twoCore (Y : Subgroup H)
    (hY : Y = ⁅Y, Stellmacher.elementaryAbelianMaxJ (P : Subgroup H)⁆)
    (hZY : ⁅Z, Y⁆ ≠ ⊥) :
    ¬ Stellmacher.elementaryAbelianMaxJ (P : Subgroup H) ≤ pCore 2 H := by
  intro hJ
  apply factor_not_le_twoCore P Z hC Y hZY
  rw [hY]
  exact (commutator_mono le_rfl hJ).trans (commutator_le_right _ _)

/-- Construct an offender from a maximum elementary subgroup of the specified Sylow group. -/
theorem exists_maxElementary_offender (Y : Subgroup H)
    (hF : generalizedFitting H = pCore 2 H)
    (hY : Y = ⁅Y, Stellmacher.elementaryAbelianMaxJ (P : Subgroup H)⁆)
    (hZY : ⁅Z, Y⁆ ≠ ⊥) :
    ∃ A ∈ Stellmacher.elementaryAbelianMaxSubgroups (P : Subgroup H),
      ¬ A ≤ pCore 2 H ∧ IsOffender (quotientAction P Z hC) (A.map coreProjection) := by
  have hJ := thompson_not_le_twoCore P Z hC Y hY hZY
  have hex : ∃ A ∈ Stellmacher.elementaryAbelianMaxSubgroups (P : Subgroup H),
      ¬ A ≤ pCore 2 H := by
    by_contra! h
    exact hJ (sSup_le h)
  obtain ⟨A, hA, hAn⟩ := hex
  refine ⟨A, hA, hAn, ?_⟩
  apply maxElementary_isOffender (moduleClosure Z) coreProjection
    (QuotientGroup.mk'_surjective _) _ (P : Subgroup H) A
  · exact (moduleClosure_le_twoCore P Z hC hF).trans (pCore_isPGroup.le_sylow_of_normal P)
  · exact hA
  · simpa only [coreProjection, QuotientGroup.ker_mk'] using hAn

/-- The branch produces an FF-module rather than taking one as a premise. -/
theorem quotientAction_isFFModule (Y : Subgroup H)
    (hF : generalizedFitting H = pCore 2 H)
    (hY : Y = ⁅Y, Stellmacher.elementaryAbelianMaxJ (P : Subgroup H)⁆)
    (hZY : ⁅Z, Y⁆ ≠ ⊥) : IsFFModule (quotientAction P Z hC) := by
  obtain ⟨A, _, _, hA⟩ := exists_maxElementary_offender P Z hC Y hF hY hZY
  exact ⟨A.map coreProjection, hA⟩

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch
