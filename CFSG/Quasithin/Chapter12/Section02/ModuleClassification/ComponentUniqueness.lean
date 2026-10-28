module

public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.Definitions
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalityEvenModelsBinary
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalityOddModels

/-!
# Unique local components in the seven Section 12.2 module rows

All seven literal actors have unique C-components in full Sylow overgroups.
The binary linear rows use the checked flag/Levi calculation through degree
five. The small alternating and triple-six rows use their actual orders;
A₈ uses its binary linear identification, and G₂(2)′ uses its proper Sylow
overgroups. Uniqueness lifts through the actual solvable quotient kernels.

For the alternating rows, that kernel is C_L(V), rather than O₂(L).
Its image in the quasisimple two-core quotient is central: otherwise the
nontrivial central action would vanish. This proves its solvability and
justifies the original-group transport without equating the two kernels.
The H-star application is in LocalConfigurationNaturalHStarSourceRestrictionsNormalization.

Source: Aschbacher–Smith, 1.2.8(1), 12.2.2(3) and 12.2.7, printed
pp.506,795,797. Imported model calculations retain their ATLAS attribution
in LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02
open Chapter1.Section02.MovedMaximality
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual centralizer of the chosen module is solvable when the
component quotient by its two-core is quasisimple. -/
theorem ChosenModule.actionCentralizer_isSolvable
    (D : ChosenModule T L V) (hq : IsQuasisimple (L ⧸ pCore 2 L)) :
    Group.IsSolvable ((centralizer (V : Set G)).subgroupOf L) := by
  let := hq
  let q := QuotientGroup.mk' (pCore 2 L)
  have hk : D.centralQuotientAction.ker ≤ center (L ⧸ pCore 2 L) := by
    apply (IsQuasisimple.normal_le_center_or_eq_top D.centralQuotientAction.ker).resolve_right
    intro ht
    apply D.centralAction_ne_one
    apply MonoidHom.ext
    intro l
    exact DFunLike.congr_fun (D.centralQuotientAction.ker_eq_top_iff.mp ht) (q l)
  have hc : (centralizer (V : Set G)).subgroupOf L ≤
      (center (L ⧸ pCore 2 L)).comap q := by
    intro l hl
    exact hk (D.actionCentralizer_le_centralAction_ker hl)
  let : Group.IsNilpotent (pCore 2 L) := pCore_isNilpotent
  let : Group.IsSolvable q.ker := by
    rw [show q = QuotientGroup.mk' (pCore 2 L) from rfl, QuotientGroup.ker_mk']
    infer_instance
  let := isSolvable_comap_of_solvable_ker q (center (L ⧸ pCore 2 L))
  exact Group.isSolvable_of_isSolvable_injective
    (f := inclusion hc) (inclusion_injective hc)

private theorem alternating_unique {n : ℕ} (hlo : 5 ≤ n) (hhi : n ≤ 8) :
    SylowOvergroupComponentUnique (alternatingGroup (Fin n)) := by
  by_cases h8 : n = 8
  · subst n
    exact alternating_eight_sylow_overgroup_component_unique ⟨MulEquiv.refl _⟩
  · apply SylowOvergroupComponentUnique.of_not_sixteen_dvd_card
    have hn : n = 5 ∨ n = 6 ∨ n = 7 := by omega
    rcases hn with rfl | rfl | rfl <;>
      rw [nat_card_alternatingGroup, Nat.card_fin] <;> decide

/-- Each literal seven-module row gives unique C-components in every
overgroup of an intrinsic full Sylow subgroup of the original component. -/
theorem ChosenModule.sylowOvergroupComponentUnique_of_alternatives
    (D : ChosenModule T L V) (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (rows : ModuleAlternatives1222 D) : SylowOvergroupComponentUnique L := by
  let := hq
  let : Group.IsNilpotent (pCore 2 L) := pCore_isNilpotent
  let : Group.IsSolvable (QuotientGroup.mk' (pCore 2 L)).ker := by
    rw [QuotientGroup.ker_mk']; infer_instance
  have hlinear (n : ℕ) (hn : n ≤ 5)
      (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
      SylowOvergroupComponentUnique L := by
    apply SylowOvergroupComponentUnique.of_surjective (QuotientGroup.mk' (pCore 2 L))
      (QuotientGroup.mk'_surjective _)
    exact SylowOvergroupComponentUnique.of_equiv
      (e.trans (BinaryLinear.OuterCyclic.slEquivLinear n))
      (BinaryLinear.sylow_overgroup_component_unique_le_five n hn)
  let := D.actionCentralizer_normal
  let := D.actionCentralizer_isSolvable hq
  let : Group.IsSolvable (QuotientGroup.mk' ((centralizer (V : Set G)).subgroupOf L)).ker := by
    rw [QuotientGroup.ker_mk']; infer_instance
  have halt (n : ℕ) (hlo : 5 ≤ n) (hhi : n ≤ 8)
      (e : (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin n)) :
      SylowOvergroupComponentUnique L :=
    SylowOvergroupComponentUnique.of_surjective (QuotientGroup.mk' _)
      (QuotientGroup.mk'_surjective _)
      (SylowOvergroupComponentUnique.of_equiv e (alternating_unique hlo hhi))
  cases rows with
  | linear n hn e => exact hlinear n (by omega) e.groupEquiv
  | linearThreeExtension e _ _ => exact hlinear 3 (by decide) e
  | linearFiveExterior e _ _ => exact hlinear 5 (by decide) e
  | alternating n hlo hhi e => exact halt n hlo hhi e.groupEquiv
  | alternatingSevenFour e _ => exact halt 7 (by decide) (by decide) e
  | g2 e =>
    apply SylowOvergroupComponentUnique.of_surjective (QuotientGroup.mk' (pCore 2 L))
      (QuotientGroup.mk'_surjective _)
    let : IsSimpleGroup (commutator (Atlas.G2.Model (ZMod 2))) :=
      Atlas.G2.isSimple_commutator_binary
    let : IsSimpleGroup (L ⧸ pCore 2 L) := e.groupEquiv.isSimpleGroup
    exact binary_g2_derived_sylow_overgroup_component_unique ⟨e.groupEquiv⟩
  | tripleSix e _ _ _ =>
    apply SylowOvergroupComponentUnique.of_surjective (QuotientGroup.mk' (pCore 2 L))
      (QuotientGroup.mk'_surjective _)
    apply SylowOvergroupComponentUnique.of_not_sixteen_dvd_card
    rw [Nat.card_congr e.toEquiv, Atlas.Codes.hexEven_card]
    decide

end CFSG.Quasithin.Chapter12.Section02
