module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.FixedSeed
public import CFSG.Quasithin.ChapterB.Section02.Baumann.Basic
public import CFSG.Quasithin.ChapterB.Section02.Thompson.Embedding
public import Theory.Representation.BinaryOffender.Replacement

/-!
# The rank consequence of the A7 ratio-one row in 11.4.2

The linear fixed codimension in the actual centralizer quotient is the
difference of logarithms of the orders of the original module and its
centralizer. Ratio at least one excludes strong offenders. B.2.4(3) then
makes C_T(VK) have full two-rank in T. Since this centralizer is O2(KzT)
and lies in R1, the original R1 and T have equal two-rank.

This proves the rank consequence with the ratio explicit. Recognizing the
natural six-space and proving ratio one remain with the A7 row comparison.
Source: Aschbacher--Smith, 11.4.2, printed p.777, and B.2.4(3).
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven

section Internal
variable {H : Type*} [Group H] [Finite H]

/-- The literal internal action has exactly the source logarithmic codimension. -/
theorem internal_fixedCodim (W A : Subgroup H) [W.Normal] [IsElementaryAbelian 2 W] :
    fixedCodim (ChapterB.InternalThompsonAction.action W)
      (A.map (ChapterB.InternalThompsonAction.actionMk W)) =
        ChapterB.BaumannArgument.fixedCodim W A := by
  let ρ := ChapterB.InternalThompsonAction.action W
  let q := ChapterB.InternalThompsonAction.actionMk W
  have hW : Nat.log 2 (Nat.card W) = Module.finrank (ZMod 2) (Additive W) := by
    change Nat.log 2 (Nat.card (Additive W)) = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      Nat.log_pow Nat.one_lt_two]
  have hC : Nat.log 2 (Nat.card (W ⊓ centralizer (A : Set H) : Subgroup H)) =
      Module.finrank (ZMod 2) (fixedSpace ρ (A.map q)) := by
    rw [←Nat.card_congr (NormalElementaryQuotient.fixedSpaceEquiv W q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) A)]
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      Nat.log_pow Nat.one_lt_two]
    rfl
  change fixedCodim ρ (A.map q) = _
  have hdim := fixedCodim_add_finrank ρ (A.map q)
  unfold ChapterB.BaumannArgument.fixedCodim
  rw [hW,hC]
  omega

/-- The no-strong-offender source hypothesis follows from the actual ratio. -/
theorem internal_no_strong_of_ratio (W R : Subgroup H) [W.Normal]
    [IsElementaryAbelian 2 W]
    (hq : 1 ≤ quadraticRatio (ChapterB.InternalThompsonAction.action W)) :
    ChapterB.BaumannArgument.NoStrongOffenders W R := by
  intro A _ hA hne
  rw [←internal_fixedCodim W A]
  change rank (A.map (ChapterB.InternalThompsonAction.actionMk W)) ≤ _
  by_contra! hlt
  have hs : IsStrongFFModule (ChapterB.InternalThompsonAction.action W) :=
    ⟨_,⟨hne,hA⟩,hlt⟩
  exact (not_lt_of_ge hq) ((isStrongFFModule_iff_quadraticRatio_lt_one _).mp hs)

end Internal

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (E : Closure.Geometry D)

/-- Ratio one on VK forces equality of the original ambient two-ranks. -/
theorem twoRank_radical_eq_sylow_of_ratio
    (h : EarlierGeometry E) (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : E.Kz ≠ E.K) (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G))
    (hq : 1 ≤ quadraticRatio (action E)) :
    ChapterB.twoRank E.R₁ = ChapterB.twoRank (T : Subgroup G) := by
  let P : Subgroup (localGroup E) := sylow E
  have hWP : moduleSubgroup E ≤ P :=
    (module_le_radical E).trans (fun _ hx => radical_le_sylow E hx)
  have hc := (ChapterB.BaumannArgument.centralizer_rank_and_alpha
    (moduleSubgroup E) P hWP (internal_no_strong_of_ratio _ P hq)).1
  have he := (action_structure E h hf hne hstar hcent).1
  change ChapterB.twoRank ((sylow E : Subgroup (localGroup E)) ⊓
    centralizer (moduleSubgroup E : Set (localGroup E))) = ChapterB.twoRank P at hc
  rw [←he] at hc
  have hRP : radical E ≤ P := fun _ hx => radical_le_sylow E hx
  have hlo := Nat.log_mono_right (b := 2)
    (elementaryAbelianMaxOrder_le_and_j_le_of_eq _ _ (intrinsic_core_le_radical E)).1
  have hhi := Nat.log_mono_right (b := 2)
    (elementaryAbelianMaxOrder_le_and_j_le_of_eq _ _ hRP).1
  have hr : ChapterB.twoRank (radical E) = ChapterB.twoRank P := by
    change ChapterB.twoRank (pCore 2 (localGroup E)) ≤ ChapterB.twoRank (radical E) at hlo
    exact le_antisymm hhi (hc ▸ hlo)
  have hRmap : (radical E).map (localGroup E).subtype = E.R₁ :=
    map_subgroupOf_eq_of_le ((radical_le_sylow E).trans le_sup_right)
  have hPmap : P.map (localGroup E).subtype = (T : Subgroup G) := by
    exact map_subgroupOf_eq_of_le le_sup_right
  rw [←hRmap,←hPmap,ChapterB.twoRank_map_injective _ (localGroup E).subtype_injective,
    ChapterB.twoRank_map_injective _ (localGroup E).subtype_injective]
  exact hr

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven
