module

public import CFSG.Quasithin.ChapterC.Section01.BlockDefs
public import Theory.GroupAction.SubgroupQuotientFullAction
public import Theory.ElementaryAbelian.Quotient

/-!
# Elementary structure of short groups

We construct the actual conjugation action on Ũ(L) and establish the
elementary consequences of C.1.7. In particular O₂(L)/U(L) is central in
L/U(L), the first step of C.1.8. Quotients retain two-perfection. These
conclusions follow from commutator functoriality, without assuming the later
block structure or commuting-block theorems.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.7–8,
printed p.123.
-/

public section

namespace CFSG.Quasithin.ChapterC

open Subgroup Theory.GroupTheory

variable {L : Type*} [Group L]

theorem blockU_le_core : blockU L ≤ pCore 2 L :=
  commutator_le_left _ _

instance blockU_characteristic : (blockU L).Characteristic :=
  inferInstanceAs (⁅pCore 2 L, (⊤ : Subgroup L)⁆).Characteristic

theorem blockFixed_map : (blockFixed L).map (blockU L).subtype =
    blockU L ⊓ center L := by
  rw [blockFixed, subgroupOf_map_subtype, inf_comm]

/-- The central layer occurring in C.1.8. -/
theorem blockU_core_image_le_center :
    (pCore 2 L).map (QuotientGroup.mk' (blockU L)) ≤ center (L ⧸ blockU L) := by
  rw [← commutator_top_right_eq_bot_iff_le_center]
  have ht : (⊤ : Subgroup L).map (QuotientGroup.mk' (blockU L)) = ⊤ := by
    rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
    exact QuotientGroup.mk'_surjective _
  rw [← ht, ← map_commutator]
  change (blockU L).map (QuotientGroup.mk' (blockU L)) = ⊥
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']

theorem IsShort.residual_eq_top (h : IsShort L) : pResidual 2 L = ⊤ :=
  (pResidual_eq_top_iff 2 L).mpr h.twoPerfect

theorem IsShort.quotient_twoPerfect (h : IsShort L) (N : Subgroup L) [N.Normal] :
    IsPPerfect 2 (L ⧸ N) :=
  h.twoPerfect.of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

theorem IsShort.blockU_ne_bot (h : IsShort L) : blockU L ≠ ⊥ := by
  intro heq
  have hi := h.irreducible.1
  rw [heq, bot_inf_eq] at hi
  exact lt_irrefl _ hi

theorem IsShort.blockFixed_ne_top (h : IsShort L) : blockFixed L ≠ ⊤ := by
  intro heq
  have hm := blockFixed_map (L := L)
  rw [heq, ← MonoidHom.range_eq_map, range_subtype] at hm
  exact h.irreducible.1.ne hm.symm

theorem IsShort.module_nontrivial (h : IsShort L) : Nontrivial (BlockModule L) :=
  QuotientGroup.nontrivial_iff.mpr h.blockFixed_ne_top

theorem IsShort.module_elementary (h : IsShort L) :
    IsElementaryAbelian 2 (BlockModule L) := by
  let := h.elementary
  infer_instance

theorem IsShort.core_ne_bot (h : IsShort L) : pCore 2 L ≠ ⊥ := by
  intro hbot
  apply h.blockU_ne_bot
  exact le_bot_iff.mp (hbot ▸ blockU_le_core)

theorem IsShort.core_centralizes_blockU (h : IsShort L) :
    pCore 2 L ≤ centralizer (blockU L : Set L) :=
  le_centralizer_iff.mp h.central

/-- The module quotient carries the literal conjugation action. -/
theorem exists_blockModuleAction :
    ∃ ρ : L →* MulAut (BlockModule L), ∀ (l : L) (u : blockU L),
      ρ l (QuotientGroup.mk' (blockFixed L) u) =
        QuotientGroup.mk' (blockFixed L) (blockConjugate L l u) := by
  obtain ⟨ρ, hρ⟩ := exists_quotient_conjugation_action
    (⊤ : Subgroup L) (blockU L) (center L)
    (by rw [normalizer_eq_top]) (by rw [normalizer_eq_top]) inferInstance
  refine ⟨ρ.comp topEquiv.symm.toMonoidHom, ?_⟩
  intro l u
  exact hρ ⟨l, mem_top l⟩ u

/-- Every literal conjugation action on Ũ(L) kills O₂(L). -/
theorem IsShort.core_le_moduleAction_ker (h : IsShort L)
    (ρ : L →* MulAut (BlockModule L))
    (hρ : ∀ (l : L) (u : blockU L),
      ρ l (QuotientGroup.mk' (blockFixed L) u) =
        QuotientGroup.mk' (blockFixed L) (blockConjugate L l u)) :
    pCore 2 L ≤ ρ.ker := by
  intro l hl
  apply MonoidHom.mem_ker.mpr
  ext v
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (blockFixed L) v
  rw [hρ]
  have hconj : blockConjugate L l u = u := by
    apply Subtype.ext
    change l * (u : L) * l⁻¹ = (u : L)
    rw [mem_centralizer_iff.mp (h.central u.property) l hl, mul_inv_cancel_right]
  rw [hconj]
  rfl

/-- Thus the natural action is an action of the actual core quotient. -/
theorem IsShort.exists_quotient_moduleAction (h : IsShort L) :
    ∃ ρ : (L ⧸ pCore 2 L) →* MulAut (BlockModule L),
      ∀ (l : L) (u : blockU L),
      ρ (QuotientGroup.mk' (pCore 2 L) l) (QuotientGroup.mk' (blockFixed L) u) =
        QuotientGroup.mk' (blockFixed L) (blockConjugate L l u) := by
  obtain ⟨ρ, hρ⟩ := exists_blockModuleAction (L := L)
  exact ⟨QuotientGroup.lift (pCore 2 L) ρ (h.core_le_moduleAction_ker ρ hρ), hρ⟩

end CFSG.Quasithin.ChapterC
