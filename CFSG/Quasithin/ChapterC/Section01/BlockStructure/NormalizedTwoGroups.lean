module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.ModuleLift
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.CoreAction
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Centralizer
public import Theory.GroupTheory.PGroup.SubnormalCore

/-!
# Two-subgroups normalized by a short group

A two-subgroup normalizing and normalized by a short group either contains
its entire commutator layer or centralizes it. Apply irreducibility to the
commutator, then two-perfect commutator idempotence to remove the central case.
For a Sylow two-subgroup T normalizing L, its centralizer of U(L) is exactly
O₂(LT): the centralizer is normalized by both L and T and hence lies in the
local two-core. All normality is relative to the displayed subgroups.

These statements supply the layer and centralizer arguments for the actual
omega-center closure in 3.3.31. Source: Aschbacher–Smith C.1.7–11 and C.6.3,
printed pp.123–124 and166–167.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G] [Finite G]

/-- A mutually normalizing two-subgroup contains the whole layer or centralizes L. -/
theorem IsShort.blockU_le_or_centralizes_of_normalizing_twoGroup
    {L P : Subgroup G} (hL : IsShort L) (hP : IsPGroup 2 P)
    (hLP : L ≤ normalizer (P : Set G)) (hPL : P ≤ normalizer (L : Set G)) :
    (blockU L).map L.subtype ≤ P ∨ P ≤ centralizer (L : Set G) := by
  let A := ⁅P, L⁆
  have hAP : A ≤ P := le_normalizer_iff_commutator_le_left.mp hLP
  have hAL : A ≤ L := le_normalizer_iff_commutator_le_right.mp hPL
  have hcore : A ≤ L.pCoreIn 2 := le_pCoreIn_of_normalizes
    (hP.to_le hAP) hAL (normalizer_commutator_ge_right P L)
  have hid : ⁅A, L⁆ = A := commutator_isPPerfect_idempotent L P hL.twoPerfect hP hLP
  have hAU : A ≤ (blockU L).map L.subtype := by
    rw [blockU, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
    exact hid.symm.le.trans (commutator_mono hcore le_rfl)
  let : (A.subgroupOf L).Normal :=
    normal_subgroupOf_of_le_normalizer (normalizer_commutator_ge_right P L)
  have hAU' : A.subgroupOf L ≤ blockU L := by
    intro x hx
    obtain ⟨y, hy, he⟩ := hAU hx
    exact (Subtype.ext he : y = x) ▸ hy
  rcases RankOne.ChiProduct.short_normal_layer_dichotomy hL (A.subgroupOf L) hAU' with hc | he
  · right
    have hAC : A ≤ centralizer (L : Set G) := by
      intro a ha l hl
      exact congrArg Subtype.val (mem_center_iff.mp
        (hc (show (⟨a, hAL ha⟩ : L) ∈ A.subgroupOf L from ha)) ⟨l, hl⟩)
    exact commutator_eq_bot_iff_le_centralizer.mp
      (hid.symm.trans (commutator_eq_bot_iff_le_centralizer.mpr hAC))
  · left
    have hm := congrArg (map L.subtype) he
    rw [map_subgroupOf_eq_of_le hAL] at hm
    exact hm.symm.le.trans hAP

variable {T : Sylow 2 G} {L : Subgroup G}

omit [Finite G] in
private theorem local_core_le_sylow :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) := by
  simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
    pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)

omit [Finite G] in
private theorem local_join_normalizes_core : L ⊔ (T : Subgroup G) ≤
    normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) :=
  (L ⊔ (T : Subgroup G)).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))

/-- The Sylow centralizer of the short layer is the literal local two-core. -/
theorem IsShort.sylow_centralizer_blockU_eq_pCoreIn
    (hb : IsShort L) (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    (T : Subgroup G) ⊓ centralizer ((ChapterC.blockU L).map L.subtype : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let U := (ChapterC.blockU L).map L.subtype
  let C := (T : Subgroup G) ⊓ centralizer (U : Set G)
  have hLU : L ≤ normalizer (U : Set G) := L.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image L (ChapterC.blockU L))
  have hTU : (T : Subgroup G) ≤ normalizer (U : Set G) :=
    hTL.trans
      (normalizer_le_normalizer_characteristic_image L (ChapterC.blockU L))
  have hCQ : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ centralizer (U : Set G) :=
    hb.normalizing_twoGroup_centralizes_blockU (isPGroup_pCoreIn 2 _)
      (le_sup_left.trans local_join_normalizes_core)
      (local_core_le_sylow.trans hTL)
  have hMQ : L.pCoreIn 2 ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
    apply pCoreAmbient_mono_of_isSubnormalIn L (L ⊔ (T : Subgroup G)) 2 le_sup_left
    exact (normal_subgroupOf_of_le_normalizer
      (sup_le L.le_normalizer hTL)).isSubnormal
  have hCL : ⁅C,L⁆ ≤ L := le_normalizer_iff_commutator_le_right.mp
    (inf_le_left.trans hTL)
  have hCC : ⁅C,L⁆ ≤ centralizer (U : Set G) :=
    (commutator_mono inf_le_right le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp
        (hLU.trans (normalizer_le_normalizer_centralizer U)))
  have hCM : ⁅C,L⁆ ≤ L.pCoreIn 2 := by
    intro x hx
    refine mem_map.mpr ⟨⟨x,hCL hx⟩, hb.centralizer_blockU.le ?_, rfl⟩
    intro u hu
    exact Subtype.ext (hCC hx u (mem_map_of_mem L.subtype hu))
  have hLC : L ≤ normalizer (C : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr
      (hCM.trans (hMQ.trans (le_inf local_core_le_sylow hCQ)))
  have hTC : (T : Subgroup G) ≤ normalizer (C : Set G) :=
    (le_inf (T : Subgroup G).le_normalizer
      (hTU.trans (normalizer_le_normalizer_centralizer U))).trans
      inf_normalizer_le_normalizer_inf
  exact le_antisymm
    (le_pCoreIn_of_normalizes (T.isPGroup'.to_le (show C ≤ T from inf_le_left))
      (inf_le_left.trans le_sup_right) (sup_le hLC hTC))
    (le_inf local_core_le_sylow hCQ)

end CFSG.Quasithin.ChapterC
