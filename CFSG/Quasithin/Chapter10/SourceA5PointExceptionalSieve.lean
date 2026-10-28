module
public import CFSG.Quasithin.Chapter10.SourceA5PointCoreCenter
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.ExceptionalSmall

/-!
# Removing the exceptional rank-two carriers from the original point data

The literal image of L in I/Z(I) has a two-core center of order at least
sixteen, so its two-core is nontrivial. This discharges the Ree and Tits
normalizer exclusions directly from the original moved module. Both results
retain the original central quotient and require only the containing-subgroup
inclusion and carrier identification.

Source: Aschbacher–Smith 10.2.9, printed pp.750–751, applying A.3.12.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
open ChapterA.Section03.SourceEmbeddings.FiveLocalFF
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D

private theorem center_image_core_ne_bot
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {I : Subgroup G} (hLI : L ≤ I) :
    pCore 2 ((L.subgroupOf I).map (QuotientGroup.mk' (center I))) ≠ ⊥ := by
  let B := (L.subgroupOf I).map (QuotientGroup.mk' (center I))
  have hlow := source_a5_marked_core_center_card D e hLI (MulEquiv.refl B)
  intro hz
  have hc := (center (pCore 2 B)).card_le_card_group
  have hcard : Nat.card (pCore 2 B) = 1 := by rw [hz,card_bot]
  omega

/-- The original moved-module bound excludes every large Ree central quotient. -/
theorem source_a5_not_ree_containing_quotient
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {I : Subgroup G} (hLI : L ≤ I)
    {m : ℕ} (hm : 1 ≤ m) (eI : (I ⧸ center I) ≃* ReeF4.Model m) : False :=
  ExceptionalSmall.not_ree _ (center_image_core_ne_bot D e hLI)
    (source_a5_containing_center_image_quotient e hLI) hm eI

/-- The original moved-module bound excludes the Tits central quotient. -/
theorem source_a5_not_tits_containing_quotient
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {I : Subgroup G} (hLI : L ≤ I)
    (eI : (I ⧸ center I) ≃* Tits.ParrottGroup) : False :=
  ExceptionalSmall.not_tits _ (center_image_core_ne_bot D e hLI)
    (source_a5_containing_center_image_quotient e hLI) eI

end CFSG.Quasithin.Chapter10
