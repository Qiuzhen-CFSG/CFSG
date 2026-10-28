module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.BinaryAffineCentralCover
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootLocalCover
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.AffineExclusion

/-!
# Faithfulness of the affine root-generated local group

The full local cover maps onto the doubly transitive group of order 144 and
has odd central stem kernel. The degree-nine affine cover theorem kills this
kernel. The actual root-generated subgroup embeds in that cover, so its own
panel projection is injective, even when the simple remainder is not in the
panel kernel. The argument keeps the literal panel maps throughout.

Source: Fong--Seitz I (4A)(c), printed p.19, and (5B)--(5C), pp.25--26.
-/

public noncomputable section
open Subgroup
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

theorem affine_local_cover_injective (j : Fin 2)
    (hs : Group.IsSolvable (localGroup Q split j))
    (hp : Nat.card (Panel Q j) = 9) (hg : Nat.card (localGroup Q split j) = 144) :
    Function.Injective (LocalCover.projection Q split j) := by
  let := hs
  obtain ⟨hf,hk,ho,hd⟩ := LocalCover.central_odd_cover Q split j
  exact BinaryPanel.injective_odd_stem_nine_action
    (localGroup_two_pretransitive Q split j) hp hg (panelBase Q j)
    (LocalCover.projection Q split j) hf hk ho hd

theorem affine_root_image_injective (j : Fin 2)
    (hs : Group.IsSolvable (localGroup Q split j))
    (hp : Nat.card (Panel Q j) = 9) (hg : Nat.card (localGroup Q split j) = 144) :
    Function.Injective (rootImageProjection Q split j) := by
  have hi := affine_local_cover_injective Q split j hs hp hg
  apply (MonoidHom.ker_eq_bot_iff _).mp
  change ((panelAction Q j (rankOne Q split j)
    (rankOne_le_parabolic Q split j)).rangeRestrict).ker = ⊥
  rw [MonoidHom.ker_rangeRestrict,panelAction_ker]
  apply eq_bot_iff.mpr
  intro r hr
  let z : localClosure Q split j := inclusion (rankOne_le_localClosure Q split j) r
  let q := QuotientGroup.mk' (LocalCover.radicalInClosure Q split j)
  have hk : q z ∈ (LocalCover.projection Q split j).ker := by
    rw [LocalCover.projection_ker]
    exact mem_map_of_mem _ hr
  have hz : q z = 1 := mem_bot.mp ((MonoidHom.ker_eq_bot_iff _).mpr hi ▸ hk)
  have hrad : (r : X ⧸ Q.D) ∈ LocalCover.radical Q split j :=
    (QuotientGroup.eq_one_iff z).mp hz
  exact Subtype.ext (disjoint_def.mp (RootLocalCover.rankOne_disjoint_radical Q split j)
    r.property hrad)
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
