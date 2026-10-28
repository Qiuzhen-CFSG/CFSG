module
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Commutation.CubicMovement
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.LocalClass.CubicResidual
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.Movement

/-!
# Cubic residual blocks in the original local class

When the original action kernel is O₂(H) and the residual is an A₃ block,
the moved module lies in the block layer. Its natural quotient has at least
four points, while the block layer has exactly four, giving equality.
Baumann fixedness supplies actual Thompson movement, and the cubic block
commutator theorem lifts this to R=[R,J(T)]. The support is the literal
normal closure of the marked omega center.

Source: Aschbacher--Smith C.1.26--28, printed pp.132--134.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {B H : Type*} [Group B] [Group H] [Finite H] {e : B →* H}

/-- The original moved subgroup is exactly the residual block layer. -/
theorem InLocalClass.moved_eq_cubic_blockU (h : InLocalClass e)
    (hk : localKernel e = pCore 2 H)
    (hb : IsBlock (pResidual 2 H)) (ha : IsAlternatingBlock (pResidual 2 H) 3) :
    moved e = (blockU (pResidual 2 H)).map (pResidual 2 H).subtype := by
  have hc : Nat.card ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) = 3 := by
    obtain ⟨a⟩ := ha.2.2.quotient_iso
    rw [Nat.card_congr a.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    rfl
  have hr : Nat.card (pResidual 2 (LocalStar e)) = 3 := by
    let a := QuotientGroup.quotientMulEquivOfEq hk
    have hm := map_pResidual_of_surjective 2 a.toMonoidHom a.surjective
    calc
      _ = Nat.card ((pResidual 2 (LocalStar e)).map a.toMonoidHom) :=
        (card_map_of_injective a.injective).symm
      _ = Nat.card (pResidual 2 (H ⧸ pCore 2 H)) := by rw [hm]
      _ = Nat.card ((pResidual 2 H).map (QuotientGroup.mk' (pCore 2 H))) := by
        rw [map_pResidual_of_surjective 2 _ (QuotientGroup.mk'_surjective _)]
      _ = Nat.card ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) :=
        (Nat.card_congr (BlockCommutation.coreQuotientEquiv _ hb.subnormal).toEquiv).symm
      _ = 3 := hc
  have hm : moved e ≤ (blockU (pResidual 2 H)).map (pResidual 2 H).subtype := by
    rw [moved_eq_residual_commutator e hk hr, ← hb.ambient_core_commutator]
    exact commutator_mono (h.localV_le_coreOmegaCenter.trans
      (fun x hx => ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1)) le_rfl
  have hu : Nat.card ((blockU (pResidual 2 H)).map (pResidual 2 H).subtype) = 4 := by
    rw [card_subtype, ← hb.short.core_eq_blockU_of_quotient_three hc]
    exact hb.short.core_card_four_of_quotient_three hc
  have hfour : 4 ≤ Nat.card (moved e) := by
    obtain ⟨n,hn,F,_,_,_,hF,⟨m⟩⟩ := h.natural
    have hFtwo : 2 ≤ Nat.card F := Finite.one_lt_card
    calc
      4 ≤ Nat.card (MovedModule e) := by rw [m.module_card]; nlinarith
      _ ≤ Nat.card (moved e) := Nat.card_le_card_of_surjective _
        (QuotientGroup.mk'_surjective (movedFixed e))
  exact eq_of_le_of_card_ge hm (by rw [hu]; exact hfour)

/-- The residual block has support in the original marked normal closure. -/
theorem InLocalClass.cubic_block_support (h : InLocalClass e)
    (hk : localKernel e = pCore 2 H)
    (hb : IsBlock (pResidual 2 H)) (ha : IsAlternatingBlock (pResidual 2 H) 3) :
    (blockU (pResidual 2 H)).map (pResidual 2 H).subtype ≤ localV e := by
  rw [← h.moved_eq_cubic_blockU hk hb ha]
  exact moved_le_localV e

variable [Finite B]
/-- The original Thompson subgroup generates the residual by commutators. -/
theorem InLocalClass.cubic_residual_thompson (h : InLocalClass e)
    (hB : IsBaumannFixed B) (hk : localKernel e = pCore 2 H)
    (hb : IsBlock (pResidual 2 H)) (ha : IsAlternatingBlock (pResidual 2 H) 3)
    (T : Sylow 2 H) (he : e.range = (T : Subgroup H)) :
    pResidual 2 H = ⁅pResidual 2 H,elementaryAbelianMaxJ (T : Subgroup H)⁆ := by
  apply hb.eq_commutator_of_cubic_movement
  · obtain ⟨a⟩ := ha.2.2.quotient_iso
    rw [Nat.card_congr a.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    rfl
  · exact T.isPGroup'.to_le (sSup_le fun _ hA => hA.1)
  · exact le_normalizer_of_normal
  · rw [← h.moved_eq_cubic_blockU hk hb ha]
    exact h.thompson_moves_moved hB T he
end CFSG.Quasithin.ChapterC.GlaubermanNiles
