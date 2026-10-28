module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SevenSource.ExceptionalRestriction
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SevenSource.CubicPropagation
public import Theory.Representation.AlternatingSevenFiveSeed.Natural

/-!
# The exceptional A₇ seed propagates on the original Baumann subgroup

The selected A₅ preimage acts naturally on the original moving four-space.
Its actual centralizer kernel has two-power order. The natural source theorem
therefore constructs its Glauberman–Niles local class, retaining central
fixed factors. Equality of Baumann images transfers the original Thompson
movement; normalizer generation then yields a characteristic normal subgroup
or a block on the original component.

The ambient preimage, its quotient image and its residual placement are the
separate central-cover selection step. No shortness or classification callback
is assumed here.

Source: Aschbacher–Smith C.1.24, printed pp.130–131, exceptional branch.
-/

public section
open Subgroup Stellmacher Representation Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.ChapterC.RankOne.Alternating.SevenSource
open ChapterB.QuasisimpleSource
local notation "A7" => alternatingGroup (Fin 7)
variable {G : Type*} [Group G] [Finite G]

/-- The marked source A₅ seed completes the block propagation, including the
original characteristic-subgroup alternative. -/
theorem exceptional_marked_seed_block_alternative
    (T : Sylow 2 G) (L U H : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* A7) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set G))
    (B : Subgroup A7) (hH : H.map q = B) (hUH : U ≤ H)
    (F : BinaryField) (hF : 3 < Nat.card F.Carrier)
    (a : B ≃* SL(2,F.Carrier))
    (p : Additive U ≃ₗ[ZMod 2] (Fin 2 → F.Carrier))
    (he : ∀ (b : B) v,
      p (NormalElementaryQuotient.representation U q hq hk b v) =
        specialLinearNatural 2 (a b) (p v))
    (hk2 : IsPGroup 2 (q.ker.subgroupOf H))
    (hf : generalizedFitting G = pCore 2 G) (hQH : pCore 2 G ≤ H)
    (P : Sylow 2 H)
    (hB : (ChapterB.baumann (P : Subgroup H)).map H.subtype = ChapterB.baumann (T : Subgroup G))
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (hgen : H ⊔ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) = ⊤)
    (hYL : (pResidual 2 H).map H.subtype ≤ L)
    (hL : L.IsSubnormal) (hpL : IsPPerfect 2 L)
    (hfL : generalizedFitting L = pCore 2 L)
    [IsQuasisimple (L ⧸ pCore 2 L)]
    (hne : ¬ (((pResidual 2 H).map H.subtype).subgroupOf L).map
      (QuotientGroup.mk' (pCore 2 L)) ≤ center (L ⧸ pCore 2 L)) :
    (∃ C : Subgroup (ChapterB.baumann (T : Subgroup G)),
      C.Characteristic ∧ C ≠ ⊥ ∧ (C.map (ChapterB.baumann (T : Subgroup G)).subtype).Normal) ∨
      IsBlock L := by
  have hJH := selected_thompson_movement_of_baumann T U H hUH P hB hJ
  have hlocal := exceptional_selected_natural_localClass U q hq hk B H hH hUH
    F hF a p he hk2 hf hQH P hJH
  have hSne : ChapterB.baumann (T : Subgroup G) ≠ ⊥ := by
    intro hs
    apply hJ
    exact (ChapterB.elementaryAbelianMaxJ_le_baumann (T : Subgroup G)).trans
      (hs ▸ bot_le)
  exact CFSG.Quasithin.ChapterC.RankOne.SevenSource.selected_seed_block_alternative
    (T : Subgroup G) L H T.isPGroup' hQH P hB hSne hlocal hgen hYL hL hpL hfL hne

/-- The actual faithful exceptional four-space supplies its own natural A₅
coordinates. Only the separately constructed ambient seed remains explicit. -/
theorem exceptional_four_space_seed_block_alternative
    (T : Sylow 2 G) (L U H : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* A7) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set G))
    (hd : Module.finrank (ZMod 2) (Additive U) = 4)
    (B : Subgroup A7) (eB : B ≃* alternatingGroup (Fin 5))
    (hBN : (T : Subgroup G).map q ≤ normalizer (B : Set A7))
    (hH : H.map q = B) (hUH : U ≤ H)
    (hk2 : IsPGroup 2 (q.ker.subgroupOf H))
    (hf : generalizedFitting G = pCore 2 G) (hQH : pCore 2 G ≤ H)
    (P : Sylow 2 H)
    (hB : (ChapterB.baumann (P : Subgroup H)).map H.subtype = ChapterB.baumann (T : Subgroup G))
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (hgen : H ⊔ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) = ⊤)
    (hYL : (pResidual 2 H).map H.subtype ≤ L)
    (hL : L.IsSubnormal) (hpL : IsPPerfect 2 L)
    (hfL : generalizedFitting L = pCore 2 L)
    [IsQuasisimple (L ⧸ pCore 2 L)]
    (hne : ¬ (((pResidual 2 H).map H.subtype).subgroupOf L).map
      (QuotientGroup.mk' (pCore 2 L)) ≤ center (L ⧸ pCore 2 L)) :
    (∃ C : Subgroup (ChapterB.baumann (T : Subgroup G)),
      C.Characteristic ∧ C ≠ ⊥ ∧ (C.map (ChapterB.baumann (T : Subgroup G)).subtype).Normal) ∨
      IsBlock L := by
  obtain ⟨a,p,he⟩ := Representation.AlternatingSevenFiveSeed.natural_restriction
    (NormalElementaryQuotient.representation U q hq hk)
    (NormalElementaryQuotient.representation_injective U q hq hk) hd B eB
    (T.mapSurjective (f := q) hq) hBN
  let F : BinaryField := {
    Carrier := Representation.SL2FourNatural.F
    degree := 2
    degree_pos := by decide
    card_eq := by rw [Nat.card_eq_fintype_card,Representation.SL2FourNatural.card_field]; decide }
  have hF : 3 < Nat.card F.Carrier := by
    change 3 < Nat.card Representation.SL2FourNatural.F
    rw [Nat.card_eq_fintype_card,Representation.SL2FourNatural.card_field]
    decide
  exact exceptional_marked_seed_block_alternative T L U H q hq hk B hH hUH
    F hF a p he hk2 hf hQH P hB hJ hgen hYL hL hpL hfL hne

end CFSG.Quasithin.ChapterC.RankOne.Alternating.SevenSource
