module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalModuleAction
public import Theory.Representation.NormalElementaryQuotient.NormalMoved

/-!
The literal residual images in the marked terminal quotient are normal, and the
second one is the odd group A₃. Invariance of moved spaces therefore transports
back to normalization of the original subgroup commutators in Y.

These are the subgroup transports in the B.5.6 application at the end of 12.3.1
(Aschbacher–Smith, volume II, printed p.812).
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02 ChapterB.SourceInduction
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
variable {S : Setup T L V} {D : S.LocalAnalysis}
namespace TerminalPoint
variable (P : TerminalPoint S D)

private theorem L2_le_Y : P.L2 ≤ P.Y := le_sup_right.trans le_sup_left

private theorem commutator_map (X : Subgroup G) (hX : X ≤ P.Y) :
    (⁅P.U.subgroupOf P.Y,X.subgroupOf P.Y⁆).map P.Y.subtype = ⁅P.U,X⁆ := by
  rw [map_commutator,map_subgroupOf_eq_of_le P.U_le_Y,map_subgroupOf_eq_of_le hX]

/-- The second residual has the literal odd action image specified by ProductAnalysis. -/
theorem moduleAction_second_odd (A : P.ProductAnalysis) :
    Odd (Nat.card ((P.L2.subgroupOf P.Y).map (QuotientGroup.mk' (pCore 2 P.Y)))) := by
  have hc : Nat.card ((P.L2.subgroupOf P.Y).map (QuotientGroup.mk' (pCore 2 P.Y))) = 3 := by
    rw [← card_map_of_injective (f := A.quotient.toMonoidHom) A.quotient.injective,
      map_map,A.second_image,Nat.card_congr (prodEquiv _ _).toEquiv,
      Nat.card_prod,Nat.card_unique,one_mul,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  rw [hc]
  decide

/-- Both literal residual commutator subgroups are invariant under Y. -/
theorem module_moved_normalized (A : P.ProductAnalysis) (X : Subgroup G)
    (hX : X ≤ P.Y)
    (hn : ((X.subgroupOf P.Y).map
      (A.quotient.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 P.Y)))).Normal) :
    P.Y ≤ normalizer (⁅P.U,X⁆ : Subgroup G) := by
  let q := QuotientGroup.mk' (pCore 2 P.Y)
  let B := (X.subgroupOf P.Y).map q
  have hn' : (B.map A.quotient.toMonoidHom).Normal := by
    simpa only [B,map_map] using hn
  let : B.Normal := hn'.of_map_injective A.quotient.injective
  let : (⁅P.U.subgroupOf P.Y,X.subgroupOf P.Y⁆).Normal :=
    NormalElementaryQuotient.commutator_normal_of_image_normal (P.U.subgroupOf P.Y)
      q (QuotientGroup.mk'_surjective _) ((QuotientGroup.ker_mk' _).trans
        (P.module_centralizer_eq A).symm) (X.subgroupOf P.Y)
  rw [←P.commutator_map X hX]
  have htop : (⊤ : Subgroup P.Y).map P.Y.subtype = P.Y := by
    rw [←MonoidHom.range_eq_map,range_subtype]
  conv_lhs => rw [←htop]
  exact (map_mono (le_normalizer_of_normal : (⊤ : Subgroup P.Y) ≤
    normalizer ((⁅P.U.subgroupOf P.Y,X.subgroupOf P.Y⁆ : Subgroup P.Y) : Set P.Y))).trans
      (le_normalizer_map _)

/-- The crossed normalization premise of the terminal endpoint. -/
theorem module_second_normalized (A : P.ProductAnalysis) :
    P.Y ≤ normalizer (⁅P.U,P.L2⁆ : Subgroup G) := by
  apply P.module_moved_normalized A P.L2 P.L2_le_Y
  rw [A.second_image]
  infer_instance

end TerminalPoint
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
