module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.LocalC129.ControlIntersection
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.Models
/-!
# The original alternating-three Borel mark

The block quotient has prime order three, so the proper controlled
intersection is exactly the two-core. Under the original quotient model,
this is the full preimage of a point stabilizer in A₃.
Source: Aschbacher–Smith C.1.29, printed p.134, applied in E.6.7, p.246.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06
variable {G : Type*} [Group G] [Finite G]

private theorem a3_stabilizer_eq_bot (i : Fin 3) :
    MulAction.stabilizer (alternatingGroup (Fin 3)) i = ⊥ := by
  apply bot_unique
  intro a ha
  change a = 1
  change (a : Equiv.Perm (Fin 3)) i = i at ha
  have hh : ∀ (a : alternatingGroup (Fin 3)) (i : Fin 3),
      (a : Equiv.Perm (Fin 3)) i = i → a = 1 := by decide +kernel
  exact hh a i ha

theorem alternating_three_block_borel_of_control
    (S : Sylow 2 G) (N L : Subgroup G)
    (hN : (S : Subgroup G).characteristicNormalizerClosure ≤ N)
    (hL : ChapterC.IsBlock L) (hout : ¬ L ≤ N)
    (htype : ChapterC.IsAlternatingBlock L 3) :
    AlternatingBlockBorel L (N.subgroupOf L) 3 := by
  obtain ⟨e⟩ := htype.2.2.quotient_iso
  have hc : Nat.card (L ⧸ pCore 2 L) = 3 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hcore := ChapterC.LocalC129.prime_quotient_intersection_eq_core S N L hN
    hL.subnormal hout (by rw [hc]; exact Nat.prime_three)
  refine ⟨e, 0, ?_⟩
  rw [hcore, a3_stabilizer_eq_bot]
  change pCore 2 L = (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))).ker
  rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']

end CFSG.Quasithin.ChapterE.Section06
