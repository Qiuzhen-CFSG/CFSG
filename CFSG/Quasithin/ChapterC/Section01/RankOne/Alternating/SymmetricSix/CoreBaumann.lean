module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricSix.CoreSource
public import Stellmacher.BaumannIntermediate
public import CFSG.Quasithin.ChapterB.Section02.UniqueOffender

/-!
# Small Baumann images on the original augmentation module

A trivial Baumann image makes the Thompson subgroup centralize the five-space,
so B.2.10 makes the actual Baumann subgroup normal. In the transposition case,
adjoin O₂(G) to Baum(R). Baumann heredity preserves the same subgroup and
the augmentation version of C.1.24(c) produces a genuine block.

This is the small-image part of the 13.2.2(7) alternative. The literal
Chapter 13 point radical and its doubled-component consumer use this theorem;
the full point-radical image remains a separate source branch.
Source: Aschbacher–Smith C.1.37, pp.141–143, and13.2.2(7), pp.877–878.
-/

public section
open Subgroup Theory.GroupTheory Equiv Stellmacher
namespace CFSG.Quasithin.ChapterC.RankOne.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.TranspositionCubic
variable {G : Type*} [Group G] [Finite G]

/-- The trivial and transposition images of the actual augmentation Baumann
subgroup give the characteristic-normal or genuine block alternative. -/
theorem normal_characteristic_or_block_of_small_core_baumann
    (L V R : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    [IsQuasisimple (L ⧸ pCore 2 L)]
    (hL : L.IsCComponent) (hf : generalizedFitting G = pCore 2 G)
    (hfL : generalizedFitting L = pCore 2 L)
    (T : Sylow 2 G) (hQR : pCore 2 G ≤ R) (hRT : R ≤ T)
    (hprod : ∀ g : G, ∃ l ∈ L, ∃ t ∈ (T : Subgroup G), l*t=g)
    (q : G →* Sym) (hLq : L.map q = alternatingGroup (Fin 6))
    (hk : q.ker = pCore 2 G)
    (e : V ≃* Multiplicative (BinaryPermutation.core (Fin 6)))
    (he : ∀ (g : G) (v : V), (e (MulAut.conjNormal g v)).toAdd =
      BinaryPermutation.coreRepresentation (Fin 6) (q g) (e v).toAdd)
    (hm : ⁅V,L⁆ ≠ ⊥)
    (hsmall : (ChapterB.baumann R).map q = ⊥ ∨
      ∃ r : Sym, r.IsSwap ∧ (ChapterB.baumann R).map q = zpowers r) :
    (∃ C : Subgroup (ChapterB.baumann R), C.Characteristic ∧ C ≠ ⊥ ∧
      (C.map (ChapterB.baumann R).subtype).Normal) ∨ IsBlock L := by
  let B := ChapterB.baumann R
  have hVR : V ≤ R :=
    (show V ≤ pCore 2 G from le_sSup ⟨inferInstance,IsElementaryAbelian.isPGroup 2 V⟩).trans hQR
  have hRne : R ≠ ⊥ := by
    intro hz
    have hV : V = ⊥ := le_bot_iff.mp (hVR.trans_eq hz)
    exact hm (by rw [hV,commutator_bot_left])
  have hker := ChapterB.Offenders.SixCorePoint.kernel_centralizer V q e he
  rcases hsmall with hz | ⟨r,hr,hB⟩
  · left
    have hJ : ChapterB.thompsonJ R 0 ≤ centralizer (V : Set G) := by
      rw [ChapterB.thompsonJ_zero,←hker]
      exact (ChapterB.elementaryAbelianMaxJ_le_baumann R).trans ((Subgroup.map_eq_bot_iff _).mp hz)
    have hc : pCore 2 G = R ⊓ centralizer (V : Set G) := by
      rw [←hker,hk,inf_eq_right.mpr hQR]
    have hnormal := (ChapterB.lemma_B_2_10_centralizing V R hVR hQR hc hJ).2.2.2
    let : Nontrivial B := (nontrivial_iff_ne_bot _).mpr
      (baumann_ne_bot R (T.isPGroup'.to_le hRT) hRne)
    exact ⟨⊤,inferInstance,top_ne_bot,by
      simpa only [←MonoidHom.range_eq_map,range_subtype] using hnormal⟩
  · let R0 := B ⊔ pCore 2 G
    have hR0 : R0 ≤ R := sup_le inf_le_left hQR
    have hb : ChapterB.baumann R0 = B := baumann_eq_of_intermediate R R0 le_sup_left hR0
    have him : R0.map q = zpowers r := by
      rw [Subgroup.map_sup,hB,(Subgroup.map_eq_bot_iff _).mpr hk.symm.le,sup_bot_eq]
    have hh := normal_characteristic_or_block_of_core_six L V R0 hL hf hfL T le_sup_right
      (hR0.trans hRT) hprod q hLq e he hm r hr him
    rw [hb] at hh
    exact hh
end CFSG.Quasithin.ChapterC.RankOne.SymmetricSix
