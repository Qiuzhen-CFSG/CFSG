module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.Nonsolvable.Component

/-!
# Recognition in the whole-component dihedral row

When F* is the whole bang quotient, the retained small image fills it.
A₅ has Sylow two-subgroups of order four. Excluding that order therefore
identifies the original small subgroup as SL₃(2), giving both an ambient
bang equivalence and the subnormal PSL₃(2) in the original plus quotient.
The same comparison excludes a Sylow of order 32 by divisibility.

Source: Aschbacher–Smith, Lemma 14.7.70, printed p.1075, using
F.6.18(6),(10), printed pp.309–310.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.Nonsolvable
open Representation Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (c : CriticalPath (L := L) F)

/-- Row (6)'s full component and Sylow order recognize the bang quotient
using the original witness. The A₅ possibility has Sylow order four. -/
theorem recognition_of_fitting_top (small : SmallSubnormal c)
    (hq : IsQuasisimple (generalizedFitting ((I c) ⧸ pPrimeCore 3 (I c))))
    (ht : generalizedFitting ((I c) ⧸ pPrimeCore 3 (I c)) = ⊤)
    (S : Sylow 2 ((I c) ⧸ pPrimeCore 3 (I c))) (hS : Nat.card S ≠ 4) :
    Nonempty (BangRecognition c) := by
  obtain ⟨K, hK, hm, hN, hmN⟩ := retained_small_image c small
  obtain ⟨he, hs | hs⟩ := fitting_eq_small (K.map (plusToBang c)) hN hmN hq
  · obtain ⟨e⟩ := hs
    exact recognition_of_image_eq_top c K hK ((smallImageEquiv c K hm).trans e)
      (he.symm.trans ht)
  · obtain ⟨e⟩ := hs
    have hcard : Nat.card ((I c) ⧸ pPrimeCore 3 (I c)) = 60 := by
      have a : ((I c) ⧸ pPrimeCore 3 (I c)) ≃* alternatingGroup (Fin 5) :=
        topEquiv.symm.trans ((MulEquiv.subgroupCongr (he.symm.trans ht)).symm.trans e)
      rw [Nat.card_congr a.toEquiv, nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    apply (hS _).elim
    rw [S.card_eq_multiplicity, hcard]
    decide +kernel

/-- The whole-component rows permit only the two small ambient orders. -/
theorem card_of_fitting_top (small : SmallSubnormal c)
    (hq : IsQuasisimple (generalizedFitting ((I c) ⧸ pPrimeCore 3 (I c))))
    (ht : generalizedFitting ((I c) ⧸ pPrimeCore 3 (I c)) = ⊤) :
    Nat.card ((I c) ⧸ pPrimeCore 3 (I c)) = 168 ∨
      Nat.card ((I c) ⧸ pPrimeCore 3 (I c)) = 60 := by
  obtain ⟨K, _, _, hN, hmN⟩ := retained_small_image c small
  have hm := fitting_small_models (K.map (plusToBang c)) hN hmN hq
  have a : ((I c) ⧸ pPrimeCore 3 (I c)) ≃*
      generalizedFitting ((I c) ⧸ pPrimeCore 3 (I c)) :=
    topEquiv.symm.trans (MulEquiv.subgroupCongr ht).symm
  rcases hm with he | he <;> obtain ⟨e⟩ := he
  · exact Or.inl ((Nat.card_congr (a.trans e).toEquiv).trans Matrix.PSL3Two.card_SL)
  · right
    rw [Nat.card_congr (a.trans e).toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]

/-- Row (10)'s Sylow group has order 32, excluding both small ambient orders. -/
theorem not_sylow_thirtyTwo_of_fitting_top (small : SmallSubnormal c)
    (hq : IsQuasisimple (generalizedFitting ((I c) ⧸ pPrimeCore 3 (I c))))
    (ht : generalizedFitting ((I c) ⧸ pPrimeCore 3 (I c)) = ⊤)
    (S : Sylow 2 ((I c) ⧸ pPrimeCore 3 (I c))) : Nat.card S ≠ 32 := by
  intro hS
  have hd := (S : Subgroup ((I c) ⧸ pPrimeCore 3 (I c))).card_subgroup_dvd_card
  rcases card_of_fitting_top c small hq ht with hc | hc <;>
    rw [hS, hc] at hd <;> norm_num at hd

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.Nonsolvable
