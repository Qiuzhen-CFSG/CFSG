module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Basic
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.CoreUpgrade

/-!
# From the recognized bang quotient to the marked plus quotient

The third isomorphism theorem compares the original quotient maps. A
subnormal PSL₃(2) in I/O₂(I) and the recognition of I/O₃′(I) then discharge
the hypotheses of the kernel-removal theorem. This proves equality of the
two original cores and marks both original local images simultaneously.

The B.5 witness and the F.6 alternative comparison are still required to
construct `BangRecognition`. This module does not assert the source
classification from `Geometry` and `CoreFacts` alone. Those two independent
source branches feed the final assembly owned by this task; the earlier
universal source implications retain their existing Chapter B/F/14.3 owners.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
Lemma 14.7.70, printed pp.1074–1075 (PDF pp.1091–1092).
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison
open Subgroup Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} (c : CriticalPath (L := L) F)

/-- The third isomorphism theorem on the original I, using the proved
functoriality of O₃′ through the two-core quotient. -/
def plusBangQuotientEquiv :
    (((I c) ⧸ pCore 2 (I c)) ⧸ pPrimeCore 3 ((I c) ⧸ pCore 2 (I c))) ≃*
      ((I c) ⧸ pPrimeCore 3 (I c)) :=
  (QuotientGroup.quotientMulEquivOfEq
    (ChapterF.primeToThreeCore_map_quotientTwoCore (G := I c)).symm).trans
      (QuotientGroup.quotientQuotientEquivQuotient (pCore 2 (I c))
        (pPrimeCore 3 (I c)) ChapterF.twoCore_le_primeToThreeCore)

/-- The comparison commutes with the literal original maps. -/
theorem plusBangQuotientEquiv_mk (i : I c) :
    plusBangQuotientEquiv c
      (QuotientGroup.mk' (pPrimeCore 3 ((I c) ⧸ pCore 2 (I c))) (plusMap c i)) =
        bangMap c i := by
  simp only [plusBangQuotientEquiv, MulEquiv.trans_apply]
  rfl

/-- Actual source application of the kernel-removal theorem. The output
uses I/O₂(I), not merely the recognized prime-to-three quotient, and both
parabolic images use its original plus map. -/
theorem core_and_marking_of_bangRecognition (k : CoreFacts c)
    (r : BangRecognition c) :
    pPrimeCore 3 (I c) = pCore 2 (I c) ∧ Nonempty (ParabolicMarking c) := by
  obtain ⟨hr, ⟨e⟩⟩ := plus_equiv_of_subnormal_and_bang
    k.triple.quotient_twoCore k.triple.quotient_twoCore_eq_bot
    ((plusBangQuotientEquiv c).trans r.equiv) r.component r.subnormal r.componentEquiv
  have hm := ChapterF.primeToThreeCore_map_quotientTwoCore (G := I c)
  rw [hr] at hm
  have hc : pPrimeCore 3 (I c) ≤ pCore 2 (I c) := by
    have hh := (Subgroup.map_eq_bot_iff _).mp hm
    rwa [QuotientGroup.ker_mk'] at hh
  exact ⟨le_antisymm hc ChapterF.twoCore_le_primeToThreeCore,
    parabolicMarking_of_plus_equiv c k e⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison
