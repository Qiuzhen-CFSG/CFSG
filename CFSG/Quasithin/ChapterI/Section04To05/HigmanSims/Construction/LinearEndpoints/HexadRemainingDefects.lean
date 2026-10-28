module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.HexadWordDefectCentralizer
public import Theory.SpecificGroups.MathieuAmalgamCompletion.Relators

/-!
# The seven remaining hexad defects

This theorem packages the exact quotient and centralizer obligations for
17–22 and 24.  It does not assert either obligation; it is the native
full-kernel reduction that turns each one into an actual literal relation.
-/

public noncomputable section
open Subgroup Subgroup.CosetWordCertificate
namespace CFSG.Quasithin.HigmanSims
local notation "A6" => alternatingGroup (Fin 6)
local notation "Vec" => Theory.SpecificGroups.SymmetricSix.NaturalModule

theorem remaining_hexad_words_of_defect_centralizers
    {D : Type*} [Group D]
    (q : D→*A6) (k : q.ker≃*Multiplicative Vec)
    (hk : ∀ (g : D) (a : q.ker),
      k (MulAut.conjNormal g a)=Multiplicative.ofAdd
        (Theory.SpecificGroups.SymmetricSix.polarAction (q g).val (k a).toAdd))
    (g : Fin 4→D) (a : D)
    (hfree : ∀ v : Vec,
      Theory.SpecificGroups.SymmetricSix.polarAction (q a).val v=v → v=0)
    (hquot : ∀ i : Fin 27,
      (i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=24) →
      q (eval g (Theory.SpecificGroups.MathieuAmalgamCompletion.relator i))=1)
    (hcentral : ∀ i : Fin 27,
      (i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=24) →
      Commute (eval g (Theory.SpecificGroups.MathieuAmalgamCompletion.relator i)) a) :
    ∀ i : Fin 27,
      (i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=24) →
      eval g (Theory.SpecificGroups.MathieuAmalgamCompletion.relator i)=1 := by
  intro i hi
  exact word_eq_one_of_quotient_eq_one_of_centralizer q k hk g
    (Theory.SpecificGroups.MathieuAmalgamCompletion.relator i) a
    (hquot i hi) hfree (hcentral i hi)

end CFSG.Quasithin.HigmanSims
