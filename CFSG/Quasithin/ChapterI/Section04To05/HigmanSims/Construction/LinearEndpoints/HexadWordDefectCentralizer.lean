module

public import Theory.SpecificGroups.SymmetricSix.PolarAffine.FixedFreeCentralizerPower
public import Theory.SpecificGroups.SymmetricSix.HexadCubicWord

/-!
# A generic kernel-defect bridge for the remaining hexad words

For each remaining literal word, the quotient calculation gives a trivial
word.  If its actual lift centralizes the fixed-point-free endpoint actor,
the whole kernel defect is killed without choosing a complement.
-/

public noncomputable section
open Subgroup Subgroup.CosetWordCertificate
namespace CFSG.Quasithin.HigmanSims
local notation "A6" => alternatingGroup (Fin 6)
local notation "Vec" => Theory.SpecificGroups.SymmetricSix.NaturalModule

theorem word_eq_one_of_quotient_eq_one_of_centralizer
    {D : Type*} [Group D]
    (q : D→*A6) (k : q.ker≃*Multiplicative Vec)
    (hk : ∀ (g : D) (a : q.ker),
      k (MulAut.conjNormal g a)=Multiplicative.ofAdd
        (Theory.SpecificGroups.SymmetricSix.polarAction (q g).val (k a).toAdd))
    (g : Fin 4→D) (w : Word (Fin 4)) (a : D)
    (hquot : q (eval g w)=1)
    (hfree : ∀ v : Vec,
      Theory.SpecificGroups.SymmetricSix.polarAction (q a).val v=v → v=0)
    (hcentral : Commute (eval g w) a) : eval g w=1 := by
  have hpow : (q (eval g w))^1=1 := by simpa using hquot
  have hword :=
    Theory.SpecificGroups.SymmetricSix.PolarAffine.power_eq_one_of_quotient_power_of_centralizer_fixed_free
      q k hk (eval g w) a 1 hpow hfree (by simpa using hcentral)
  simpa using hword

end CFSG.Quasithin.HigmanSims
