module

public import Theory.SpecificGroups.Triality.OddFundamentalCentralizer.Centralizer.Lifts
public import Theory.SpecificGroups.Triality.OddFundamentalCentralizer.Centralizer.ElementaryIndex.SplitSetup
public import Theory.SpecificGroups.Triality.OddFundamentalCentralizer.Centralizer.Geometry
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.RingTheory.Nilpotent.Defs

/-!
# Reducing the split centralizer calculation to unipotent matrices

The full inverse-conjugated three-arm subsystem centralizes the central SL₂,
by the checked integral geometry. For the reverse direction on p-elements,
conjugate by the literal central-times-arms Weyl word. A p-element becomes a
unipotent matrix commuting with the two highest-root matrices at parameter 1.
Factoring that matrix in the three-arm product would give the desired reverse
containment after inverse conjugation.

`HighestUnipotentFactorization` records exactly the remaining matrix obligation.
This module does not prove it. The transfer applies in characteristic three
as well and uses no ambient order, model comparison or quotient-center premise.
The actual consumer in `ElementaryIndex` derives relative normality and coprime
index from this obligation using p-element generation and fixed-point descent.

Sources: GLS3 §§2.4, 2.6 (`refs/KGroup/GLS3/chapter2.tex`);
Aschbacher–Smith A.2.17, printed p.39, (*) and the final triality case.
-/

@[expose] public section
noncomputable section
open Matrix
open scoped MatrixGroups
namespace Triality.Standard.OddFundamentalCentralizer.ElementaryIndex
open Parabolics
variable {P : Parameters} (D : PinnedRankOneMaps P) (C : ArmRootCommutation P)

/-- The geometric factorization needed for the index calculation, stated in
the actual Geck matrices. This is an explicit proof obligation, not an instance
or an assertion that the factorization has been established. -/
def HighestUnipotentFactorization : Prop :=
  ∀ g : SplitGroup P, IsNilpotent (Geometry.matrixHom P g - 1) →
    (∀ b : Bool, Commute (Geometry.matrixHom P g)
      (Geometry.highestCurve b (1 : ExtensionField P))) →
    g ∈ (D.armsProduct C).range

/-- The entire complementary split subsystem centralizes the central root SL₂. -/
theorem splitComplementSubgroup_le_splitCentralizer :
    splitComplementSubgroup D C ≤ splitCentralizer D := by
  rintro _ ⟨⟨⟨a, b⟩, c⟩, rfl⟩
  apply Subgroup.mem_centralizer_iff.mpr
  rintro _ ⟨s, rfl⟩
  have h := ((Geometry.conjugatedCentral_commute_arm D C 0 (by decide) s a).mul_right
    (Geometry.conjugatedCentral_commute_arm D C 2 (by decide) s b)).mul_right
      (Geometry.conjugatedCentral_commute_arm D C 3 (by decide) s c)
  have hh := h.map (MulAut.conj (splitHighestWeyl D C)⁻¹).toMonoidHom
  simpa [splitComplementProduct, PinnedRankOneMaps.armsProduct_apply,
    MulAut.conj_apply, mul_assoc] using hh.eq

private theorem matrixHom_conjugatedRoot (b : Bool) (t : ExtensionField P) :
    Geometry.matrixHom P ((MulAut.conj (splitHighestWeyl D C))
      (if b then positiveRoot P 1 t else negativeRoot P 1 t)) =
      Geometry.highestCurve b t := by
  have hc : Geometry.matrixHom P (if b then positiveRoot P 1 t else negativeRoot P 1 t) =
      Geometry.curve 1 b t := by
    cases b
    · exact Geometry.matrixHom_negative P 1 t
    · exact Geometry.matrixHom_positive P 1 t
  change Geometry.matrixHom P (splitHighestWeyl D C * _ * (splitHighestWeyl D C)⁻¹) = _
  have he := Geometry.highest_curve (F := ExtensionField P) b t
  rw [← Geometry.matrixHom_highest D C] at he
  have hw : Geometry.matrixHom P (splitHighestWeyl D C) *
      Geometry.matrixHom P ((splitHighestWeyl D C)⁻¹) = 1 :=
    ((Geometry.matrixHom P).map_mul _ _).symm.trans
      ((congrArg (Geometry.matrixHom P) (mul_inv_cancel (splitHighestWeyl D C))).trans
        (map_one (Geometry.matrixHom P)))
  rw [map_mul, map_mul, hc, he, mul_assoc, hw, mul_one]

/-- An element of p-power order is unipotent in the literal Geck matrices. -/
theorem matrixHom_isNilpotent_sub_one_of_pow (g : SplitGroup P) (n : ℕ)
    (h : g ^ (P.prime ^ n) = 1) : IsNilpotent (Geometry.matrixHom P g - 1) := by
  let : CharP (Matrix Geometry.Integral.Ix Geometry.Integral.Ix (ExtensionField P)) P.prime :=
    charP_of_injective_algebraMap (algebraMap (ExtensionField P) _).injective P.prime
  refine ⟨P.prime ^ n, ?_⟩
  rw [sub_pow_char_pow_of_commute P.prime n (Commute.one_right _),
    ← map_pow, h, map_one, one_pow, sub_self]

/-- Unipotent factorization of the highest-root commutant puts every p-element
of the full split centralizer in the precise inverse-conjugated arm product. -/
theorem split_p_element_mem_of_highest_factorization
    (hf : HighestUnipotentFactorization D C)
    (g : splitCentralizer D) (n : ℕ) (hg : g ^ (P.prime ^ n) = 1) :
    g.val ∈ splitComplementSubgroup D C := by
  let w := splitHighestWeyl D C
  let e := (MulAut.conj w).toMonoidHom
  have hn := matrixHom_isNilpotent_sub_one_of_pow (e g.val) n
    (by
      have h : g.val ^ (P.prime ^ n) = 1 := congrArg Subtype.val hg
      exact (map_pow e g.val _).symm.trans ((congrArg e h).trans (map_one e)))
  have hc (b : Bool) : Commute (Geometry.matrixHom P (e g.val))
      (Geometry.highestCurve b (1 : ExtensionField P)) := by
    have hr : (if b then positiveRoot P 1 (1 : ExtensionField P)
        else negativeRoot P 1 (1 : ExtensionField P)) ∈ (D.hom 1).range := by
      cases b
      · exact ⟨SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0)
          (by decide) 1, D.negative 1 1⟩
      · exact ⟨SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1)
          (by decide) 1, D.positive 1 1⟩
    have h : Commute g.val (if b then positiveRoot P 1 (1 : ExtensionField P)
        else negativeRoot P 1 (1 : ExtensionField P)) :=
      (Subgroup.mem_centralizer_iff.mp g.property _ hr).symm
    have hm := (h.map e).map (Geometry.matrixHom P)
    have he : Geometry.matrixHom P (e (if b then positiveRoot P 1 (1 : ExtensionField P)
        else negativeRoot P 1 (1 : ExtensionField P))) = Geometry.highestCurve b 1 :=
      matrixHom_conjugatedRoot D C b 1
    exact (congrArg (fun A => Commute (Geometry.matrixHom P (e g.val)) A) he).mp hm
  obtain ⟨a, ha⟩ := hf (e g.val) hn hc
  refine ⟨a, ?_⟩
  have h := congrArg (MulAut.conj w⁻¹) ha
  simpa [splitComplementProduct, e, w, MulAut.conj_apply, mul_assoc] using h

end Triality.Standard.OddFundamentalCentralizer.ElementaryIndex
