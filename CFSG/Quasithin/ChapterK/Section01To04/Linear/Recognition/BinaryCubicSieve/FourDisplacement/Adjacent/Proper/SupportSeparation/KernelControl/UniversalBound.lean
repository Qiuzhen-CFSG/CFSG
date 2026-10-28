module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Adjacent.Proper.SupportSeparation.KernelControl.Quotient
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Adjacent.Proper.SupportSeparation.KernelControl.UniversalBound.FlagRank
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Adjacent.Proper.SupportSeparation.KernelControl.UniversalBound.Generators
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Adjacent.Proper.SupportSeparation.KernelControl.UniversalBound.FlagLift

/-!
# The proper adjacent universal quotient has dimension at most 21

The auxiliary flag presentation has dimension at most 21 by an explicit
kernel-checked rank certificate. A geometric evaluation agreeing with the
regular basis on the first two columns of every determinant-one matrix
surjects onto the original universal quotient. Descending this evaluation
therefore gives the required dimension inequality.

`FlagLift` constructs this evaluation from the literal highest-vector relations,
proving independence of matrix representatives and second-coordinate linearity.
Applying it to the quotient map proves the unconditional bound for `Universal`.
This discharges the dimension premise of
`kernel_displacements_of_universal_finrank_le` in the parent assembly; it does
not identify the universal quotient with the twenty-dimensional tensor orbit.

Source application: Aschbacher–Smith, K.3.2, printed pp.451,454–455;
Guralnick–Malle, Classification of 2F-modules II, author manuscript,
Proposition 4.8(3), pp.27–28. This is a finite binary highest-vector calculation,
not an invocation of an absolute highest-weight classification.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.SupportSeparation.KernelControl
open FlagPresentation

open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules

/-- Linearity in the second flag coordinate and the two geometric relations
suffice, provided the map agrees with the literal regular quotient on matrix
columns. `exists_universal_flag_evaluation` supplies such a map. -/
theorem universal_finrank_le_of_flag_evaluation
    (f : Point → Point →ₗ[ZMod 2] Universal)
    (hz : f 0 = 0) (hd : ∀ a, f a a = 0)
    (hp : ∀ a b, f a b + f b a + f (a + b) b = 0)
    (hvalue : ∀ g : Group,
      f (fun i => g.val i 0) (fun i => g.val i 1) =
        relations.mkQ (MonoidAlgebra.single g 1)) :
    Module.finrank (ZMod 2) Universal ≤ 21 := by
  have hsingle (g : Group) : relations.mkQ (MonoidAlgebra.single g 1) ∈
      (evaluate f).range := by
    obtain ⟨a, ha⟩ := point_surjective (fun i => g.val i 0)
    obtain ⟨b, hb⟩ := point_surjective (fun i => g.val i 1)
    refine ⟨pairVector a b, ?_⟩
    rw [evaluate_pairVector, ha, hb, hvalue]
  have hrange (x : Free) : relations.mkQ x ∈ (evaluate f).range := by
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simpa using (evaluate f).range.add_mem hx hy
    | single g c =>
      have he : MonoidAlgebra.single g c = c • MonoidAlgebra.single g (1 : ZMod 2) := by
        simp
      rw [he, map_smul]
      exact (evaluate f).range.smul_mem c (hsingle g)
  let q : FlagQuotient →ₗ[ZMod 2] Universal :=
    relationSpace.liftQ (evaluate f) (relationSpace_le_ker f hz hd hp)
  have hq : Function.Surjective q := by
    intro u
    obtain ⟨x, rfl⟩ := relations.mkQ_surjective u
    obtain ⟨y, hy⟩ := hrange x
    exact ⟨relationSpace.mkQ y, hy⟩
  exact (LinearMap.finrank_le_finrank_of_surjective hq).trans flagQuotient_finrank_le_twenty_one

/-- The original regular module modulo all translated proper adjacent relations
has dimension at most twenty-one over the binary field. -/
theorem universal_finrank_le_twenty_one : Module.finrank (ZMod 2) Universal ≤ 21 := by
  obtain ⟨f, hz, hd, hp, hvalue⟩ := exists_universal_flag_evaluation
  exact universal_finrank_le_of_flag_evaluation f hz hd hp hvalue

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.SupportSeparation.KernelControl
