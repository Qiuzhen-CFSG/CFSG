module

public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.PointSimpleDegrees.Witness

/-!
# Finite zero-tail and diagonal-slice certificates

These checks need only the published data. The raw endpoint expression
is definitionally the `Model.cut` used by the final matrix interface.
Keeping the finite checks under this narrow import reduces compiler
memory; `Arithmetic` connects them to the unchanged `blockCertificate`.

Source: James, J. Algebra 27 (1973), 57–111; witness conventions in
`PointSimpleDegrees/source/README.md`. Regenerate with `source/generate.py`.
-/

set_option Elab.async false

@[expose] public section
namespace Representation.MathieuSmall.M12DegreeGap.PointSimpleDegrees.CosetFlag.MatrixChecks.BlockChecks
open Data

def certificate (t : Factor) : Prop :=
  ∀ (s : Fin 2) (y : Fin (degree t)),
    (Witness.adaptedColumns[s.val]!)[Witness.endpoints[min t.val 33]! + y.val]! >>>
        Witness.endpoints[min (t.val + 1) 33]! = 0 ∧
    ((Witness.adaptedColumns[s.val]!)[Witness.endpoints[min t.val 33]! + y.val]! >>>
        Witness.endpoints[min t.val 33]!) % 2 ^ degree t =
      ((modelColumns[(factorKind t).val]!)[s.val]!)[y.val]!

private theorem block00 : certificate 0 := by
  unfold certificate
  decide +kernel

private theorem block01 : certificate 1 := by
  unfold certificate
  decide +kernel

private theorem block02 : certificate 2 := by
  unfold certificate
  decide +kernel

private theorem block03 : certificate 3 := by
  unfold certificate
  decide +kernel

private theorem block04 : certificate 4 := by
  unfold certificate
  decide +kernel

private theorem block05 : certificate 5 := by
  unfold certificate
  decide +kernel

private theorem block06 : certificate 6 := by
  unfold certificate
  decide +kernel

private theorem block07 : certificate 7 := by
  unfold certificate
  decide +kernel

private theorem block08 : certificate 8 := by
  unfold certificate
  decide +kernel

private theorem block09 : certificate 9 := by
  unfold certificate
  decide +kernel

private theorem block10 : certificate 10 := by
  unfold certificate
  decide +kernel

private theorem block11 : certificate 11 := by
  unfold certificate
  decide +kernel

private theorem block12 : certificate 12 := by
  unfold certificate
  decide +kernel

private theorem block13 : certificate 13 := by
  unfold certificate
  decide +kernel

private theorem block14 : certificate 14 := by
  unfold certificate
  decide +kernel

private theorem block15 : certificate 15 := by
  unfold certificate
  decide +kernel

private theorem block16 : certificate 16 := by
  unfold certificate
  decide +kernel

private theorem block17 : certificate 17 := by
  unfold certificate
  decide +kernel

private theorem block18 : certificate 18 := by
  unfold certificate
  decide +kernel

private theorem block19 : certificate 19 := by
  unfold certificate
  decide +kernel

private theorem block20 : certificate 20 := by
  unfold certificate
  decide +kernel

private theorem block21 : certificate 21 := by
  unfold certificate
  decide +kernel

private theorem block22 : certificate 22 := by
  unfold certificate
  decide +kernel

private theorem block23 : certificate 23 := by
  unfold certificate
  decide +kernel

private theorem block24 : certificate 24 := by
  unfold certificate
  decide +kernel

private theorem block25 : certificate 25 := by
  unfold certificate
  decide +kernel

private theorem block26 : certificate 26 := by
  unfold certificate
  decide +kernel

private theorem block27 : certificate 27 := by
  unfold certificate
  decide +kernel

private theorem block28 : certificate 28 := by
  unfold certificate
  decide +kernel

private theorem block29 : certificate 29 := by
  unfold certificate
  decide +kernel

private theorem block30 : certificate 30 := by
  unfold certificate
  decide +kernel

private theorem block31 : certificate 31 := by
  unfold certificate
  decide +kernel

private theorem block32 : certificate 32 := by
  unfold certificate
  decide +kernel

/-- Both packed block identities, for every column of every layer. -/
theorem all_blocks (t : Factor) : certificate t := by
  fin_cases t
  · exact block00
  · exact block01
  · exact block02
  · exact block03
  · exact block04
  · exact block05
  · exact block06
  · exact block07
  · exact block08
  · exact block09
  · exact block10
  · exact block11
  · exact block12
  · exact block13
  · exact block14
  · exact block15
  · exact block16
  · exact block17
  · exact block18
  · exact block19
  · exact block20
  · exact block21
  · exact block22
  · exact block23
  · exact block24
  · exact block25
  · exact block26
  · exact block27
  · exact block28
  · exact block29
  · exact block30
  · exact block31
  · exact block32

end Representation.MathieuSmall.M12DegreeGap.PointSimpleDegrees.CosetFlag.MatrixChecks.BlockChecks
