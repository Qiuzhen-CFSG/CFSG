module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Data1792
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.CoordinateDensity

/-!
# A proposed kernel vector and a short algebra element

These are exact data for the structural certificate in `source/README.md`.
The algebra element is a sum of fifteen short words in the original ATLAS
pair. Its membership in every containing algebra and the zeroth coordinate
of the proposed kernel vector are proved here. No kernel, rank, invertibility,
or orbit-spanning assertion is inferred from the external discovery script.

Source matrices: ATLAS M24G1-f2r1792B0.m1/.m2, attributed and hashed in
`../source/README.md`; source application: James, J. Algebra 27 (1973), 57–111.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792
open Matrix

def nucleusBits : Nat := 186512425105640208833563359981986649253372916492979019368987771119186107935437291884423668070741375692166533850193080862629110222040870571657157314302158703742423806843959589995070914461979564359707216301998446991261361307054068955738160965108034118438287523828972509301473931817351813319936232831795760600224819896664432035244590919598607518422851897201880114441312085562327488276350637086255160553174137608269477784955724209907170588505320301527254191853285167922643184099635958876198979595552650890503096617756784488087216928995324362343
def nucleus : Fin 1792 → ZMod 2 := fun i => Thompson.BinaryMatrix.bit nucleusBits i.val

def singular : Matrix (Fin 1792) (Fin 1792) (ZMod 2) :=
  let A := Data1792.first
  let B := Data1792.second
  (A + A*B + B + B*B) * (A*B*B) +
  (1 + A + A*B*B + B) * (A*B) +
  (B*A + B*A*B + B*A*B*B) * (A*B) +
  (A + A*B + B + B*B) * B

theorem singular_mem (Q : Subalgebra (ZMod 2) (Matrix (Fin 1792) (Fin 1792) (ZMod 2)))
    (hA : Data1792.first ∈ Q) (hB : Data1792.second ∈ Q) : singular ∈ Q := by
  have hab := Q.mul_mem hA hB
  have hbb := Q.mul_mem hB hB
  have habb := Q.mul_mem hab hB
  have hba := Q.mul_mem hB hA
  have hbab := Q.mul_mem hba hB
  have hbabb := Q.mul_mem hbab hB
  have h0 := Q.add_mem (Q.add_mem (Q.add_mem hA hab) hB) hbb
  have h1 := Q.add_mem (Q.add_mem (Q.add_mem Q.one_mem hA) habb) hB
  have h2 := Q.add_mem (Q.add_mem hba hbab) hbabb
  exact Q.add_mem (Q.add_mem (Q.add_mem (Q.mul_mem h0 habb) (Q.mul_mem h1 hab))
    (Q.mul_mem h2 hab)) (Q.mul_mem h0 hB)

theorem nucleus_zero : nucleus 0 = 1 := by decide +kernel

def rankOne : Matrix (Fin 1792) (Fin 1792) (ZMod 2) := vecMulVec nucleus (Pi.single 0 1)
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792
