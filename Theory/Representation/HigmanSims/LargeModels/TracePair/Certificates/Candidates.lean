module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Marked

/-!
# Candidate null vectors for the degree-896 HS density certificate

The vectors are obtained by exact elimination from
H = A + B + omega² I. They are normalized so that the row pairs to one
with the column. Only that small normalization is checked here. Kernel
identities, the invertible perturbation and the two spanning orbits are
separate finite obligations, not assumptions implicit in these definitions.

Source: the literal ATLAS HSG1-f4r896aB0 matrices in `../source/`.
The candidate generation script and further untrusted witnesses are in `source/`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Certificates

/-- The algebra whose fullness is required by the marked-action consumer. -/
abbrev generated := Algebra.adjoin Four
  ({matrixA, matrixB} : Set (Matrix (Fin 896) (Fin 896) Four))

/-- The singular element used to extract a rank-one projector. -/
def singular : Matrix (Fin 896) (Fin 896) Four :=
  matrixA + matrixB + omega ^ 2 • 1

def nullColumnPacked : ℕ := 33502133219306315133374910248729701975617225173867185098259629076890320386313649128992859378017781885991315835012022062255304039948414747130454863504092041792359952678251645306009006462170244862940564433715578564510326406531297966451322434336453560964969895198087368363869286397398462458879147056205094897540395266436639729844969206977440409847516694316623176242855564676876818748053594200078185267948834410981498674461825406125498177796995311743742968019549393163825920561520520925831043031197702507126595312890369582412396344831353461204

def nullColumn : Fin 896 → Four := fun i => entry nullColumnPacked i.val

def nullRowPacked : ℕ := 244602192123607723892311061251929366029534291457370583318602854482611133472111035021237381458637680222481168070618266568579859512068013436012153182032906622725392849114433317477772720855324333777548810429300936081150436522329941149964589350370443962617221154704622648735685758422196842375938411869623119634441454445597765604373138767522683720260505481433565917878465067540377390007048721918907878581105615516462314373131010618838544176109301839729296418688011180631064554739649946703263887795229319919115453167342277524902630622563492721506

def nullRow : Fin 896 → Four := fun i => entry nullRowPacked i.val

theorem nullPair_normalized : dotProduct nullRow nullColumn = 1 := by decide +kernel

/-- The column orbit under the actual generated algebra. -/
def columnOrbitSpan : Submodule Four (Fin 896 → Four) :=
  Submodule.span Four (Set.range fun L : generated => (L.val).mulVec nullColumn)

/-- The row orbit under the actual generated algebra. -/
def rowOrbitSpan : Submodule Four (Fin 896 → Four) :=
  Submodule.span Four (Set.range fun R : generated => Matrix.vecMul nullRow R.val)

end Representation.HigmanSims.LargeModels.TracePair.Certificates
