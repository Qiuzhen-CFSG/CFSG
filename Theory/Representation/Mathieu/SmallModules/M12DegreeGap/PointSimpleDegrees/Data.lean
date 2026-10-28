module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.FinCases

/-!
# Common matrix witnesses for the M₁₁ eleven-coset filtration

These are candidate diagonal blocks for an adapted flag of the native
720-dimensional coset action. There are 33 layers, with degrees 1, 10, 32
and 44. Equal-degree blocks have been aligned by exact binary changes of
basis. Data alone asserts neither invariance nor irreducibility.

The matrices act on COLUMN vectors; bit i of column j is entry (i,j).
The two generators are the existing native A and B, in that order.
See `source/README.md` for discovery, conventions and certificate contracts.
Source: James, J. Algebra 27 (1973), 57–111.
-/

@[expose] public section
namespace Representation.MathieuSmall.M12DegreeGap.PointSimpleDegrees.Data

abbrev Model := Fin 4
abbrev Factor := Fin 33

def modelDegree (i : Model) : ℕ := ![1, 10, 32, 44] i

def factorKinds : Array Model := #[2, 3, 0, 3, 1, 0, 1, 3, 0, 3, 0, 3, 3, 0, 1, 3, 0, 1, 3, 0, 3, 3, 0, 1, 0, 3, 3, 0, 3, 3, 0, 1, 0]

def factorKind (t : Factor) : Model := factorKinds[t.val]!

def degree (t : Factor) : ℕ := modelDegree (factorKind t)

def modelColumns : Array (Array (Array ℕ)) := #[
  #[
  #[1],
  #[1]
],
  #[
  #[271, 453, 971, 358, 286, 487, 391, 295, 614, 878],
  #[769, 378, 44, 776, 735, 368, 291, 582, 677, 421]
],
  #[
  #[893386754, 893386753, 2466250760, 2751463428, 2181169216, 2487353472, 889323536, 2701262880, 2499807232, 2432704512, 2504163328, 608174336, 587464704, 541065728, 3008364544, 2466382848, 2692874240, 826408960, 2705330176, 1061158912, 889208832, 1895825408, 2248146944, 2789408768, 838860800, 2218786816, 67108864, 2970091520, 2453667840, 385875968, 3076521984, 2147483648],
  #[1216356354, 1207967748, 135299088, 1208000544, 1208254465, 1075085568, 142647808, 142648320, 1216393216, 8404992, 8486912, 1217536000, 1082400776, 1209532416, 1085284352, 1220837376, 152346624, 1250951168, 1284775936, 269524992, 1611669504, 1216356416, 135266304, 9478144, 1083187328, 3221520384, 1074044928, 1082138624, 135536640, 142606336, 8691712, 1209042944]
],
  #[
  #[14987254490865, 14987254490866, 14926331490198, 13577455670325, 1088901873291, 16258302080289, 13772637703125, 16258302080385, 14137390741404, 7051402541331, 13283166746726, 14137390743196, 2031470488141, 2289327640057, 7964934151290, 10591480844579, 445392405961, 6282449190681, 12068974786081, 2543629851475, 9045323564861, 16772984201056, 11673838090889, 3405792521088, 11542385401912, 37687900, 6273718389882, 14918887554800, 13873308695483, 8367022716039, 3469150560836, 1717155299208, 6165341069774, 2251672672230, 12184846695516, 15745038022419, 8746951431977, 4805045139413, 3117721593271, 11136213620673, 7300313608753, 11649111338944, 9634074748515, 1990505321863],
  #[7666093155839, 3577165091950, 3218347043372, 11172314610894, 4109548780339, 14176658200522, 5412743876803, 14639980474319, 16461968461052, 5481841435928, 1803963341298, 13710318339906, 10482266175197, 13795603797048, 12462600188486, 451170127739, 5721214622567, 470659165709, 1171354078849, 13230175956452, 2891636220263, 16752094123152, 319496557356, 15329039437678, 5539773025201, 5896433904199, 606530169569, 8969061971068, 5105207452467, 9591265031407, 7084235291270, 4388825389324, 6217163939432, 6938128514145, 17588172536785, 9850825527620, 11723831214298, 1262848394, 4656827320258, 9604498385369, 13563062615019, 14672101457215, 14574268295707, 4249804136665]
]
]

def modelMatrix (i : Model) (s : Fin 2) :
    Matrix (Fin (modelDegree i)) (Fin (modelDegree i)) (ZMod 2) :=
  fun r c => if ((modelColumns[i.val]!)[s.val]!)[c.val]!.testBit r.val then 1 else 0

def factorMatrix (t : Factor) (s : Fin 2) :
    Matrix (Fin (degree t)) (Fin (degree t)) (ZMod 2) := modelMatrix (factorKind t) s

theorem modelDegree_pos (i : Model) : 0 < modelDegree i := by
  fin_cases i <;> decide

theorem degree_pos (t : Factor) : 0 < degree t := modelDegree_pos (factorKind t)

theorem degree_allowed (t : Factor) : degree t ∈ ({1, 10, 32, 44} : Set ℕ) := by
  change modelDegree (factorKind t) ∈ _
  generalize factorKind t = i
  fin_cases i <;> decide

/-- The finite algebra obligation: the two displayed operators have no
proper nonzero common invariant binary subspace. This is not asserted here. -/
def SimpleMatrices : Prop :=
  ∀ (i : Model) (S : Submodule (ZMod 2) (Fin (modelDegree i) → ZMod 2)),
    (∀ (s : Fin 2) (v : Fin (modelDegree i) → ZMod 2),
      v ∈ S → (modelMatrix i s).mulVec v ∈ S) → S = ⊥ ∨ S = ⊤

end Representation.MathieuSmall.M12DegreeGap.PointSimpleDegrees.Data
