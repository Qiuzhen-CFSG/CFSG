module

public import Theory.Representation.G2OrthogonalCover.HyperplaneCoordinates
public import Theory.Representation.FirstCohomologyG2Natural.BinaryPair

/-!
# The two derived-G₂ orbits on binary cover hyperplanes

Two existing explicit commutators act affinely on the 64 canonical hyperplane
parameters. A kernel-checked table of words of length at most nine reaches
all 36 norm-zero and all 28 norm-one parameters. The literal hyperplane image
formula then gives the intended seven-dimensional orbit theorem, rather than
an assertion about hyperplanes in the natural six-dimensional quotient.

Source: Aschbacher--Smith, Lemma 12.4.8, printed p.815, citing Aschbacher
(1987), Theorems 2--3. Root coordinates retain the attribution in the imported
ATLAS port; see LICENSES/ATLAS.txt.
-/

@[expose] public section

namespace Atlas.G2.Natural.OrthogonalCover.Hyperplanes

local notation "F" => ZMod 2
local notation "D" => commutator (Model F)

def stepA (a : Parameters) : Parameters :=
  ![a 0 + a 2 + a 5 + 1, a 1 + a 3 + a 4 + a 5 + 1,
    a 2 + a 4, a 3 + a 5, a 4, a 5]

def stepB (a : Parameters) : Parameters :=
  ![a 3, a 5, a 1, a 4, a 0, a 2]

theorem act_binaryA (a : Parameters) :
    act (binaryA F).val a = stepA a := by
  change coordinates ((binaryA F).val.val (representative a)) = _
  rw [binaryA_apply]
  funext i
  fin_cases i <;> simp [coordinates, representative, stepA, add_assoc, add_comm]

theorem act_binaryB (a : Parameters) :
    act (binaryB F).val a = stepB a := by
  change coordinates ((binaryB F).val.val (representative a)) = _
  rw [binaryB_apply]
  rfl

private def wordAction : List Bool → Parameters → Parameters
  | [], a => a
  | b :: w, a => if b then stepB (wordAction w a) else stepA (wordAction w a)

private def wordElement : List Bool → D
  | [] => 1
  | b :: w => (if b then binaryB F else binaryA F) * wordElement w

private theorem act_word (w : List Bool) (a : Parameters) :
    act (wordElement w).val a = wordAction w a := by
  induction w with
  | nil => exact act_one a
  | cons b w ih =>
    cases b
    · simp only [wordElement, Bool.false_eq_true, if_false, Subgroup.coe_mul, act_mul,
        act_binaryA, ih, wordAction]
    · simp only [wordElement, if_true, Subgroup.coe_mul, act_mul,
        act_binaryB, ih, wordAction]

private def decode (n : Fin 64) : Parameters := fun i => (n.val / 2 ^ i.val : ℕ)

private def encode (a : Parameters) : Fin 64 :=
  Fin.ofNat 64 ((a 0).val + 2 * (a 1).val + 4 * (a 2).val +
    8 * (a 3).val + 16 * (a 4).val + 32 * (a 5).val)

/-- Canonical representatives of the two affine norm classes. -/
def seed (q : F) : Parameters := ![q, 0, 0, 0, 0, q]

private def orbitWord : Fin 64 → List Bool := ![
  [],
  [true,true,false,true,false],
  [false,true,true,false,true,false],
  [false],
  [false,true,false,true,true,false],
  [false,true,false,false,true,true,false],
  [true,false,true,true,false],
  [true,false,false,true,true,false],
  [true,false,true,false],
  [false,true,false,true,false],
  [false,true,true,false,false,true,false],
  [true,true,false,false,true,false],
  [true,true],
  [true,false,true,true,false],
  [true,false,false,false,true,false,true],
  [true,false,false,true,false,false,true,true,false],
  [false,true,false],
  [false,false,false,true,false],
  [true],
  [true,false],
  [true,false],
  [false,false,true,false],
  [true,false,false],
  [false,true],
  [true,false,false,false,true,false],
  [false,false,true,false,false,false,true,false],
  [false,true,true,false],
  [false,false,false,true,true,false],
  [true,true,false],
  [false,false,true,true,false],
  [false,false,false,true,false,false,false,true,false],
  [false,true,false,false,false,true,false],
  [false,false,false,true,true,false],
  [],
  [false,true,true,false],
  [false,false],
  [true,true,false,true,true,false],
  [false,false,false,true,true,false,false],
  [false,false,true,true,false,true,true,false],
  [false,true,true,false,false],
  [true,true,false],
  [false],
  [false,false,true,true,false],
  [false,false,false],
  [true,true,false,false],
  [false,true,true,false,true,true,false],
  [false,false,true,true,false,false],
  [false,false,false,true,true,false,true,true,false],
  [true,false,true,false,false,true,true,false],
  [false,true,false,true],
  [false,false,false,true,false,true],
  [true,false,true,true,false,true,true,false],
  [false,true,false,false,true,false],
  [false,true,false,false,true,true,false],
  [true,false,true,true,false,false],
  [false,false,false,true,false,false,true,false],
  [true,false,false,true,false],
  [true,false,false,true,true,false],
  [false,false,true,false,false,true,true,false],
  [false,false,true,false,false,true,false],
  [true,false,true],
  [true,false,true,false,false,false,true,false],
  [true,false,false,false,true,false,false,true,false],
  [false,false,true,false,true]]

set_option maxRecDepth 16384 in
private theorem decode_encode : ∀ a : Parameters, decode (encode a) = a := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem orbitWord_correct : ∀ n : Fin 64,
    wordAction (orbitWord n) (seed (normClass (decode n))) = decode n := by
  decide +kernel

/-- Every parameter is reached by an actual derived-group word from its norm seed. -/
theorem exists_derived_seed (a : Parameters) :
    ∃ g : D, act g.val (seed (normClass a)) = a := by
  refine ⟨wordElement (orbitWord (encode a)), ?_⟩
  rw [act_word]
  have hh := orbitWord_correct (encode a)
  simpa only [decode_encode] using hh

/-- Equality of the two affine norm labels exactly characterizes derived orbits. -/
theorem exists_derived_act_iff (a b : Parameters) :
    (∃ g : D, act g.val a = b) ↔ normClass a = normClass b := by
  constructor
  · rintro ⟨g, hg⟩
    exact (normClass_act g.val a).symm.trans (congrArg normClass hg)
  · intro he
    obtain ⟨g, hg⟩ := exists_derived_seed a
    obtain ⟨h, hh⟩ := exists_derived_seed b
    have hginv : act g.val⁻¹ a = seed (normClass a) := by
      conv_lhs => rw [← hg]
      rw [← act_mul, inv_mul_cancel, act_one]
    refine ⟨h * g⁻¹, ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_inv, act_mul, hginv, he]
    exact hh

/-- The two norm classes have the source orbit lengths 36 and 28. -/
theorem normClass_cards :
    Fintype.card {a : Parameters // normClass a = 0} = 36 ∧
      Fintype.card {a : Parameters // normClass a = 1} = 28 := by
  constructor <;> decide +kernel

/-- The orbit statement concerns literal hyperplanes in the seven-space. -/
theorem exists_derived_map_hyperplane_iff (a b : Parameters) :
    (∃ g : D, (hyperplane a).map (traceZeroAction F g.val) = hyperplane b) ↔
      normClass a = normClass b := by
  simp only [map_hyperplane, hyperplane_injective.eq_iff]
  exact exists_derived_act_iff a b

end Atlas.G2.Natural.OrthogonalCover.Hyperplanes
