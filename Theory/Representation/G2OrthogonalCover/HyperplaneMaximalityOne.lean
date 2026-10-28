module

public import Theory.Representation.G2OrthogonalCover.HyperplaneMaximality
import all Theory.Representation.G2OrthogonalCover.HyperplaneOrbits

/-!
# Maximal stabilizers in the orbit of 28 cover hyperplanes

Two short derived-group words fix the norm-one seed and are transitive on
its 27-point complement. Their coordinate formulas and 27 reaching words
are checked by small finite kernel reductions. The point stabilizer is
therefore transitive on its complement, proving primitivity and maximality.

The internal import intentionally reuses the word interpreter and bit
encoding of the companion orbit module; none leaks into the public API.
Only the primitive action required by the source is asserted: no separate
identification of the point stabilizer is needed.

Source: Aschbacher--Smith, Lemma 12.4.8, printed p.815. Root coordinates
retain the attribution in the imported ATLAS port; see LICENSES/ATLAS.txt.
-/

@[expose] public noncomputable section
namespace Atlas.G2.Natural.OrthogonalCover.Hyperplanes
local notation "F" => ZMod 2
local notation "D" => commutator (Model F)

private def xWord : List Bool :=
  [true,false,false,true,false,false,true,false,false,true,true,false,false,true,false,false]
private def yWord : List Bool :=
  [true,true,false,false,true,false,true,false,false,false,true,false,true,false,false]

private def xActor : D := wordElement xWord
private def yActor : D := wordElement yWord

private def stepX (a : Parameters) : Parameters :=
  ![a 0, a 1+a 2, a 1, a 3+a 4, a 3, a 5]
private def stepY (a : Parameters) : Parameters :=
  ![a 1+a 4+1, a 1+a 3+a 4+a 5+1, a 0+a 1+a 2+a 4+1,
    a 0+a 1+a 2+a 4+a 5, a 2+a 3+a 5+1, a 2+a 3+a 4+1]

set_option maxRecDepth 16384 in
private theorem xWord_coordinates : ∀ a : Parameters,
    wordAction xWord a = stepX a := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem yWord_coordinates : ∀ a : Parameters,
    wordAction yWord a = stepY a := by
  decide +kernel

private theorem act_xActor (a : Parameters) : act xActor.val a = stepX a :=
  (act_word xWord a).trans (xWord_coordinates a)
private theorem act_yActor (a : Parameters) : act yActor.val a = stepY a :=
  (act_word yWord a).trans (yWord_coordinates a)

private def localWordAction : List Bool → Parameters → Parameters
  | [], a => a
  | b :: w, a => if b then stepY (localWordAction w a) else stepX (localWordAction w a)
private def localWordElement : List Bool → D
  | [] => 1
  | b :: w => (if b then yActor else xActor) * localWordElement w

private theorem act_localWord (w : List Bool) (a : Parameters) :
    act (localWordElement w).val a = localWordAction w a := by
  induction w with
  | nil => exact act_one a
  | cons b w ih =>
    cases b
    · simp only [localWordElement, Bool.false_eq_true, if_false, Subgroup.coe_mul,
        act_mul, act_xActor, ih, localWordAction]
    · simp only [localWordElement, if_true, Subgroup.coe_mul,
        act_mul, act_yActor, ih, localWordAction]

private def offSeed : Parameters := ![0,0,1,1,0,0]
private def localOrbitWord : Fin 64 → List Bool := ![
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [true,false,true,true],
  [true,false,true],
  [true,false,true,false,false],
  [],
  [],
  [false,true,true,false,false],
  [false,true,true,false],
  [],
  [],
  [false,false],
  [true,false,true,true,false,false],
  [],
  [],
  [false],
  [true,false,true,true,false],
  [true,true,false,false],
  [true,true,false],
  [],
  [],
  [],
  [],
  [],
  [false,true,false],
  [],
  [true,false],
  [],
  [false,false,true,false],
  [],
  [false,false,true],
  [],
  [true,false,false],
  [true,true,false,true,false],
  [],
  [true,false,true,false],
  [],
  [],
  [false,true],
  [false,true,true],
  [],
  [],
  [false,false,true,false,false],
  [true,true,false,true],
  [],
  [],
  [true],
  [true,true,false,true,false,false],
  [],
  [true,true],
  [],
  [],
  [false,true,false,false]]

set_option maxRecDepth 16384 in
private theorem localOrbitWord_correct : ∀ n : Fin 64,
    normClass (decode n) = 1 → decode n ≠ seed 1 →
      localWordAction (localOrbitWord n) offSeed = decode n := by
  decide +kernel

private theorem localWord_fixes_seed (w : List Bool) :
    localWordAction w (seed 1) = seed 1 := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b <;> simp only [localWordAction, Bool.false_eq_true, if_false, if_true, ih]
    all_goals decide +kernel

private theorem exists_seed_fixer_reaching (a : Parameters)
    (ha : normClass a = 1) (hne : a ≠ seed 1) :
    ∃ g : D, act g.val (seed 1) = seed 1 ∧ act g.val offSeed = a := by
  refine ⟨localWordElement (localOrbitWord (encode a)), ?_, ?_⟩
  · rw [act_localWord, localWord_fixes_seed]
  · rw [act_localWord]
    have hh := localOrbitWord_correct (encode a)
    simpa only [decode_encode] using hh (by simpa only [decode_encode] using ha)
      (by simpa only [decode_encode] using hne)

private def baseOne : Fibre 1 := ⟨seed 1, by decide +kernel⟩
private def offBase : Fibre 1 := ⟨offSeed, by decide +kernel⟩

/-- The actual derived action on the norm-one fibre is doubly transitive. -/
private theorem derived_stabilizer_one_transitive :
    ∀ a b : Fibre 1, a ≠ baseOne → b ≠ baseOne →
      ∃ g : D, g • baseOne = baseOne ∧ g • a = b := by
  intro a b ha hb
  obtain ⟨g, hga, hg⟩ := exists_seed_fixer_reaching a.val a.property
    (fun he => ha (Subtype.ext he))
  obtain ⟨h, hha, hh⟩ := exists_seed_fixer_reaching b.val b.property
    (fun he => hb (Subtype.ext he))
  have hgfix : g • baseOne = baseOne := Subtype.ext hga
  have hhfix : h • baseOne = baseOne := Subtype.ext hha
  have hgmove : g • offBase = a := Subtype.ext hg
  have hhmove : h • offBase = b := Subtype.ext hh
  refine ⟨h * g⁻¹, ?_, ?_⟩
  · calc
      (h * g⁻¹) • baseOne = h • (g⁻¹ • (g • baseOne)) :=
        (mul_smul h g⁻¹ baseOne).trans
          (congrArg (fun z => h • (g⁻¹ • z)) hgfix.symm)
      _ = baseOne := by rw [inv_smul_smul, hhfix]
  · calc
      (h * g⁻¹) • a = h • (g⁻¹ • (g • offBase)) :=
        (mul_smul h g⁻¹ a).trans
          (congrArg (fun z => h • (g⁻¹ • z)) hgmove.symm)
      _ = b := by rw [inv_smul_smul, hhmove]

instance derived_primitive_one : MulAction.IsPreprimitive D (Fibre 1) :=
  MulAction.isPreprimitive_of_stabilizer_transitive baseOne
    derived_stabilizer_one_transitive

instance : Nontrivial (Fibre 1) :=
  ⟨⟨baseOne, offBase, by decide +kernel⟩⟩

/-- Actual derived-group stabilizers in the orbit of length 28 are maximal. -/
theorem isCoatom_derived_stabilizer_one (a : Fibre 1) :
    IsCoatom (MulAction.stabilizer D a) :=
  MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive D a

end Atlas.G2.Natural.OrthogonalCover.Hyperplanes
