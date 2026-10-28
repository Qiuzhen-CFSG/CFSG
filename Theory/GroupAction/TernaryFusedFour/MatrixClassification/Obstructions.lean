module

public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Check
public import Theory.GroupAction.TernaryFusedFour.Reduction
/-!
# Matrix obstructions among the certified SL₃(3) nodes

Short positive generator words supply elements of order four in twenty-two
nodes. In five further nodes the literal action on the first coordinate line
separates two involutions: their (0,0) entries are 2 and 1, whereas the entry
homomorphism is constant on internal conjugacy classes. All word calculations
are checked by kernel reduction. No diagnostic subgroup labels are assumed.

Source application: Bender (1974), (4.1), p.225, citing Janko (1966), Lemma 3.1.
-/

namespace TernaryFusedFour.MatrixClassification
open Matrix Matrix.PSL3Three Matrix.PSL3Three.CertifiedEnumeration
open Theory.GroupTheory Theory.GroupTheory.SubgroupEnumeration
open Matrix.PSL3Three.CertifiedEnumeration.CosetCheck
open Matrix.PSL3Three.CertifiedEnumeration.ExtensionCheck (allFin allFin_sound)

public structure FourWitness where
  index : Fin 50
  word : List (Fin (generatorCodes index).length)

@[expose] public def FourWitness.element (w : FourWitness) : SL := evalWord (generator w.index) w.word

@[expose] public def FourWitness.check (w : FourWitness) : Bool :=
  matrixEq (w.element ^ 4).val 1 && !matrixEq (w.element ^ 2).val 1

private theorem evalWord_generator_mem (i : Fin 50) (w : List (Fin (generatorCodes i).length)) :
    evalWord (generator i) w ∈ properNode i := by
  induction w with
  | nil => exact (properNode i).one_mem
  | cons j w ih => exact (properNode i).mul_mem (Subgroup.subset_closure ⟨j, rfl⟩) ih

public theorem FourWitness.sound (w : FourWitness) (h : w.check = true) :
    ∃ x ∈ properNode w.index, orderOf x = 4 := by
  simp only [FourWitness.check, Bool.and_eq_true, Bool.not_eq_true'] at h
  refine ⟨w.element, evalWord_generator_mem _ _, ?_⟩
  apply orderOf_eq_prime_pow (p := 2) (n := 1)
  · intro he
    have hm : (w.element ^ 2).val = (1 : SL).val := congrArg Subtype.val he
    have hh := h.2
    rw [hm] at hh
    have ht : matrixEq (1 : SL).val 1 = true := by decide
    rw [ht] at hh
    contradiction
  · exact Subtype.ext (matrixEq_sound h.1)

@[expose] public def fourWitness : Fin 22 → FourWitness :=
 ![⟨5, (show List (Fin 1) from [0])⟩, ⟨10, (show List (Fin 2) from [0])⟩, ⟨11, (show List (Fin 2) from [0, 1])⟩, ⟨12, (show List (Fin 2) from [0, 0])⟩,
   ⟨19, (show List (Fin 2) from [0])⟩, ⟨25, (show List (Fin 2) from [1])⟩, ⟨26, (show List (Fin 2) from [0, 1])⟩, ⟨28, (show List (Fin 2) from [0])⟩, ⟨29, (show List (Fin 2) from [1])⟩,
   ⟨33, (show List (Fin 2) from [1, 1])⟩, ⟨37, (show List (Fin 2) from [0])⟩, ⟨38, (show List (Fin 2) from [0])⟩, ⟨39, (show List (Fin 2) from [0, 1])⟩, ⟨40, (show List (Fin 2) from [0, 0])⟩,
   ⟨41, (show List (Fin 2) from [0])⟩, ⟨42, (show List (Fin 2) from [1, 1])⟩, ⟨44, (show List (Fin 2) from [0])⟩, ⟨45, (show List (Fin 2) from [1])⟩, ⟨46, (show List (Fin 2) from [1])⟩,
   ⟨47, (show List (Fin 2) from [0])⟩, ⟨48, (show List (Fin 2) from [1, 1])⟩, ⟨49, (show List (Fin 2) from [1, 1])⟩]

private theorem fourWitness_checked : allFin (fun j => (fourWitness j).check) = true := by decide +kernel

public theorem order_four_nodes (j : Fin 22) :
    ∃ x ∈ properNode (fourWitness j).index, orderOf x = 4 :=
  (fourWitness j).sound (allFin_sound fourWitness_checked j)

@[expose] public def lineEntry (H : Subgroup SL) (hH : H ≤ lineStabilizerSL) : H →* ZMod 3 where
  toFun g := g.val.val 0 0
  map_one' := rfl
  map_mul' a b := by
    have hb := (mem_lineStabilizerSL_iff b.val).mp (hH b.property)
    simp [SpecialLinearGroup.coe_mul, mul_apply, Fin.sum_univ_three, hb.1, hb.2]

public structure FusionWitness where
  index : Fin 50
  first : List (Fin (generatorCodes index).length)
  second : List (Fin (generatorCodes index).length)

@[expose] public def FusionWitness.check (w : FusionWitness) : Bool :=
  let x := evalWord (generator w.index) w.first
  let y := evalWord (generator w.index) w.second
  matrixEq (x ^ 2).val 1 && !matrixEq x.val 1 &&
  matrixEq (y ^ 2).val 1 && !matrixEq y.val 1 &&
  decide (x.val 0 0 ≠ y.val 0 0)

public theorem FusionWitness.sound (w : FusionWitness)
    (hline : properNode w.index ≤ lineStabilizerSL) (h : w.check = true) :
    ¬ (∀ t u : properNode w.index, orderOf t = 2 → orderOf u = 2 → IsConj t u) := by
  simp only [FusionWitness.check, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hx2, hx⟩, hy2⟩, hy⟩, hxy⟩ := h
  let x : properNode w.index := ⟨evalWord (generator w.index) w.first, evalWord_generator_mem _ _⟩
  let y : properNode w.index := ⟨evalWord (generator w.index) w.second, evalWord_generator_mem _ _⟩
  have horder (z : properNode w.index) (hz2 : matrixEq (z.val ^ 2).val 1 = true)
      (hz : matrixEq z.val.val 1 = false) : orderOf z = 2 := by
    apply orderOf_eq_prime
    · exact Subtype.ext (Subtype.ext (matrixEq_sound hz2))
    · intro he
      have hh := congrArg (fun g : properNode w.index => g.val.val) he
      rw [hh] at hz
      change matrixEq (1 : SL).val 1 = false at hz
      have ht : matrixEq (1 : SL).val 1 = true := by decide
      rw [ht] at hz
      contradiction
  intro hfuse
  have hc := (lineEntry _ hline).map_isConj (hfuse x y (horder x hx2 hx) (horder y hy2 hy))
  exact hxy (isConj_iff_eq.mp hc)

@[expose] public def fusionWitness : Fin 5 → FusionWitness :=
 ![⟨4, (show List (Fin 2) from [0]), (show List (Fin 2) from [0, 1])⟩, ⟨17, (show List (Fin 2) from [0, 0, 1]), (show List (Fin 2) from [0, 0, 0])⟩,
   ⟨30, (show List (Fin 2) from [0, 1, 0, 1, 0, 1, 1, 1]), (show List (Fin 2) from [1, 0, 1])⟩,
   ⟨31, (show List (Fin 2) from [1, 0, 0, 0, 1]), (show List (Fin 2) from [0, 0, 0, 1, 0, 1, 0, 1])⟩,
   ⟨43, (show List (Fin 2) from [1, 1, 1, 0, 1, 1, 1]), (show List (Fin 2) from [0, 1, 0, 1, 0, 1, 1, 1])⟩]

private theorem fusionWitness_checked : allFin (fun j => (fusionWitness j).check) = true := by decide +kernel

public theorem unfused_nodes (j : Fin 5) :
    ¬ (∀ t u : properNode (fusionWitness j).index,
      orderOf t = 2 → orderOf u = 2 → IsConj t u) := by
  apply (fusionWitness j).sound
  · have hc : candidateIndex (fusionWitness j).index = 0 := by revert j; decide
    have hh := properNode_le_candidate (fusionWitness j).index
    change properNode (fusionWitness j).index ≤ candidate 0
    simpa only [hc] using hh
  · exact allFin_sound fusionWitness_checked j

end TernaryFusedFour.MatrixClassification
