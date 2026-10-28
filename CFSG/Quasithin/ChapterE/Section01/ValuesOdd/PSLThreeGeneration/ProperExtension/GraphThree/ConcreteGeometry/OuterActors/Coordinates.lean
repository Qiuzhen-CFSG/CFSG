module
public import Theory.SpecificGroups.PSL3Three.GraphLocalQuotients
public import Theory.SpecificGroups.PSL3.OddPrimeGraphExtension.GraphLargeStructure
public import Theory.SpecificGroups.PSL3Three.Cardinality
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.OuterActors.Coordinates.Table

/-!
# A 32-element Sylow in the literal PSL₃(3) graph extension

The inner matrix embedding is faithful, and its two graph cosets are disjoint.
The sixteen matrices in `Coordinates.Table` are stable under inverse transpose;
combining them with the graph involution gives a closed 32-element subgroup.
The proved inner/graph normal form gives ambient order 11232, so the subgroup
has odd index 351 and is Sylow. All coordinate tests refer to the actual
subgroup of automorphisms of the projective matrix group.

Two explicit Gram matrices conjugate inverse transpose to coordinates
`(9,true)` and `(13,true)`. Their literal centralizers are the candidates for
the remaining local and actor certificates. No generation or actor-placement
claim is made by this module.

Source: Aschbacher–Smith E.1.2, E.1.5, E.1.14(7), printed pp.209–210, 214;
Asc82a Lemma 4.11. The inner matrix table is attributed in `Coordinates.Table`.
-/

public section
open Subgroup Matrix.PSL3Three Matrix.PSL3.OuterSolvable
open Matrix.PSL3.OddPrimeGraphExtension
open Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure
open Matrix.PSL3Three.GraphLocalQuotients
open Matrix.PSL3Three.GraphWitnesses.EightCentralizers.GraphModel
open Matrix.PSL3Three.GraphWitnesses.EightCentralizers
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.OuterActors
set_option maxRecDepth 10000

private theorem graphSL_inv (x : SL) :
    graphSL (ZMod 3) x⁻¹ = Matrix.SpecialLinearGroup.transpose x := by
  change (Matrix.SpecialLinearGroup.transpose x⁻¹)⁻¹ = Matrix.SpecialLinearGroup.transpose x
  apply inv_eq_of_mul_eq_one_left
  apply Subtype.ext
  change x.val.transpose * (x⁻¹).val.transpose = (1 : SL).val
  rw [← Matrix.transpose_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one]

@[expose] def graphIndex : Fin 16 → Fin 16 :=
  ![0, 7, 6, 5, 4, 3, 2, 1, 14, 13, 12, 11, 10, 9, 8, 15]

theorem twoElement_graph (i : Fin 16) :
    graphSL (ZMod 3) (twoElement i) = twoElement (graphIndex i) := by
  have hg : graphSL (ZMod 3) (twoElement i) =
      Matrix.SpecialLinearGroup.transpose ((twoElement i)⁻¹) := by
    simpa only [inv_inv] using graphSL_inv (twoElement i)⁻¹
  rw [hg, ← twoElement_inv]
  apply Subtype.ext
  revert i
  decide +kernel

@[expose] def inner : SL →* G where
  toFun x := ⟨MulAut.conj (project x), mem_sup_left ⟨project x, rfl⟩⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)

theorem inner_injective : Function.Injective inner := by
  intro x y h
  apply project_injective
  exact MulAut.conj_injective_of_center_eq_bot psl_center_eq_bot (congrArg Subtype.val h)

theorem graphElement_mul_inner (x : SL) :
    graphElement * inner x = inner (graphSL (ZMod 3) x) * graphElement := by
  apply Subtype.ext
  ext y
  change graph (ZMod 3) (project x * y * (project x)⁻¹) =
    project (graphSL (ZMod 3) x) * graph (ZMod 3) y * (project (graphSL (ZMod 3) x))⁻¹
  simp only [map_mul, map_inv]
  rfl

theorem graphElement_sq : graphElement * graphElement = 1 := by
  apply Subtype.ext
  exact (pow_two (graph (ZMod 3))).symm.trans (graph_sq (ZMod 3))

@[expose] def pair (x : SL) (b : Bool) : G :=
  inner x * if b then graphElement else 1

theorem pair_inner_iff (x : SL) (b : Bool) :
    pair x b ∈ innerPart (ZMod 3) ↔ b = false := by
  cases b with
  | false => simp only [pair, Bool.false_eq_true, ↓reduceIte, mul_one]
             exact iff_of_true ⟨project x, rfl⟩ trivial
  | true =>
    simp only [Bool.true_eq_false, iff_false]
    intro h
    apply graph_not_inner
    change (inner x).val * graph (ZMod 3) ∈ MulAut.innerSubgroup PSL at h
    have hi : (inner x).val ∈ MulAut.innerSubgroup PSL := ⟨project x, rfl⟩
    have hh := (MulAut.innerSubgroup PSL).mul_mem
      ((MulAut.innerSubgroup PSL).inv_mem hi) h
    simpa only [inv_mul_cancel_left] using hh

theorem pair_injective : Function.Injective (fun p : SL × Bool => pair p.1 p.2) := by
  rintro ⟨x,b⟩ ⟨y,d⟩ h
  change pair x b = pair y d at h
  have hb : b = d := by
    have hh : b = false ↔ d = false := by
      rw [← pair_inner_iff x b, ← pair_inner_iff y d, h]
    cases b <;> cases d <;> simp_all
  subst d
  have hx : x = y := inner_injective (mul_right_cancel h)
  exact Prod.ext hx rfl

theorem pair_surjective : Function.Surjective (fun p : SL × Bool => pair p.1 p.2) := by
  intro a
  obtain ⟨x, hx | hx⟩ := automorphism_inner_or_inner_graph a.val
  · obtain ⟨s, rfl⟩ := project_surjective x
    exact ⟨(s,false), Subtype.ext (by simpa [pair, inner] using hx.symm)⟩
  · obtain ⟨s, rfl⟩ := project_surjective x
    exact ⟨(s,true), Subtype.ext (by simpa [pair, inner, graphElement] using hx.symm)⟩

theorem card_graphExtension : Nat.card G = 11232 := by
  rw [← Nat.card_congr (Equiv.ofBijective _ ⟨pair_injective, pair_surjective⟩),
    Nat.card_prod, card_SL]
  norm_num [Nat.card_eq_fintype_card]

theorem pair_mul (x y : SL) (b d : Bool) :
    pair x b * pair y d = pair (x * if b then graphSL (ZMod 3) y else y) (b.xor d) := by
  cases b <;> cases d <;>
    simp [pair, map_mul]
  · rw [mul_assoc]
  · rw [mul_assoc, graphElement_mul_inner, ← mul_assoc]
  · rw [mul_assoc, ← mul_assoc graphElement, graphElement_mul_inner,
      mul_assoc (inner (graphSL (ZMod 3) y)), graphElement_sq, mul_one]

abbrev Index := Fin 16 × Bool

@[expose] def element (i : Index) : G := pair (twoElement i.1) i.2

@[expose] def multiply (i j : Index) : Index :=
  (productIndex i.1 (if i.2 then graphIndex j.1 else j.1), i.2.xor j.2)

@[expose] def inverse (i : Index) : Index :=
  (if i.2 then graphIndex (inverseIndex i.1) else inverseIndex i.1, i.2)

theorem element_mul (i j : Index) : element (multiply i j) = element i * element j := by
  rw [element, element, element, pair_mul]
  unfold multiply
  dsimp only
  rw [twoElement_mul]
  cases i.2 <;> simp only [Bool.false_eq_true, ↓reduceIte, twoElement_graph]

theorem element_one : element (0,false) = 1 := by
  change inner (twoElement 0) * 1 = 1
  have h : twoElement 0 = 1 := Subtype.ext (by decide +kernel)
  rw [h, map_one, mul_one]

theorem element_inv (i : Index) : element (inverse i) = (element i)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← element_mul]
  have hi : multiply (inverse i) i = (0,false) := by
    revert i
    decide +kernel
  rw [hi, element_one]

@[expose] def standardSubgroup : Subgroup G where
  carrier := Set.range element
  one_mem' := ⟨(0,false), element_one⟩
  mul_mem' := by
    rintro _ _ ⟨i,rfl⟩ ⟨j,rfl⟩
    exact ⟨multiply i j, element_mul i j⟩
  inv_mem' := by
    rintro _ ⟨i,rfl⟩
    exact ⟨inverse i, element_inv i⟩

theorem element_injective : Function.Injective element := by
  intro i j h
  have he := @pair_injective (twoElement i.1, i.2) (twoElement j.1, j.2) h
  apply Prod.ext
  · have hm := congrArg Prod.fst he
    have hi : ∀ i j : Fin 16, (twoElement i).val = (twoElement j).val → i = j := by decide +kernel
    exact hi _ _ (congrArg Subtype.val hm)
  · exact congrArg (fun p : SL × Bool => p.2) he

/-- Commutation in the actual extension reduces to equality of 32-element coordinates. -/
theorem element_commute_iff (i j : Index) :
    Commute (element i) (element j) ↔ multiply i j = multiply j i := by
  change element i * element j = element j * element i ↔ _
  rw [← element_mul, ← element_mul]
  exact element_injective.eq_iff

theorem element_sq_eq_one_iff (i : Index) :
    element i ^ 2 = 1 ↔ multiply i i = (0,false) := by
  rw [pow_two, ← element_mul, ← element_one]
  exact element_injective.eq_iff

theorem element_mem_inner_iff (i : Index) :
    element i ∈ innerPart (ZMod 3) ↔ i.2 = false := pair_inner_iff _ _

theorem element_mem_standardSubgroup (i : Index) : element i ∈ standardSubgroup := ⟨i,rfl⟩

/-- The concrete coordinate table identifies all 32 elements of the subgroup. -/
@[expose] noncomputable def standardEquiv : Index ≃ standardSubgroup := Equiv.ofBijective
    (fun i => ⟨element i, ⟨i,rfl⟩⟩)
    ⟨fun _ _ h => element_injective (congrArg Subtype.val h), by
      rintro ⟨_,i,rfl⟩
      exact ⟨i,rfl⟩⟩

@[simp] theorem standardEquiv_apply (i : Index) : (standardEquiv i).val = element i := rfl

theorem standardSubgroup_card : Nat.card standardSubgroup = 32 := by
  rw [← Nat.card_congr standardEquiv]
  norm_num [Nat.card_eq_fintype_card]

/-- A Sylow subgroup of the literal graph extension, with explicit coordinates. -/
@[expose] def standardSylow : Sylow 2 G :=
  (IsPGroup.of_card (p := 2) (n := 5) standardSubgroup_card).toSylow (by
    have hc := standardSubgroup.card_mul_index
    rw [standardSubgroup_card, card_graphExtension] at hc
    have hi : standardSubgroup.index = 351 := by omega
    rw [hi]
    decide)

theorem standardSylow_coe : (standardSylow : Subgroup G) = standardSubgroup := rfl

/-- The two graph-involution centralizers used by the finite placement calculation. -/
@[expose] def localMatrix (j : Bool) : SL := if j then
  ⟨!![0,0,1; 1,1,0; 0,1,0], by decide⟩ else
  ⟨!![0,0,1; 0,1,0; 2,2,0], by decide⟩

@[expose] def localConjugator (j : Bool) : G := inner (localMatrix j)

@[expose] def localIndex (j : Bool) : Index := (if j then 13 else 9, true)

/-- The local markers are actual conjugates of inverse transpose. -/
theorem localConjugator_graph (j : Bool) :
    (MulAut.conj (localConjugator j)) graphElement = element (localIndex j) := by
  change inner (localMatrix j) * graphElement * (inner (localMatrix j))⁻¹ = _
  rw [← map_inv, mul_assoc, graphElement_mul_inner, ← mul_assoc, ← map_mul]
  have hm : localMatrix j * graphSL (ZMod 3) (localMatrix j)⁻¹ =
      twoElement (localIndex j).1 := by
    rw [graphSL_inv]
    apply Subtype.ext
    revert j
    decide +kernel
  rw [hm]
  rfl

theorem localSubgroup_marker (j : Bool) :
    localSubgroup (localConjugator j) = centralizer {element (localIndex j)} := by
  rw [localSubgroup_eq_centralizer, localConjugator_graph]

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.OuterActors
