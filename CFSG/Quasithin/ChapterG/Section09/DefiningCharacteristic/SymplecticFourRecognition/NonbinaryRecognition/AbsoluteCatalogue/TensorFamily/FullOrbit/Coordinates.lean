module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.NonbinaryRecognition.TensorModels
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.Coordinates
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.FullGroup
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.Actions
/-!
# Marked vectors and matrices for the full symplectic tensor

The standard unipotent subgroup acts through the inverse of the actual
inclusion isomorphism from the derived symplectic group. The exceptional
square formula evaluates the full tensor's highest-to-lowest coefficient.
The same marked Sylow fixes the highest vector, and the graph-fixed block
exchange carries it to the lowest vector.

Source: the concrete basic modules of GLS3, 2.8.6(a), 2.8.10(d),
`refs/KGroup/GLS3/chapter2.tex`; the natural branch on printed pp.356–357
of `refs/quasithin.pdf`.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
open Matrix
set_option linter.unusedSimpArgs false
namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.Nonbinary.FullOrbit
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
variable {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
local instance : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
local notation "a" => (Sum.inl (0 : Fin 2) : Coordinate)
local notation "c" => (Sum.inr (0 : Fin 2) : Coordinate)

noncomputable def sylowMap (hq : 2 < Nat.card F) : unipotent (F := F) →* Derived F :=
  (derivedEquivFull_of_card_gt_two hq).symm.toMonoidHom.comp unipotent.subtype

@[simp] lemma sylowMap_val (hq : 2 < Nat.card F) (u : unipotent (F := F)) :
    (sylowMap hq u).val = u.val :=
  by
    change ((derivedEquivFull_of_card_gt_two hq).symm u.val).val = u.val
    rw [← derivedEquivFull_of_card_gt_two_apply hq]
    exact (derivedEquivFull_of_card_gt_two hq).apply_symm_apply u.val

lemma graphDerived_val (g : Derived F) :
    (graphDerived F g).val = ExceptionalGraph.graphAut g.val := rfl

lemma graph_even (g : Derived F) (k : ℕ) (i j : Coordinate) :
    ((graphDerived F ^ (2*k)) g).val.val i j = (g.val.val i j) ^ (2^k) := by
  induction k generalizing g with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, pow_add, MulAut.mul_apply, ih, graphDerived_square_apply, ← pow_mul, pow_succ']

lemma graph_odd (g : Derived F) (k : ℕ) (i j : Coordinate) :
    ((graphDerived F ^ (2*k+1)) g).val.val i j =
      ((graphDerived F g).val.val i j) ^ (2^k) := by
  rw [pow_add, MulAut.mul_apply, pow_one, graph_even]

lemma full_product (g : Derived F) (n : ℕ) :
    (∏ j ∈ Finset.range (2*n), ((graphDerived F ^ j) g).val.val a c) =
      (g.val.val a c)^(2^n-1) * ((graphDerived F g).val.val a c)^(2^n-1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, show 2*n+2 = (2*n+1)+1 by omega,
      Finset.prod_range_succ, Finset.prod_range_succ, ih, graph_even, graph_odd]
    have he : 2^(n+1)-1 = (2^n-1)+2^n := by have := Nat.two_pow_pos n; omega
    rw [he, pow_add, pow_add]
    ring

lemma graph_element_entry (hq : 2 < Nat.card F) (b x y z : F) :
    ((graphDerived F (sylowMap hq (CentralRootGeometry.element b x y z))).val.val a c) =
      x*z+y^2+b*y*z := by
  rw [graphDerived_val, sylowMap_val]
  change ExceptionalGraph.graphMatrix _ a c = _
  rw [CentralRootGeometry.element_matrix]
  simp [ExceptionalGraph.graphMatrix, ExceptionalGraph.minor, ExceptionalGraph.first,
    ExceptionalGraph.second, Matrix.fromBlocks]
  ring

variable {E : Type*} [Field E]
abbrev FullIndex (n : ℕ) := (Finset.univ : Finset (Fin (2*n)))
def highest (n : ℕ) : ((FullIndex n → Coordinate) → E) := Pi.single (fun _ => a) 1
def lowest (n : ℕ) : ((FullIndex n → Coordinate) → E) := Pi.single (fun _ => c) 1

set_option backward.isDefEq.respectTransparency false in
lemma highest_coefficient (e : F →+* E) {n : ℕ} (hq : 2 < Nat.card F)
    (hF : Nat.card F = 2^n) (b x y z : F) :
    (tensorModel e (FullIndex n) (sylowMap hq (CentralRootGeometry.element b x y z))
      (lowest n)) (fun _ => a) =
      e (x^(Nat.card F-1) * (x*z+y^2+b*y*z)^(Nat.card F-1)) := by
  classical
  change (tensorMatrix e (FullIndex n) _).mulVec (Pi.single (fun _ => c) 1) _ = _
  simp only [Matrix.mulVec_single, MulOpposite.op_one, one_smul]
  change tensorMatrix e (FullIndex n) _ (fun _ => a) (fun _ => c) = _
  unfold tensorMatrix
  rw [← map_prod]
  congr 1
  change (∏ j : (Finset.univ : Finset (Fin (2*n))),
    ((graphDerived F ^ (j.val : ℕ)) (sylowMap hq (CentralRootGeometry.element b x y z))).val.val a c) = _
  rw [Finset.prod_coe_sort (Finset.univ : Finset (Fin (2*n)))
    (fun j : Fin (2*n) => ((graphDerived F ^ (j : ℕ))
      (sylowMap hq (CentralRootGeometry.element b x y z))).val.val a c)]
  change (∏ j : Fin (2*n), _) = _
  rw [Fin.prod_univ_eq_prod_range (fun j : ℕ => ((graphDerived F ^ j)
    (sylowMap hq (CentralRootGeometry.element b x y z))).val.val a c) (2*n)]
  rw [full_product, graph_element_entry, sylowMap_val, CentralRootGeometry.element_matrix, hF]
  rfl

lemma tensor_single (e : F →+* E) {n : ℕ} (S : Finset (Fin (2*n)))
    (g : Derived F) (x y : S → Coordinate) :
    tensorModel e S g (Pi.single y 1) x =
      ∏ j : S, e (((graphDerived F ^ (j.val : ℕ)) g).val.val (x j) (y j)) := by
  classical
  change (tensorMatrix e S g).mulVec (Pi.single y 1) x = _
  simp only [Matrix.mulVec_single, MulOpposite.op_one, one_smul]
  rfl

lemma graph_power_mem_unipotent (hq : 2 < Nat.card F) (u : unipotent (F := F)) (k : ℕ) :
    ((graphDerived F ^ k) (sylowMap hq u)).val ∈ unipotent := by
  induction k with
  | zero => simp [u.property]
  | succ k ih =>
    rw [pow_succ', MulAut.mul_apply, graphDerived_val]
    exact EvenBorelTorus.graph_mem_unipotent _ ih

lemma unipotent_column (u : unipotent (F := F)) (i : Coordinate) :
    u.val.val i a = if i = a then 1 else 0 := by
  obtain ⟨⟨b,x,y,z⟩, rfl⟩ := CentralRootGeometry.element_surjective u
  rw [CentralRootGeometry.element_matrix]
  rcases i with i | i <;> fin_cases i <;> rfl

lemma highest_fixed (e : F →+* E) (n : ℕ) (hq : 2 < Nat.card F)
    (u : unipotent (F := F)) :
    tensorModel e (FullIndex n) (sylowMap hq u) (highest n) = highest n := by
  classical
  ext x
  rw [highest, tensor_single]
  have hh (j : FullIndex n) :
      ((graphDerived F ^ (j.val : ℕ)) (sylowMap hq u)).val.val (x j) a =
        if x j = a then 1 else 0 :=
    unipotent_column ⟨_, graph_power_mem_unipotent hq u _⟩ (x j)
  simp_rw [hh]
  simp only [apply_ite e, map_one, map_zero]
  rw [Fintype.prod_ite_zero]
  simp [highest, Pi.single_apply, funext_iff, eq_comm]

/-- Exchange the two marked hyperbolic blocks in the actual matrix carrier. -/
def blockExchange : Sp F := ⟨Matrix.fromBlocks 0 1 1 0, by
  rw [SymplecticGroup.mem_iff]
  simp [Matrix.J, Matrix.fromBlocks_multiply, Matrix.fromBlocks_transpose, CharTwo.neg_eq]
  constructor <;> ext i j <;> simp [CharTwo.neg_eq]⟩

lemma graph_blockExchange : ExceptionalGraph.graphAut (blockExchange (F := F)) = blockExchange := by
  apply Subtype.ext
  change ExceptionalGraph.graphMatrix _ = _
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [blockExchange, ExceptionalGraph.graphMatrix, ExceptionalGraph.minor,
      ExceptionalGraph.first, ExceptionalGraph.second, Matrix.fromBlocks, Matrix.one_apply]

noncomputable def longElement (hq : 2 < Nat.card F) : Derived F :=
  (derivedEquivFull_of_card_gt_two hq).symm blockExchange

@[simp] lemma longElement_val (hq : 2 < Nat.card F) :
    (longElement hq).val = blockExchange :=
  by
    change ((derivedEquivFull_of_card_gt_two hq).symm blockExchange).val = blockExchange
    rw [← derivedEquivFull_of_card_gt_two_apply hq]
    exact (derivedEquivFull_of_card_gt_two hq).apply_symm_apply blockExchange

lemma graph_longElement (hq : 2 < Nat.card F) :
    graphDerived F (longElement hq) = longElement hq := by
  apply Subtype.ext
  rw [graphDerived_val, longElement_val, graph_blockExchange]

lemma graph_power_longElement (hq : 2 < Nat.card F) (k : ℕ) :
    (graphDerived F ^ k) (longElement hq) = longElement hq := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', MulAut.mul_apply, ih, graph_longElement]

lemma longElement_highest (e : F →+* E) (n : ℕ) (hq : 2 < Nat.card F) :
    tensorModel e (FullIndex n) (longElement hq) (highest n) = lowest n := by
  classical
  ext x
  rw [highest, tensor_single]
  simp_rw [graph_power_longElement, longElement_val]
  have hh (i : Coordinate) : (blockExchange (F := F)).val i a =
      if i = c then 1 else 0 := by
    rcases i with i | i <;> fin_cases i <;> rfl
  simp_rw [hh]
  simp only [apply_ite e, map_one, map_zero]
  rw [Fintype.prod_ite_zero]
  simp [lowest, Pi.single_apply, funext_iff, eq_comm]

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.Nonbinary.FullOrbit
