module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.NonbinaryRecognition.TensorModels
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.Actions
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.Coordinates
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.FullGroup

/-!
# Marked symplectic matrix actions

The actual derived/full equivalence lifts the standard unipotent group,
simple coroots and negative simple roots. Graph stability and the explicit
Sylow coordinates give the highest column and lowest row. The graph-square
identity gives every Frobenius twist of the coroot and negative-root columns.
No involutivity of the exceptional graph automorphism is assumed.

Sources: GLS3, 2.8.4 and 2.8.10(d), `refs/KGroup/GLS3/chapter2.tex`;
Aschbacher--Smith, G.9.3, printed pp.356--357 of `refs/quasithin.pdf`.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.Nonbinary.MarkedWeights
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
open Representation.OneCohomology.SymplecticFour
open Matrix

variable {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
local instance : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2

/-- The literal inclusion inverse supplied by perfectness for q > 2. -/
noncomputable def lift (hq : 2 < Nat.card F) : Sp F ≃* Derived F :=
  (derivedEquivFull_of_card_gt_two hq).symm

@[simp] theorem lift_val (hq : 2 < Nat.card F) (g : Sp F) : (lift hq g).val = g := by
  simpa only [lift, derivedEquivFull_of_card_gt_two_apply] using
    (derivedEquivFull_of_card_gt_two hq).apply_symm_apply g

/-- The marked standard upper unipotent subgroup in the derived carrier. -/
def U : Subgroup (Derived F) := unipotent.comap (commutator (Sp F)).subtype

/-- Inclusion of the actual standard unipotent subgroup. -/
noncomputable def unipotentLift (hq : 2 < Nat.card F) : unipotent (F := F) →* Derived F :=
  (lift hq).toMonoidHom.comp unipotent.subtype

@[simp] theorem unipotentLift_val (hq : 2 < Nat.card F) (u : unipotent (F := F)) :
    (unipotentLift hq u).val = u.val := lift_val hq u.val

/-- The pullback marking is exactly the image of the actual unipotent inclusion. -/
theorem unipotentLift_range (hq : 2 < Nat.card F) :
    (unipotentLift hq).range = U (F := F) := by
  ext g
  constructor
  · rintro ⟨u, rfl⟩
    change (unipotentLift hq u).val ∈ unipotent
    rw [unipotentLift_val]
    exact u.property
  · intro hg
    refine ⟨⟨g.val, hg⟩, ?_⟩
    apply Subtype.ext
    exact unipotentLift_val hq ⟨g.val, hg⟩

theorem graphDerived_val (g : Derived F) : (graphDerived F g).val = graphAut g.val := rfl

theorem graphDerived_pow_mem_unipotent (g : Derived F) (hg : g ∈ U) (j : ℕ) :
    ((graphDerived F ^ j) g).val ∈ unipotent := by
  induction j with
  | zero => exact hg
  | succ j ih =>
    rw [pow_succ', MulAut.mul_apply, graphDerived_val]
    exact EvenBorelTorus.graph_mem_unipotent _ ih

private theorem unipotent_column (g : Sp F) (hg : g ∈ unipotent) (i : Coordinate) :
    g.val i (.inl 0) = if i = .inl 0 then 1 else 0 := by
  obtain ⟨⟨b,u,w,v⟩, he⟩ := CentralRootGeometry.element_surjective ⟨g,hg⟩
  have hm := congrArg (fun x : unipotent (F := F) => x.val.val) he
  rw [CentralRootGeometry.element_matrix] at hm
  rw [← hm]
  rcases i with i | i <;> fin_cases i <;> rfl

private theorem unipotent_row (g : Sp F) (hg : g ∈ unipotent) (i : Coordinate) :
    g.val (.inr 0) i = if i = .inr 0 then 1 else 0 := by
  obtain ⟨⟨b,u,w,v⟩, he⟩ := CentralRootGeometry.element_surjective ⟨g,hg⟩
  have hm := congrArg (fun x : unipotent (F := F) => x.val.val) he
  rw [CentralRootGeometry.element_matrix] at hm
  rw [← hm]
  rcases i with i | i <;> fin_cases i <;> rfl

/-- Every graph power fixes the marked highest coordinate column. -/
theorem graph_unipotent_column (g : Derived F) (hg : g ∈ U) (j : ℕ) (i : Coordinate) :
    ((graphDerived F ^ j) g).val.val i (.inl 0) = if i = .inl 0 then 1 else 0 :=
  unipotent_column _ (graphDerived_pow_mem_unipotent g hg j) i

/-- Every graph power fixes the marked lowest coordinate row. -/
theorem graph_unipotent_row (g : Derived F) (hg : g ∈ U) (j : ℕ) (i : Coordinate) :
    ((graphDerived F ^ j) g).val.val (.inr 0) i = if i = .inr 0 then 1 else 0 :=
  unipotent_row _ (graphDerived_pow_mem_unipotent g hg j) i

/-- The even graph powers are entrywise Frobenius powers. -/
theorem graph_even_entry (g : Derived F) (k : ℕ) (i j : Coordinate) :
    ((graphDerived F ^ (2*k)) g).val.val i j = (g.val.val i j) ^ (2^k) := by
  induction k generalizing g with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, pow_add, MulAut.mul_apply]
    rw [ih, graphDerived_square_apply, ← pow_mul]
    congr 1
    simp [pow_succ, Nat.mul_comm]

/-- The odd graph powers are Frobenius powers of the genuine exceptional image. -/
theorem graph_odd_entry (g : Derived F) (k : ℕ) (i j : Coordinate) :
    ((graphDerived F ^ (2*k+1)) g).val.val i j =
      (graphMatrix g.val.val i j) ^ (2^k) := by
  rw [pow_add, MulAut.mul_apply, pow_one, graph_even_entry]
  rfl

omit [Finite F] [Algebra (ZMod 2) F] in
/-- The diagonal graph formula, with the original symplectic coordinates. -/
theorem graph_diagonal (s t : Fˣ) :
    graphMatrix (diagonalTorus s t).val = (diagonalTorus (s*t) (s/t)).val := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [graphMatrix, minor, first, second, diagonalTorus, Matrix.diagonal,
      div_eq_mul_inv, mul_comm]

/-- The simple coroot for root 6. -/
noncomputable def corootA (hq : 2 < Nat.card F) (s : Fˣ) : Derived F :=
  lift hq (diagonalTorus s s⁻¹)
/-- The simple coroot for root 2. -/
noncomputable def corootB (hq : 2 < Nat.card F) (s : Fˣ) : Derived F :=
  lift hq (diagonalTorus 1 s)

omit [Finite F] [Algebra (ZMod 2) F] in
private theorem diagonal_column (s t : Fˣ) (i : Coordinate) :
    (diagonalTorus s t).val i (.inl 0) = if i = .inl 0 then (s:F) else 0 := by
  rcases i with i | i <;> fin_cases i <;> rfl

theorem corootA_column (hq : 2 < Nat.card F) (s : Fˣ) (j : ℕ) (i : Coordinate) :
    ((graphDerived F ^ j) (corootA hq s)).val.val i (.inl 0) =
      if i = .inl 0 then (s:F) ^ (if j%2=0 then 2^(j/2) else 0) else 0 := by
  have hj : j = 2*(j/2) + j%2 := by omega
  by_cases hp : j%2=0
  · have hj' : j = 2*(j/2) := by omega
    conv_lhs => rw [hj']
    rw [graph_even_entry]
    simp only [corootA, lift_val, diagonal_column, hp, ite_true]
    split_ifs <;> simp
  · have hj' : j = 2*(j/2)+1 := by omega
    conv_lhs => rw [hj']
    rw [graph_odd_entry]
    simp only [corootA, lift_val, graph_diagonal, diagonal_column, hp, ite_false]
    simp

theorem corootB_column (hq : 2 < Nat.card F) (s : Fˣ) (j : ℕ) (i : Coordinate) :
    ((graphDerived F ^ j) (corootB hq s)).val.val i (.inl 0) =
      if i = .inl 0 then (s:F) ^ (if j%2=1 then 2^(j/2) else 0) else 0 := by
  by_cases hp : j%2=1
  · have hj' : j = 2*(j/2)+1 := by omega
    conv_lhs => rw [hj']
    rw [graph_odd_entry]
    simp only [corootB, lift_val, graph_diagonal, diagonal_column, hp, ite_true, one_mul]
    split_ifs <;> simp
  · have hj' : j = 2*(j/2) := by omega
    conv_lhs => rw [hj']
    rw [graph_even_entry]
    simp only [corootB, lift_val, diagonal_column, hp, ite_false]
    split_ifs <;> simp

/-- The negative root opposite the simple root of the indicated parity. -/
noncomputable def negativeRoot (hq : 2 < Nat.card F) (p : Fin 2) : Derived F :=
  lift hq (rootElement (if p = 0 then 7 else 3) 1)

/-- The negative simple root adds the second coordinate exactly in its own parity. -/
theorem negativeRoot_column (hq : 2 < Nat.card F) (p : Fin 2) (j : ℕ) (i : Coordinate) :
    ((graphDerived F ^ j) (negativeRoot hq p)).val.val i (.inl 0) =
      if i = .inl 0 ∨ (j%2 = p.val ∧ i = .inl 1) then 1 else 0 := by
  by_cases hp : j%2=0
  · have hj : j = 2*(j/2) := by omega
    conv_lhs => rw [hj]
    rw [graph_even_entry]
    simp only [negativeRoot, lift_val]
    fin_cases p <;> rcases i with i | i <;> fin_cases i <;>
      simp [rootElement, rootMatrix, Matrix.fromBlocks, Matrix.single, hp]
  · have hj : j = 2*(j/2)+1 := by omega
    have hp' : j%2=1 := by omega
    conv_lhs => rw [hj]
    rw [graph_odd_entry]
    simp only [negativeRoot, lift_val]
    fin_cases p <;> rcases i with i | i <;> fin_cases i <;>
      simp [rootElement, rootMatrix, graphMatrix, minor, first, second,
        Matrix.fromBlocks, Matrix.single, hp']

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.Nonbinary.MarkedWeights
