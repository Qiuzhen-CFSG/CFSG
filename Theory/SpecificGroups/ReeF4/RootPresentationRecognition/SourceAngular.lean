module
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.AngularPresentation
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.SourcePositive

/-!
# Faithful angular positive presentation on the same marked source quotient

The original field charts and pair equations first prove homomorphisms from
each native whole root group to its marked source root. The additional angular
conjugation equations then construct evaluation of the proved finite positive
presentation. Its range is exactly the same source U by Carter's coordinates.
Those coordinates also give the same product of root orders as the native U,
so the constructed evaluation has trivial kernel. This yields an actual
source/native positive subgroup isomorphism with literal field-generator formulas.

The source owner still must construct the charts and verify the angular finite
equations. No global model map, source order, simplicity or faithfulness is an
input. This module does not prove signed global Bruhat reduction or comparison
of the full Ree group, its Borel or its parabolics.

Source: Carter 2.5.10--17; GLS3 2.4.5--6; DGS, *Groups and Graphs*, p.224.
-/

@[expose] public noncomputable section
namespace ReeF4.RootPresentationRecognition.SourceAngular
open Subgroup PositiveTables
open Theory.GroupTheory OrderedRootPresentation
open CentralCovers.TwoPrimary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits)
variable {m : ℕ} (d : SourcePositive.Charts Q split m)

private theorem source_word_single (i : PositiveTables.Root) (a : PositiveTables.Parameter m i) :
    PositivePresentation.word (fun i b => (d.chart i b : X ⧸ Q.D)) (single i a) = d.chart i a := by
  cases i with
  | inl j => fin_cases j <;> simp [PositivePresentation.word, single, List.ofFn_succ,
      d.equations.pair_zero, d.equations.quartet_zero]
  | inr j => fin_cases j <;> simp [PositivePresentation.word, single, List.ofFn_succ,
      d.equations.pair_zero, d.equations.quartet_zero]

/-- The given source field charts, reindexed by the actual native root carriers. -/
def parameterEquiv (i : PositiveTables.Root) : AngularPresentation.Parameter m i ≃ d.root i :=
  (rootChartEquiv m i).symm.trans (d.chart i)

@[simp] theorem parameterEquiv_field (i : PositiveTables.Root) (a : PositiveTables.Parameter m i) :
    parameterEquiv Q split d i (rootChartEquiv m i a) = d.chart i a := by
  simp only [parameterEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]

/-- The original pair equations already force the complete local root law. -/
theorem parameterEquiv_mul (i : PositiveTables.Root) (a b : AngularPresentation.Parameter m i) :
    parameterEquiv Q split d i (a*b) = parameterEquiv Q split d i a * parameterEquiv Q split d i b := by
  let ea := (rootChartEquiv m i).symm a
  let eb := (rootChartEquiv m i).symm b
  let ec := (rootChartEquiv m i).symm (a*b)
  have hchart (v : AngularPresentation.Parameter m i) :
      (PositiveTables.root m i ((rootChartEquiv m i).symm v) : Model m) = v := by
    rw [← rootChartEquiv_apply]
    exact congrArg Subtype.val ((rootChartEquiv m i).apply_symm_apply v)
  have ht : PositiveTables.exchange i i ea eb = single i ec := by
    apply exchange_unique
    rw [product_single]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, ea, eb, ec, hchart]
  apply Subtype.ext
  change (d.chart i ec : X ⧸ Q.D) = (d.chart i ea : X ⧸ Q.D) * d.chart i eb
  rw [d.equations.exchange, ht, source_word_single]

/-- Local homomorphisms are proved from field equations, not supplied as input. -/
def sourceRoot (i : PositiveTables.Root) : AngularPresentation.Parameter m i →* X ⧸ Q.D :=
  (d.root i).subtype.comp
    (MulEquiv.toMonoidHom
      { toEquiv := parameterEquiv Q split d i
        map_mul' := parameterEquiv_mul Q split d i })

@[simp] theorem sourceRoot_field (i : PositiveTables.Root) (a : PositiveTables.Parameter m i) :
    sourceRoot Q split d i (rootChartEquiv m i a) = d.chart i a :=
  congrArg Subtype.val (parameterEquiv_field Q split d i a)

theorem sourceRoot_range (i : PositiveTables.Root) : (sourceRoot Q split d i).range = d.root i := by
  apply le_antisymm
  · rintro x ⟨a,rfl⟩; exact (parameterEquiv Q split d i a).property
  · intro x hx
    obtain ⟨a,ha⟩ := (parameterEquiv Q split d i).surjective ⟨x,hx⟩
    exact ⟨a,congrArg Subtype.val ha⟩

/-- Extra finite equations for the angular table. Their variables range over
two individual roots; no global map, kernel or uniqueness is a premise. -/
def Equations : Prop := OrderedRootPresentation.Equations (AngularPresentation.table m)
  (sourceRoot Q split d)

variable (E : Equations Q split d)

def eval : AngularPresentation.Presentation m →* X ⧸ Q.D :=
  OrderedRootPresentation.eval (AngularPresentation.table m) E

@[simp] theorem eval_root (i : PositiveTables.Root) (a : AngularPresentation.Parameter m i) :
    eval Q split d E (OrderedRootPresentation.root (AngularPresentation.table m) i a) =
      sourceRoot Q split d i a := OrderedRootPresentation.eval_root _ _ i a

theorem eval_range : (eval Q split d E).range = split.U := by
  have he : (eval Q split d E).range =
      join (AngularPresentation.Parameter m) (sourceRoot Q split d) sourceOrder :=
    OrderedRootPresentation.eval_range _ _ AngularPresentation.order_nodup mem_sourceOrder
  apply le_antisymm
  · rw [he]
    apply join_le
    intro i _
    rw [sourceRoot_range]
    exact SourcePositive.root_le_unipotent Q split d i
  · rw [← SourcePositive.eval_range Q split d]
    rintro y ⟨g,rfl⟩
    apply PresentedGroup.generated_by _
      ((eval Q split d E).range.comap (SourcePositive.eval Q split d)) _ g
    rintro ⟨i,a⟩
    change SourcePositive.eval Q split d (PositivePresentation.generator m i a) ∈
      (eval Q split d E).range
    rw [SourcePositive.eval_generator, he]
    apply range_le_join (AngularPresentation.Parameter m) (sourceRoot Q split d) sourceOrder
      (mem_sourceOrder i)
    exact ⟨rootChartEquiv m i a, sourceRoot_field Q split d i a⟩

include d in
/-- Carter's source coordinates have exactly the native coordinate count.
Neither the order of the source U nor a presentation kernel is assumed. -/
theorem source_card : Nat.card split.U = Nat.card (Parabolics.unipotent m) := by
  rw [unipotent_card_ordered Q split d.orientation, d.rotation_eight, d.order_eq]
  simp only [List.map_ofFn, List.prod_ofFn]
  calc
    _ = ∏ j : Fin 8, Nat.card (AngularPresentation.Parameter m (d.index j)) := by
      apply Finset.prod_congr rfl
      intro j _
      exact (Nat.card_congr (parameterEquiv Q split d (d.index j))).symm
    _ = ∏ i : PositiveTables.Root, Nat.card (AngularPresentation.Parameter m i) :=
      d.index.prod_comp (fun i : PositiveTables.Root => Nat.card (AngularPresentation.Parameter m i))
    _ = Nat.card (Blocks m) := by rw [Nat.card_pi]
    _ = _ := Nat.card_congr (positiveEquiv m)

def evalU : AngularPresentation.Presentation m →* split.U :=
  (eval Q split d E).codRestrict _ (fun g => by
    rw [← eval_range Q split d E]
    exact ⟨g,rfl⟩)

theorem evalU_surjective : Function.Surjective (evalU Q split d E) := by
  intro u
  have hu : (u : X ⧸ Q.D) ∈ (eval Q split d E).range := by
    rw [eval_range]; exact u.property
  obtain ⟨g,hg⟩ := hu
  exact ⟨g,Subtype.ext hg⟩

/-- The source kernel is trivial by proved collection and the same Carter
coordinates. There is no source simplicity or faithfulness assumption. -/
theorem evalU_bijective : Function.Bijective (evalU Q split d E) := by
  apply (evalU_surjective Q split d E).bijective_of_nat_card_le
  rw [source_card Q split d]
  exact le_of_eq (Nat.card_congr (AngularPresentation.nativeEquiv m).toEquiv)

def sourceEquiv : AngularPresentation.Presentation m ≃* split.U :=
  MulEquiv.ofBijective (evalU Q split d E) (evalU_bijective Q split d E)

/-- Actual positive subgroup comparison, retaining the same source quotient. -/
def comparison : split.U ≃* Parabolics.unipotent m :=
  (sourceEquiv Q split d E).symm.trans (AngularPresentation.nativeEquiv m)

theorem comparison_field (i : PositiveTables.Root) (a : PositiveTables.Parameter m i) :
    (comparison Q split d E ⟨d.chart i a, SourcePositive.root_le_unipotent Q split d i
      (d.chart i a).property⟩ : Model m) = PositiveTables.root m i a := by
  let g := OrderedRootPresentation.root (AngularPresentation.table m) i (rootChartEquiv m i a)
  have he : sourceEquiv Q split d E g =
      ⟨d.chart i a, SourcePositive.root_le_unipotent Q split d i (d.chart i a).property⟩ := by
    apply Subtype.ext
    exact (eval_root Q split d E i _).trans (sourceRoot_field Q split d i a)
  rw [← he]
  change (AngularPresentation.nativeEquiv m
    ((sourceEquiv Q split d E).symm (sourceEquiv Q split d E g)) : Model m) = _
  rw [MulEquiv.symm_apply_apply]
  exact AngularPresentation.nativeEquiv_root m i (rootChartEquiv m i a)

end ReeF4.RootPresentationRecognition.SourceAngular
