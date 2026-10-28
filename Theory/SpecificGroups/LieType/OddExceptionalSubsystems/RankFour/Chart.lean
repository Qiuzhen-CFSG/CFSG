module
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.RankFour.Coroots
public import Mathlib.GroupTheory.NoncommPiCoprod
public import Theory.GroupTheory.CoordinateInversionFaithfulness

/-!
# Four commuting signed roots in a literal E6 Cartan subdiagram

The roots at 0,5,2 with positive sign and at 3 with negative sign commute.
Their product defines a four-coordinate additive chart in the native root
group. The coroot products h1h3,h4h3,h3,h2 invert precisely one coordinate.
Faithful single-root parameters and these coordinate detectors prove that
no nonidentity chart element lies in the actual center. The homomorphism
therefore remains injective after the defining central quotient.

Sources: GLS3 §§1.12, 2.4 and 2.6; Aschbacher–Smith A.2.17, printed p.39.
-/

@[expose] public noncomputable section
namespace ExceptionalSplit.OddRankFour
open Theory.AlgebraicGroup.StandardRootSystem
open TwistedE6.FoldedSubsystem.HigherRealizations
attribute [local instance] Classical.decEq
variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι]

/-- Six literal simple roots with the numbered E6 Cartan matrix. -/
structure SixNodes (b : P.Base) where
  node : Fin 6 → b.support
  injective : Function.Injective node
  cartan : ∀ i j, b.cartanMatrix (node i) (node j) = typeE6CartanMatrix i j

namespace SixNodes
variable (c : SixNodes b) (F : Type*) [Field F]

def rootIndex : Fin 4 → Fin 6 := ![0,5,2,3]
def rootSign : Fin 4 → Bool := ![true,true,true,false]

def root (i : Fin 4) (t : F) : rootGenerated P b F :=
  signedSimple F (rootSign i) (c.node (rootIndex i)) t

def rootHom (i : Fin 4) : Multiplicative F →* rootGenerated P b F where
  toFun t := c.root F i t.toAdd
  map_one' := signedSimple_zero _ _ _
  map_mul' t u := signedSimple_add _ _ _ t.toAdd u.toAdd

theorem rootHom_injective (i : Fin 4) : Function.Injective (c.rootHom F i) := by
  intro t u h
  exact Multiplicative.toAdd.injective (signedSimple_injective _ _ h)

variable [P.IsIrreducible]

theorem rootHom_commute {i j : Fin 4} (hij : i ≠ j) (t u : Multiplicative F) :
    Commute (c.rootHom F i t) (c.rootHom F j u) := by
  have hn : c.node (rootIndex i) ≠ c.node (rootIndex j) := by
    intro h
    have h := c.injective h
    fin_cases i <;> fin_cases j <;> simp_all [rootIndex]
  change Commute (signedSimple F (rootSign i) (c.node (rootIndex i)) t.toAdd)
    (signedSimple F (rootSign j) (c.node (rootIndex j)) u.toAdd)
  by_cases hs : rootSign i = rootSign j
  · rw [← hs]
    apply signedSimple_commute _ _ _ _ hn
    rw [c.cartan]
    fin_cases i <;> fin_cases j <;> simp_all [rootSign,rootIndex,typeE6CartanMatrix]
  · cases hi : rootSign i <;> cases hj : rootSign j
    · exact (hs (hi.trans hj.symm)).elim
    · exact (signedSimple_opposite_commute F _ _ hn.symm _ _).symm
    · exact signedSimple_opposite_commute F _ _ hn _ _
    · exact (hs (hi.trans hj.symm)).elim

/-- The four actual commuting signed root groups, in graph-stable order. -/
def chart : (Fin 4 → Multiplicative F) →* rootGenerated P b F :=
  MonoidHom.noncommPiCoprod (c.rootHom F) (fun _ _ hij t u => c.rootHom_commute F hij t u)

@[simp] theorem chart_single (i : Fin 4) (t : Multiplicative F) :
    c.chart F (Pi.mulSingle i t) = c.root F i t.toAdd :=
  MonoidHom.noncommPiCoprod_mulSingle _ _ _

theorem chart_formula (a : Fin 4 → Multiplicative F) :
    c.chart F a = signedSimple F true (c.node 0) (a 0).toAdd *
      signedSimple F true (c.node 5) (a 1).toAdd *
      signedSimple F true (c.node 2) (a 2).toAdd *
      signedSimple F false (c.node 3) (a 3).toAdd := by
  have ha : a = Pi.mulSingle 0 (a 0) * Pi.mulSingle 1 (a 1) *
      Pi.mulSingle 2 (a 2) * Pi.mulSingle 3 (a 3) := by
    ext i
    fin_cases i <;> simp
  conv_lhs => rw [ha, map_mul, map_mul, map_mul, chart_single, chart_single, chart_single, chart_single]
  simp only [root, rootIndex, rootSign, Matrix.cons_val]

/-- The actual simple-coroot sign word at one of the six marked nodes. -/
def coroot (i : Fin 6) : rootGenerated P b F := elementaryCoroot (c.node i)

omit [P.IsIrreducible] in
theorem coroot_square (i : Fin 6) : c.coroot F i ^ 2 = 1 := elementaryCoroot_square _

omit [P.IsIrreducible] in
theorem coroot_commute (i j : Fin 6) : Commute (c.coroot F i) (c.coroot F j) :=
  elementaryCoroot_commute _ _

omit [P.IsIrreducible] in
theorem coroot_root (i : Fin 6) (s : Bool) (j : Fin 6) (t : F) :
    c.coroot F i * signedSimple F s (c.node j) t * (c.coroot F i)⁻¹ =
      signedSimple F s (c.node j) ((((-1 : Fˣ) ^ typeE6CartanMatrix j i : Fˣ) : F) * t) := by
  simpa only [coroot, c.cartan] using elementaryCoroot_conjugate_signed (c.node i) (c.node j) s t


/-- The exact coordinate signs of a minus-one coroot. -/
def corootAction (i : Fin 6) (a : Fin 4 → Multiplicative F) : Fin 4 → Multiplicative F :=
  fun k => Multiplicative.ofAdd (((((-1 : Fˣ) ^ typeE6CartanMatrix (rootIndex k) i : Fˣ) : F)) * (a k).toAdd)

theorem coroot_chart (i : Fin 6) (a : Fin 4 → Multiplicative F) :
    c.coroot F i * c.chart F a * (c.coroot F i)⁻¹ = c.chart F (corootAction F i a) := by
  rw [chart_formula]
  change MulAut.conj (c.coroot F i) (_ * _ * _ * _) = _
  simp only [map_mul, MulAut.conj_apply, coroot_root]
  rw [chart_formula]
  simp only [corootAction, rootIndex, Matrix.cons_val, toAdd_ofAdd]

theorem coroot_three_chart (a : Fin 4 → Multiplicative F) :
    c.coroot F 3 * c.chart F a * (c.coroot F 3)⁻¹ =
      c.chart F ![a 0,a 1,(a 2)⁻¹,a 3] := by
  rw [coroot_chart]
  congr 1
  funext k
  fin_cases k <;> simp [corootAction,rootIndex,typeE6CartanMatrix,Fin.ext_iff]

theorem coroot_two_chart (a : Fin 4 → Multiplicative F) :
    c.coroot F 2 * c.chart F a * (c.coroot F 2)⁻¹ =
      c.chart F ![a 0,a 1,a 2,(a 3)⁻¹] := by
  rw [coroot_chart]
  congr 1
  funext k
  fin_cases k <;> simp [corootAction,rootIndex,typeE6CartanMatrix,Fin.ext_iff]

theorem coroot_pair_chart (a : Fin 4 → Multiplicative F) :
    (c.coroot F 1 * c.coroot F 4) * c.chart F a * (c.coroot F 1 * c.coroot F 4)⁻¹ =
      c.chart F ![(a 0)⁻¹,(a 1)⁻¹,a 2,a 3] := by
  calc
    _ = c.coroot F 1 * (c.coroot F 4 * c.chart F a * (c.coroot F 4)⁻¹) * (c.coroot F 1)⁻¹ := by group
    _ = c.chart F (corootAction F 1 (corootAction F 4 a)) := by rw [coroot_chart,coroot_chart]
    _ = _ := by
      congr 1
      funext k
      fin_cases k <;> simp [corootAction,rootIndex,typeE6CartanMatrix,Fin.ext_iff]

/-- These actual coroot products separately invert the four coordinates. -/
def detector : Fin 4 → rootGenerated P b F :=
  ![c.coroot F 1 * c.coroot F 3, c.coroot F 4 * c.coroot F 3, c.coroot F 3, c.coroot F 2]

theorem detector_chart (i : Fin 4) (a : Fin 4 → Multiplicative F) :
    c.detector F i * c.chart F a * (c.detector F i)⁻¹ =
      c.chart F (CoordinateInversion.invertCoordinate i a) := by
  fin_cases i
  · change (c.coroot F 1 * c.coroot F 3) * c.chart F a * (c.coroot F 1 * c.coroot F 3)⁻¹ = _
    calc
      _ = c.coroot F 1 * (c.coroot F 3 * c.chart F a * (c.coroot F 3)⁻¹) * (c.coroot F 1)⁻¹ := by group
      _ = c.chart F (corootAction F 1 (corootAction F 3 a)) := by rw [coroot_chart,coroot_chart]
      _ = _ := by
        congr 1
        funext k
        fin_cases k <;> simp [corootAction,rootIndex,typeE6CartanMatrix,CoordinateInversion.invertCoordinate,Fin.ext_iff]
  · change (c.coroot F 4 * c.coroot F 3) * c.chart F a * (c.coroot F 4 * c.coroot F 3)⁻¹ = _
    calc
      _ = c.coroot F 4 * (c.coroot F 3 * c.chart F a * (c.coroot F 3)⁻¹) * (c.coroot F 4)⁻¹ := by group
      _ = c.chart F (corootAction F 4 (corootAction F 3 a)) := by rw [coroot_chart,coroot_chart]
      _ = _ := by
        congr 1
        funext k
        fin_cases k <;> simp [corootAction,rootIndex,typeE6CartanMatrix,CoordinateInversion.invertCoordinate,Fin.ext_iff]
  · change c.coroot F 3 * c.chart F a * (c.coroot F 3)⁻¹ = _
    rw [coroot_three_chart]
    congr 1
    funext k
    fin_cases k <;> simp [CoordinateInversion.invertCoordinate,Fin.ext_iff]
  · change c.coroot F 2 * c.chart F a * (c.coroot F 2)⁻¹ = _
    rw [coroot_two_chart]
    congr 1
    funext k
    fin_cases k <;> simp [CoordinateInversion.invertCoordinate,Fin.ext_iff]

/-- The literal chart remains faithful in the center quotient. -/
def projectiveChart : (Fin 4 → Multiplicative F) →* Model P b F :=
  (projection P b F).comp (c.chart F)

theorem projectiveChart_injective (h2 : (2 : F) ≠ 0) :
    Function.Injective (c.projectiveChart F) := by
  apply CoordinateInversion.field_quotient_injective (fun _ => h2) (c.chart F)
  · intro i t u h
    apply c.rootHom_injective F i
    change c.root F i t.toAdd = c.root F i u.toAdd
    simpa only [chart_single] using h
  · exact c.detector_chart F

theorem chart_injective (h2 : (2 : F) ≠ 0) : Function.Injective (c.chart F) :=
  Function.Injective.of_comp (c.projectiveChart_injective F h2)

end SixNodes
end ExceptionalSplit.OddRankFour
