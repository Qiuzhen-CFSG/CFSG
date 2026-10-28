module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.FourActors.Geometry.Transfer

/-!
# Quarter-turn seeds for outer four-group fusion

In the literal PSL3 graph extension, let z0=diag(-1,-1,1),
w=diag(1,-1,-1), and let r be the determinant-one quarter-turn on coordinates
0,1. For each nonzero d, the outer involution
 a(d)=inner(diag(d,d,d^(-2)))*inverse-transpose
centralizes r and w. The relations r^2=z0 and w*r*w^(-1)=r^(-1) show
that <r,w,a(d)> is a two-subgroup in C(z0), and r carries w to w*z0.
This constructs the common seed used by `ConjugateFusion.lean`.

`StandardActorCoverage` states the separate simultaneous normal-form problem
for an arbitrary original actor. It is not proved by these matrix calculations.

Source: the concrete fusion step used for Aschbacher--Smith E.1.14(7),
printed p.214, through E.1.1--5, pp.209--210, and A.3.21(a), p.55.
The book cites Aschbacher (1982), Lemma 4.11, for the full generation result.
-/

public section
open Subgroup Matrix
open scoped MatrixGroups
open Matrix.PSL3 Matrix.PSL3.OuterSolvable
open Matrix.PSL3.OddPrimeGraphExtension
open Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure
open CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerGenerationGeometry
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.ConjugateFusion
variable (F : Type*) [Field F]

@[expose] def reflectionSL : SL(3,F) :=
  ⟨!![1, 0, 0; 0, -1, 0; 0, 0, -1], by simp [Matrix.det_fin_three]⟩

@[expose] def quarterTurnSL : SL(3,F) :=
  ⟨!![0, -1, 0; 1, 0, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

@[expose] def twistSL (d : Fˣ) : SL(3,F) :=
  ⟨!![d, 0, 0; 0, d, 0; 0, 0, (d⁻¹ : Fˣ)^2], by
    simp [Matrix.det_fin_three, pow_two, ← mul_assoc]⟩

@[expose] def reflection : graphExtension F := innerSL F (reflectionSL F)
@[expose] def quarterTurn : graphExtension F := innerSL F (quarterTurnSL F)
@[expose] def twistedGraph (d : Fˣ) : graphExtension F :=
  innerSL F (twistSL F d) * graphElement F
@[expose] def standardActor (d : Fˣ) : Subgroup (graphExtension F) :=
  zpowers (reflection F) ⊔ zpowers (twistedGraph F d)
@[expose] def seed (d : Fˣ) : Subgroup (graphExtension F) :=
  (zpowers (quarterTurn F) ⊔ zpowers (reflection F)) ⊔ zpowers (twistedGraph F d)

/-- Simultaneous normal form for the original outer four-group; existence is
an independent finite-field congruence problem. -/
@[expose] def StandardActorCoverage : Prop :=
  ∀ A : Subgroup (graphExtension F), IsElementaryAbelian 2 A →
    Nat.card A = 4 → Nat.card (A ⊓ innerPart F : Subgroup _) = 2 →
    ∃ (g : graphExtension F) (d : Fˣ),
      A.map (MulAut.conj g).toMonoidHom = standardActor F d

private theorem reflectionSL_sq : reflectionSL F ^ 2 = 1 := by
  rw [pow_two]
  apply Subtype.ext
  change (reflectionSL F).val * (reflectionSL F).val = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reflectionSL, Matrix.mul_apply, Fin.sum_univ_three]

private theorem quarterTurnSL_sq : quarterTurnSL F ^ 2 = SL3.standardInvolution F := by
  rw [pow_two]
  apply Subtype.ext
  change (quarterTurnSL F).val * (quarterTurnSL F).val = (SL3.standardInvolution F).val
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quarterTurnSL, SL3.standardInvolution, Matrix.mul_apply, Fin.sum_univ_three]

private theorem quarterTurnSL_reflection :
    quarterTurnSL F * reflectionSL F =
      (reflectionSL F * SL3.standardInvolution F) * quarterTurnSL F := by
  apply Subtype.ext
  change (quarterTurnSL F).val * (reflectionSL F).val =
    ((reflectionSL F).val * (SL3.standardInvolution F).val) * (quarterTurnSL F).val
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quarterTurnSL, reflectionSL, SL3.standardInvolution, Matrix.mul_apply,
      Fin.sum_univ_three]

private theorem quarterTurnSL_transpose :
    Matrix.SpecialLinearGroup.transpose (quarterTurnSL F) = (quarterTurnSL F)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  apply Subtype.ext
  change (quarterTurnSL F).val.transpose * (quarterTurnSL F).val = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quarterTurnSL, Matrix.mul_apply, Fin.sum_univ_three]

private theorem graphSL_reflection : graphSL F (reflectionSL F) = reflectionSL F := by
  change (Matrix.SpecialLinearGroup.transpose (reflectionSL F))⁻¹ = _
  have ht : Matrix.SpecialLinearGroup.transpose (reflectionSL F) = reflectionSL F := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [ht]
  symm
  apply eq_inv_of_mul_eq_one_left
  exact (pow_two _).symm.trans (reflectionSL_sq F)

private theorem twistSL_transpose (d : Fˣ) :
    Matrix.SpecialLinearGroup.transpose (twistSL F d) = twistSL F d := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem twistSL_commutes (d : Fˣ) :
    Commute (twistSL F d) (reflectionSL F) ∧
      Commute (twistSL F d) (quarterTurnSL F) := by
  constructor
  · apply Subtype.ext
    change (twistSL F d).val * (reflectionSL F).val =
      (reflectionSL F).val * (twistSL F d).val
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [twistSL, reflectionSL, Matrix.mul_apply, Fin.sum_univ_three]
  · apply Subtype.ext
    change (twistSL F d).val * (quarterTurnSL F).val =
      (quarterTurnSL F).val * (twistSL F d).val
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [twistSL, quarterTurnSL, Matrix.mul_apply, Fin.sum_univ_three]

private theorem graph_inner (x : SL(3,F)) :
    graphElement F * innerSL F x * (graphElement F)⁻¹ = innerSL F (graphSL F x) := by
  symm
  apply Subtype.ext
  change MulAut.conj (projection F (graphSL F x)) =
    graph F * MulAut.conj (projection F x) * (graph F)⁻¹
  have he : projection F (graphSL F x) = graph F (projection F x) := rfl
  rw [he]
  ext y
  simp only [MulAut.mul_apply, MulAut.inv_apply, MulAut.conj_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

private theorem graph_commutes {x : SL(3,F)} (hx : graphSL F x = x) :
    Commute (graphElement F) (innerSL F x) := by
  apply mul_inv_eq_iff_eq_mul.mp
  rw [graph_inner, hx]

private theorem twistedGraph_sq (d : Fˣ) : twistedGraph F d ^ 2 = 1 := by
  have hg : graphElement F ^ 2 = 1 := Subtype.ext (graph_sq F)
  have hd : graphSL F (twistSL F d) = (twistSL F d)⁻¹ := by
    change (Matrix.SpecialLinearGroup.transpose _)⁻¹ = _
    rw [twistSL_transpose]
  have hact := graph_inner F (twistSL F d)
  rw [hd, map_inv] at hact
  calc
    twistedGraph F d ^ 2 = innerSL F (twistSL F d) *
        (graphElement F * innerSL F (twistSL F d) * (graphElement F)⁻¹) *
        (graphElement F ^ 2) := by simp only [twistedGraph, pow_two]; group
    _ = 1 := by rw [hact, hg, mul_inv_cancel, one_mul]

private theorem twistedGraph_commutes (d : Fˣ) :
    Commute (twistedGraph F d) (reflection F) ∧
      Commute (twistedGraph F d) (quarterTurn F) := by
  obtain ⟨hw, hr⟩ := twistSL_commutes F d
  constructor
  · exact (hw.map (innerSL F)).mul_left (graph_commutes F (graphSL_reflection F))
  · have hfix : graphSL F (quarterTurnSL F) = quarterTurnSL F := by
      change (Matrix.SpecialLinearGroup.transpose _)⁻¹ = _
      rw [quarterTurnSL_transpose, inv_inv]
    exact (hr.map (innerSL F)).mul_left (graph_commutes F hfix)

private theorem reflection_sq : reflection F ^ 2 = 1 := by
  rw [reflection, ← map_pow, reflectionSL_sq, map_one]

private theorem quarterTurn_sq : quarterTurn F ^ 2 = standardInner F := by
  rw [quarterTurn, ← map_pow, quarterTurnSL_sq]
  rfl

private theorem quarterTurn_fourth : quarterTurn F ^ 4 = 1 := by
  rw [show 4 = 2 * 2 from rfl, pow_mul, quarterTurn_sq]
  change (innerSL F (SL3.standardInvolution F)) ^ 2 = 1
  rw [← map_pow, SL3.standardInvolution_sq, map_one]

private theorem quarterTurn_reflection :
    MulAut.conj (quarterTurn F) (reflection F) = reflection F * standardInner F := by
  apply mul_inv_eq_iff_eq_mul.mpr
  change innerSL F (quarterTurnSL F) * innerSL F (reflectionSL F) =
    (innerSL F (reflectionSL F) * innerSL F (SL3.standardInvolution F)) *
      innerSL F (quarterTurnSL F)
  simp only [← map_mul, quarterTurnSL_reflection]

private theorem reflection_quarterTurn :
    MulAut.conj (reflection F) (quarterTurn F) = (quarterTurn F)⁻¹ := by
  have hi : (reflectionSL F)⁻¹ = reflectionSL F := by
    symm
    exact eq_inv_of_mul_eq_one_left ((pow_two _).symm.trans (reflectionSL_sq F))
  change innerSL F (reflectionSL F) * innerSL F (quarterTurnSL F) *
    (innerSL F (reflectionSL F))⁻¹ = (innerSL F (quarterTurnSL F))⁻¹
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  rw [hi, ← quarterTurnSL_transpose]
  apply Subtype.ext
  change (reflectionSL F).val * (quarterTurnSL F).val * (reflectionSL F).val =
    (quarterTurnSL F).val.transpose
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quarterTurnSL, reflectionSL, Matrix.mul_apply, Fin.sum_univ_three]

private theorem seed_isPGroup (d : Fˣ) : IsPGroup 2 (seed F d) := by
  have hr : IsPGroup 2 (zpowers (quarterTurn F)) :=
    IsPGroup.of_card_dvd_pow (n := 2) (by
      simpa only [Nat.card_zpowers, Nat.reducePow] using orderOf_dvd_of_pow_eq_one (quarterTurn_fourth F))
  have hw : IsPGroup 2 (zpowers (reflection F)) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by
      simpa only [Nat.card_zpowers, pow_one] using orderOf_dvd_of_pow_eq_one (reflection_sq F))
  have ha : IsPGroup 2 (zpowers (twistedGraph F d)) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by
      simpa only [Nat.card_zpowers, pow_one] using orderOf_dvd_of_pow_eq_one (twistedGraph_sq F d))
  have hn : zpowers (reflection F) ≤ normalizer (zpowers (quarterTurn F) : Set _) := by
    apply zpowers_le.mpr
    rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change zpowers (MulAut.conj (reflection F) (quarterTurn F)) = _
    rw [reflection_quarterTurn, zpowers_inv]
  have hc : zpowers (twistedGraph F d) ≤
      centralizer (zpowers (quarterTurn F) ⊔ zpowers (reflection F) : Subgroup _) := by
    apply le_centralizer_iff.mpr
    apply sup_le
    · apply zpowers_le.mpr
      intro a ha
      obtain ⟨n, rfl⟩ := ha
      exact ((twistedGraph_commutes F d).2.zpow_left n).eq
    · apply zpowers_le.mpr
      intro a ha
      obtain ⟨n, rfl⟩ := ha
      exact ((twistedGraph_commutes F d).1.zpow_left n).eq
  exact (hr.to_sup_of_normal_left' hw hn).to_sup_of_normal_left' ha
    (hc.trans (Subgroup.centralizer_le_normalizer _))

private theorem seed_centralizes (d : Fˣ) :
    seed F d ≤ centralizer ({standardInner F} : Set (graphExtension F)) := by
  apply sup_le
  · apply sup_le
    · apply zpowers_le.mpr
      apply mem_centralizer_singleton_iff.mpr
      rw [← quarterTurn_sq]
      exact (Commute.self_pow (quarterTurn F) 2).eq
    · apply zpowers_le.mpr
      apply mem_centralizer_singleton_iff.mpr
      change innerSL F (reflectionSL F) * innerSL F (SL3.standardInvolution F) =
        innerSL F (SL3.standardInvolution F) * innerSL F (reflectionSL F)
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      change (reflectionSL F).val * (SL3.standardInvolution F).val =
        (SL3.standardInvolution F).val * (reflectionSL F).val
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [reflectionSL, SL3.standardInvolution, Matrix.mul_apply, Fin.sum_univ_three]
  · apply zpowers_le.mpr
    apply mem_centralizer_singleton_iff.mpr
    rw [← quarterTurn_sq]
    exact ((twistedGraph_commutes F d).2.pow_right 2).eq

private theorem projection_eq_of_innerSL_eq [IsSimpleGroup PSL(3,F)]
    {x y : SL(3,F)} (h : innerSL F x = innerSL F y) :
    projection F x = projection F y := by
  apply (innerPartEquiv F).injective
  apply Subtype.ext
  apply Subtype.ext
  simp only [innerPartEquiv_apply_coe]
  exact congrArg Subtype.val h

private theorem innerSL_ne_one_of_not_central [IsSimpleGroup PSL(3,F)]
    {x : SL(3,F)} (hx : x ∉ center SL(3,F)) : innerSL F x ≠ 1 := by
  intro h
  have he := projection_eq_of_innerSL_eq F (h.trans (map_one (innerSL F)).symm)
  rw [map_one] at he
  exact hx ((QuotientGroup.eq_one_iff x).mp he)

private theorem reflection_orderOf [IsSimpleGroup PSL(3,F)] (h2 : (2 : F) ≠ 0) :
    orderOf (reflection F) = 2 := by
  apply orderOf_eq_prime (reflection_sq F)
  apply innerSL_ne_one_of_not_central
  intro h
  obtain ⟨u, _, hu⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h
  have h0 := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 0 0) hu
  have h1 := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 1 1) hu
  have he : (1 : F) = -1 := h0.symm.trans h1
  apply h2
  linear_combination he

private theorem reflection_ne_standard [IsSimpleGroup PSL(3,F)] (h2 : (2 : F) ≠ 0) :
    reflection F ≠ standardInner F := by
  intro h
  have he := projection_eq_of_innerSL_eq F h
  have hc : reflectionSL F * (SL3.standardInvolution F)⁻¹ ∈ center SL(3,F) := by
    apply (QuotientGroup.eq_one_iff _).mp
    change projection F (_ * _) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel]
  have hi : (SL3.standardInvolution F)⁻¹ = SL3.standardInvolution F := by
    symm
    exact eq_inv_of_mul_eq_one_left ((pow_two _).symm.trans (SL3.standardInvolution_sq F))
  rw [hi] at hc
  obtain ⟨u, _, hu⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  change Matrix.scalar (Fin 3) u = (reflectionSL F).val * (SL3.standardInvolution F).val at hu
  have h0 := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 0 0) hu
  have h1 := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 1 1) hu
  have heq : (-1 : F) = 1 := by
    have hh := h0.symm.trans h1
    simpa [reflectionSL, SL3.standardInvolution, Matrix.mul_apply, Fin.sum_univ_three] using hh
  apply h2
  linear_combination -heq

/-- Each explicit actor has a common two-subgroup in the standard centralizer,
containing the quarter-turn which interchanges the other two inner lines. -/
theorem standardActor_seed [IsSimpleGroup PSL(3,F)] (h2 : (2 : F) ≠ 0) (d : Fˣ) :
    IsPGroup 2 (seed F d) ∧
    seed F d ≤ centralizer ({standardInner F} : Set (graphExtension F)) ∧
    standardActor F d ≤ seed F d ∧
    reflection F ∈ innerPart F ∧ orderOf (reflection F) = 2 ∧
    reflection F ≠ standardInner F ∧ reflection F ∈ standardActor F d ∧
    quarterTurn F ∈ seed F d ∧
    MulAut.conj (quarterTurn F) (reflection F) = reflection F * standardInner F := by
  refine ⟨seed_isPGroup F d, seed_centralizes F d,
    sup_le (le_sup_of_le_left le_sup_right) le_sup_right,
    ?_, reflection_orderOf F h2, reflection_ne_standard F h2,
    mem_sup_left (mem_zpowers _),
    mem_sup_left (mem_sup_left (mem_zpowers _)), quarterTurn_reflection F⟩
  exact ⟨projection F (reflectionSL F), rfl⟩

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.ConjugateFusion
