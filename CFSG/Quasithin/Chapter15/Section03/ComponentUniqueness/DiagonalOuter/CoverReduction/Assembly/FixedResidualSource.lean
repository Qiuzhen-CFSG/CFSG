module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.Assembly.Inputs
public import Theory.SpecificGroups.PSL3Four.CentralCover.MarkedFixedResiduals
public import Theory.SpecificGroups.PSL3Four.GraphFieldMarking
public import Theory.SpecificGroups.PSL3.OddPrimeGraphExtension.FieldTransport
import Mathlib.Tactic.Group

/-!
# Actual fixed-residual models of the selected four-cover

The selected component's original projective marking and central plane
construct a perfect four-cover. Each actual involution is normalized on the
projective quotient separately. The covering map is postcomposed with that
marking, leaving the component and its actual involutory action unchanged.
The one-action residual calculations then give the literal embedded residuals.

Source: Aschbacher–Smith, 15.3.38, printed pp.1136–1137. Only the supplied
source setup, constructed local result, and constructed Sylow lift are used.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
open LocalCover LocalCover.SourceBorel GlobalGeometry
open Matrix.PSL3.OuterSolvable
open Matrix.PSL3Even.OuterElementaryRank.FixedRanks
variable {G : Type*} [Group G] [Finite G]
variable {d : CharacteristicTwo.LocalData G} {I L : Subgroup G}

/-- The actual center is the selected natural elementary four-plane. -/
theorem LocalResult.center_isKleinFour (r : LocalResult d I L) : IsKleinFour (center L) := by
  obtain ⟨i, hi⟩ := r.plane
  let e : center L ≃* d.action.plane i :=
    ((center L).equivMapOfInjective L.subtype L.subtype_injective).trans
      (MulEquiv.subgroupCongr (r.cover.center_plane.trans hi))
  let : IsElementaryAbelian 2 (d.action.plane i) := d.action.elementary_of_le (d.action.plane_le i)
  let : Nontrivial (d.action.plane i) := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [d.action.card_plane]; decide)
  exact ⟨(Nat.card_congr e.toEquiv).trans (d.action.card_plane i),
    (Monoid.exponent_eq_of_mulEquiv e).trans IsElementaryAbelian.exponent_eq_prime⟩

/-- Postcompose the actual component quotient with a supplied projective
marking. The map and its central kernel are retained literally. -/
def LocalResult.fourCover (r : LocalResult d I L) (h : Setup d I L)
    (e : PSL(3,r.marking.F) ≃* Matrix.PSL3Four.PSL) : Matrix.PSL3Four.FourCover L where
  toMonoidHom := e.toMonoidHom.comp (projectiveMap r.marking)
  surjective := e.surjective.comp (r.marking.equivalence.surjective.comp
    (QuotientGroup.mk'_surjective _))
  isPerfect := h.perfect
  ker_le_center := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, projectiveMap_ker,
      ← r.cover.center_core]
  ker_eq_center := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, projectiveMap_ker,
      ← r.cover.center_core]
  center_isKleinFour := r.center_isKleinFour

@[simp] theorem LocalResult.fourCover_apply (r : LocalResult d I L) (h : Setup d I L)
    (e : PSL(3,r.marking.F) ≃* Matrix.PSL3Four.PSL) (x : L) :
    (r.fourCover h e).toMonoidHom x = e (projectiveMap r.marking x) := by rfl

private def fixedEquiv (a : G) (α : MulAut L) (ha : Candidates.ConjugationOn L a α) :
    L.subgroupOf (centralizer ({a} : Set G)) ≃* α.fixedSubgroup where
  toFun x := ⟨⟨x, x.property⟩, by
    rw [MulAut.mem_fixedSubgroup]
    apply Subtype.ext
    rw [ha]
    exact mul_inv_eq_iff_eq_mul.mpr
      (mem_centralizer_singleton_iff.mp x.val.property).symm⟩
  invFun x := ⟨⟨x, by
    apply mem_centralizer_singleton_iff.mpr
    have hx := congrArg (fun z : L => (z : G))
      ((MulAut.mem_fixedSubgroup _ _).mp x.property)
    rw [ha] at hx
    exact (mul_inv_eq_iff_eq_mul.mp hx).symm⟩, x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The ambient centralizer residual is the residual of the actual action
on the component, via the literal subgroup inclusions. -/
def residualEquivOfConjugation (a : G) (α : MulAut L)
    (ha : Candidates.ConjugationOn L a α) :
    graphResidualIn L a ≃* pResidual 2 α.fixedSubgroup := by
  let A := L.subgroupOf (centralizer ({a} : Set G))
  let e := fixedEquiv a α ha
  exact ((pResidual 2 A).equivMapOfInjective A.subtype A.subtype_injective).symm.trans
    (((pResidual 2 A).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr (map_pResidual 2 e)))

omit [Finite G] in
private theorem conjugation_sq (a : G) (α : MulAut L)
    (ha : Candidates.ConjugationOn L a α) (h2 : a ^ 2 = 1) : α ^ 2 = 1 := by
  ext x
  change ((α (α x) : L) : G) = x
  rw [ha, ha]
  calc
    _ = a ^ 2 * (x : G) * (a ^ 2)⁻¹ := by
      simp only [pow_two]
      group
    _ = x := by rw [h2]; simp

omit [Finite G] in
private theorem projective_sq (r : LocalResult d I L) (α : MulAut L)
    (β : MulAut PSL(3,r.marking.F))
    (hc : ∀ x, projectiveMap r.marking (α x) = β (projectiveMap r.marking x))
    (hα : α ^ 2 = 1) : β ^ 2 = 1 := by
  ext x
  obtain ⟨y, rfl⟩ := r.marking.equivalence.surjective x
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) y
  change β (β (projectiveMap r.marking z)) = projectiveMap r.marking z
  rw [← hc, ← hc]
  exact congrArg (projectiveMap r.marking) (DFunLike.congr_fun hα z)

private def coefficientEquiv {K : Type*} [Field K] [Finite K]
    (hK : Nat.card K = 4) : K ≃+* Matrix.PSL3Four.F := by
  let : Fintype K := Fintype.ofFinite K
  let : Fintype Matrix.PSL3Four.F := Fintype.ofFinite _
  exact FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, Matrix.PSL3Four.card_F])

private theorem field_order {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 4)
    (σ : K ≃+* K) (hσ : ∀ x, σ x = x ^ 2) : orderOf σ = 2 := by
  let : Fintype K := Fintype.ofFinite K
  let : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
    (by simpa [Nat.card_eq_fintype_card] using hK)
  have he : σ = frobeniusEquiv K 2 := by
    ext x
    exact hσ x
  rw [he]
  exact FiniteField.frobeniusEquiv_orderOf_of_card hK

private theorem fieldEquiv_square {K : Type*} [Field K]
    (e : K ≃+* Matrix.PSL3Four.F) (σ : K ≃+* K) (hσ : ∀ x, σ x = x ^ 2)
    (x : PSL(3,K)) :
    Atlas.fieldEquivPSL 3 e (fieldAction K σ x) =
      Matrix.PSL3Four.pslFrobenius (Atlas.fieldEquivPSL 3 e x) := by
  have he := Matrix.PSL3Four.fieldEquivPSL_graphField e σ hσ x
  change Atlas.fieldEquivPSL 3 e (graph K (fieldAction K σ x)) = _ at he
  rw [Matrix.PSL3.OddPrimeGraphExtension.FieldTransport.fieldEquivPSL_graph] at he
  exact (graph Matrix.PSL3Four.F).injective he

private theorem graph_marking {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 4)
    (g : GL (Fin 3) K) (hs : (linearConj K g * graph K) ^ 2 = 1) :
    ∃ e : PSL(3,K) ≃* Matrix.PSL3Four.PSL, ∀ x,
      e ((linearConj K g * graph K) x) = graph Matrix.PSL3Four.F (e x) := by
  obtain ⟨a, ha⟩ := graph_involution_conjugate (f := 2) (by decide) hK g hs
  let f := coefficientEquiv hK
  refine ⟨a.trans (Atlas.fieldEquivPSL 3 f), fun x => ?_⟩
  have hx := DFunLike.congr_fun ha (a x)
  change a ((linearConj K g * graph K) (a.symm (a x))) = graph K (a x) at hx
  rw [a.symm_apply_apply] at hx
  change Atlas.fieldEquivPSL 3 f (a ((linearConj K g * graph K) x)) = _
  rw [hx]
  exact Matrix.PSL3.OddPrimeGraphExtension.FieldTransport.fieldEquivPSL_graph f (a x)

private theorem field_marking {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 4)
    (g : GL (Fin 3) K) (σ : K ≃+* K) (hσ : ∀ x, σ x = x ^ 2)
    (hs : (linearConj K g * fieldAction K σ) ^ 2 = 1) :
    ∃ e : PSL(3,K) ≃* Matrix.PSL3Four.PSL, ∀ x,
      e ((linearConj K g * fieldAction K σ) x) = Matrix.PSL3Four.pslFrobenius (e x) := by
  obtain ⟨C, hC⟩ := FieldDescent.exists_linear_conjugate_field g σ (field_order hK σ hσ) hs
  let a := linearConj K C
  let f := coefficientEquiv hK
  refine ⟨a.trans (Atlas.fieldEquivPSL 3 f), fun x => ?_⟩
  have hx := DFunLike.congr_fun hC (a x)
  change a ((linearConj K g * fieldAction K σ) (a.symm (a x))) = fieldAction K σ (a x) at hx
  rw [a.symm_apply_apply] at hx
  change Atlas.fieldEquivPSL 3 f (a ((linearConj K g * fieldAction K σ) x)) = _
  rw [hx]
  exact fieldEquiv_square f σ hσ (a x)

/-- The selected graph involution has the source's literal PSL₂ residual,
over the coefficient field in the original quotient marking. -/
theorem graph_residual_model (h : Setup d I L) (r : LocalResult d I L)
    (b : SylowThreeLift d.T d.Y d.S L r.marking) :
    Nonempty (graphResidualIn L (b.dihedral.firstReflection : G) ≃* PSL(2,r.marking.F)) := by
  obtain ⟨g, α, hα, hc⟩ := b.graph
  change ∀ x, projectiveMap r.marking (α x) =
    (linearConj r.marking.F g * graph r.marking.F) (projectiveMap r.marking x) at hc
  have h2 : (b.dihedral.firstReflection : G) ^ 2 = 1 := by
    exact congrArg Subtype.val (b.dihedral.firstReflection_order ▸
      pow_orderOf_eq_one b.dihedral.firstReflection)
  have hs := projective_sq r α _ hc (conjugation_sq _ α hα h2)
  obtain ⟨e, he⟩ := graph_marking r.marking.card g hs
  let c := r.fourCover h e
  have hcompat x : c.toMonoidHom (α x) = graph Matrix.PSL3Four.F (c.toMonoidHom x) := by
    change e (projectiveMap r.marking (α x)) = graph Matrix.PSL3Four.F (e (projectiveMap r.marking x))
    rw [hc, he]
  exact ⟨(residualEquivOfConjugation _ α hα).trans
    ((c.graphResidualEquivOfCompatible α hcompat).trans
      (Atlas.fieldEquivPSL 2 (coefficientEquiv r.marking.card).symm))⟩

/-- The selected field involution has the literal PSL₃(2) residual. -/
theorem field_residual_model (h : Setup d I L) (r : LocalResult d I L)
    (b : SylowThreeLift d.T d.Y d.S L r.marking) :
    Nonempty (graphResidualIn L (b.dihedral.halfTurn : G) ≃* PSL(3,ZMod 2)) := by
  obtain ⟨σ, g, hσ, α, hα, hc⟩ := b.field
  change ∀ x, projectiveMap r.marking (α x) =
    (linearConj r.marking.F g * fieldAction r.marking.F σ) (projectiveMap r.marking x) at hc
  have h2 : (b.dihedral.halfTurn : G) ^ 2 = 1 := by
    exact congrArg Subtype.val (b.dihedral.halfTurn_order ▸ pow_orderOf_eq_one b.dihedral.halfTurn)
  have hs := projective_sq r α _ hc (conjugation_sq _ α hα h2)
  obtain ⟨e, he⟩ := field_marking r.marking.card g σ hσ hs
  let c := r.fourCover h e
  have hcompat x : c.toMonoidHom (α x) = Matrix.PSL3Four.pslFrobenius (c.toMonoidHom x) := by
    change e (projectiveMap r.marking (α x)) = Matrix.PSL3Four.pslFrobenius (e (projectiveMap r.marking x))
    rw [hc, he]
  exact ⟨(residualEquivOfConjugation _ α hα).trans
    (c.fieldResidualEquivOfCompatible α hcompat)⟩

/-- The selected product of graph reflection and half-turn has the literal
elementary-nine fixed residual in the component. -/
theorem graphField_residual_model (h : Setup d I L) (r : LocalResult d I L)
    (b : SylowThreeLift d.T d.Y d.S L r.marking) :
    Nonempty (graphResidualIn L ((b.dihedral.firstReflection : G) *
      (b.dihedral.halfTurn : G)) ≃* Multiplicative (Fin 2 → ZMod 3)) := by
  obtain ⟨g, α, hα, hcα⟩ := b.graph
  obtain ⟨σ, k, hσ, β, hβ, hcβ⟩ := b.field
  change ∀ x, projectiveMap r.marking (α x) =
    (linearConj r.marking.F g * graph r.marking.F) (projectiveMap r.marking x) at hcα
  change ∀ x, projectiveMap r.marking (β x) =
    (linearConj r.marking.F k * fieldAction r.marking.F σ) (projectiveMap r.marking x) at hcβ
  let a := α * β
  let w : G := (b.dihedral.firstReflection : G) * (b.dihedral.halfTurn : G)
  have hw : Candidates.ConjugationOn L w a := by
    intro x
    change ((α (β x) : L) : G) = w * (x : G) * w⁻¹
    rw [hα, hβ]
    dsimp [w]
    group
  have hw2 : w ^ 2 = 1 := by
    have he := congrArg (fun x : d.T => (x : G)) b.dihedral.conjugate_firstReflection
    have hτ2 : (b.dihedral.firstReflection : G) ^ 2 = 1 :=
      congrArg Subtype.val (b.dihedral.firstReflection_order ▸ pow_orderOf_eq_one b.dihedral.firstReflection)
    change (b.dihedral.secondReflection : G) * (b.dihedral.firstReflection : G) *
      (b.dihedral.secondReflection : G)⁻¹ = w at he
    rw [← he, ← MulAut.conj_apply, ← map_pow, hτ2, map_one]
  let m := g * inverseTransposeGL r.marking.F k
  have hprod : (linearConj r.marking.F g * graph r.marking.F) *
      (linearConj r.marking.F k * fieldAction r.marking.F σ) =
      linearConj r.marking.F m * fieldAction r.marking.F σ * graph r.marking.F := by
    calc
      _ = linearConj r.marking.F g * (graph r.marking.F * linearConj r.marking.F k) *
        fieldAction r.marking.F σ := by group
      _ = linearConj r.marking.F g *
        (linearConj r.marking.F (inverseTransposeGL r.marking.F k) * graph r.marking.F) *
        fieldAction r.marking.F σ := by rw [graph_linearConj]
      _ = (linearConj r.marking.F g * linearConj r.marking.F (inverseTransposeGL r.marking.F k)) *
        (graph r.marking.F * fieldAction r.marking.F σ) := by group
      _ = linearConj r.marking.F m * (fieldAction r.marking.F σ * graph r.marking.F) := by
        rw [← map_mul, ← (field_commute_graph σ).eq]
      _ = _ := by group
  have hc x : projectiveMap r.marking (a x) =
      (linearConj r.marking.F m * fieldAction r.marking.F σ * graph r.marking.F)
        (projectiveMap r.marking x) := by
    change projectiveMap r.marking (α (β x)) = _
    rw [hcα, hcβ]
    exact DFunLike.congr_fun hprod (projectiveMap r.marking x)
  have hs := projective_sq r a _ hc (conjugation_sq w a hw hw2)
  have hne : σ ≠ 1 := by
    intro he
    have ho := field_order r.marking.card σ hσ
    rw [he, orderOf_one] at ho
    omega
  obtain ⟨e, he⟩ := Matrix.PSL3Four.GraphFieldMarking.marking r.marking.card m σ hne hs
  let c := r.fourCover h e
  have hcompat x : c.toMonoidHom (a x) =
      (graph Matrix.PSL3Four.F * Matrix.PSL3Four.pslFrobenius) (c.toMonoidHom x) := by
    change e (projectiveMap r.marking (a x)) =
      (graph Matrix.PSL3Four.F * Matrix.PSL3Four.pslFrobenius) (e (projectiveMap r.marking x))
    rw [hc, he]
  exact ⟨(residualEquivOfConjugation w a hw).trans
    (c.graphFieldResidualEquivOfCompatible a hcompat)⟩

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
end
