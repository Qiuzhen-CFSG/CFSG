module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Models.NaturalOdd
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Models.NilpotentFive
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Models.RankOne
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting
public import Theory.GroupTheory.CComponent.FittingCentralizer
public import Theory.GroupTheory.GeneralizedFitting.CentralCoverLift

/-!
# The surviving source list supplies the outside outer action

A component with trivial two-core cannot be quasisimple if it surjects onto
odd-characteristic SL₂: central-kernel lifting would lift its central
involution into the trivial two-core. The genuine noncentral A.3.6 theorem
therefore gives the natural or nilpotent kernel, with its actual action.
The two completed kernel calculations prove nilpotence of the outer group.

Apply this to the literal K/O₂(K), deriving its relative C-component and
SQTK properties from the original flag normalizer. The source unique-flag
theorem supplies the first residual's binary PSL₂ quotient. Thus every row
of the surviving 11.4.1(2) list gives the two-closed outer group required by
both 11.4.3 products and the residual-compatible H-star selection.

The survivor list is the output of
`Radical.ofFlag_refinement_and_bounds_of_preceding_sources`; the partial
ClassicalRefinementCase predicate is never used to infer exhaustiveness.
Earlier geometry, the linear fixed-space input, 11.3.2 and Kz=K remain with
qt-d-1222-natural-local-geometry, qt-d-1222-shadow-linear-geometry,
qt-d-1222-shadow-component-triangle and qt-d-1222-shadow-component-comparison.
Their final discharge belongs to qt-d-1222-shadow-components. Generation
one and the R₁-Sylow construction remain with qt-d-1222-shadow-component-witness.

Source: Aschbacher--Smith A.3.6, pp.43--45; 11.1.2, pp.761--765;
11.4.1(2) and 11.4.3, pp.776--779.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1.Section02
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Models

/-- The structural classification and both kernel calculations, with their
inputs derived from the actual nonquasisimple component. -/
theorem nonquasisimple_outer_nilpotent
    {B : Type*} [Group B] [Finite B]
    (hC : (⊤ : Subgroup B).IsCComponent)
    (hQ : IsSQTK KnownSimple.IsKnownSimple B) (hO : pCore 2 B = ⊥)
    (hn : ¬ IsQuasisimple B) : Group.IsNilpotent (MulAut.Outer B) := by
  have hnc : ¬ fittingSubgroup (⊤ : Subgroup B) ≤ center (⊤ : Subgroup B) := by
    intro hf
    have hr : solvableRadical (⊤ : Subgroup B) = center (⊤ : Subgroup B) :=
      le_antisymm (solvableRadical_le_center_of_fitting_le_center hf)
        (le_solvableRadical _ inferInstance
          (Group.isSolvable_of_comm (fun a b => Subtype.ext
            (mem_center_iff.mp a.property b).symm)))
    let := hC.perfect
    let := hC.isSimpleGroup_quotient_solvableRadical
    let : IsQuasisimple (⊤ : Subgroup B) :=
      ⟨(QuotientGroup.quotientMulEquivOfEq hr).symm.isSimpleGroup⟩
    exact hn (IsQuasisimple.of_mulEquiv topEquiv)
  obtain ⟨hs, hc⟩ := ChapterA.Section03.NoncentralFitting.structure_of_noncentral hQ hO hC hnc
  let := hC.perfect
  have ht : Group.IsNilpotent (MulAut.Outer (⊤ : Subgroup B)) := by
    rcases hs with ha | ha
    · exact NaturalOdd.outer_nilpotent ha
    · exact NilpotentFive.outer_nilpotent (hQ.subgroup ⊤) ha hc
  let := ht
  exact Group.nilpotent_of_mulEquiv (MulAut.outerCongr topEquiv)

private theorem not_quasisimple_of_SL2_quotient
    {B F : Type*} [Group B] [Finite B] [Field F] [Finite F]
    (hcore : pCore 2 B = ⊥) (hF : (2 : F) ≠ 0)
    (f : B →* SL(2, F)) (hf : Function.Surjective f) : ¬ IsQuasisimple B := by
  intro hB
  let := hB
  have hne : (-1 : SL(2, F)) ≠ 1 := by
    intro he
    have ho := Matrix.SpecialLinearGroup.orderOf_neg_one_eq_two hF
    rw [he, orderOf_one] at ho
    norm_num at ho
  have hk : f.ker ≤ center B := by
    apply (IsQuasisimple.normal_le_center_or_eq_top f.ker).resolve_right
    intro ht
    obtain ⟨x, hx⟩ := hf (-1)
    have hxone : f x = 1 := MonoidHom.mem_ker.mp (ht.symm ▸ mem_top x)
    exact hne (hx.symm.trans hxone)
  have hm := f.map_pCore_of_central_kernel (p := 2) hf hk
  rw [hcore, Subgroup.map_bot] at hm
  let Z := zpowers (-1 : SL(2, F))
  have hz : Z ≤ center SL(2, F) := zpowers_le.mpr (mem_center_iff.mpr fun x => by simp)
  have hnormal : Z.Normal := ⟨fun x hx g => by
    rw [mem_center_iff.mp (hz hx) g]
    simpa only [mul_assoc, mul_inv_cancel, mul_one] using hx⟩
  have hp : IsPGroup 2 Z := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, Matrix.SpecialLinearGroup.orderOf_neg_one_eq_two hF, pow_one])
  have hle : Z ≤ pCore 2 SL(2, F) := le_sSup ⟨hnormal, hp⟩
  exact hne (mem_bot.mp (hm.symm ▸ hle (mem_zpowers _)))

/-- The odd-by-SL₂ source alternative supplies the full outer conclusion;
A.3.6's kernel shapes and actions are proved internally, including p = 5. -/
theorem oddSL2_outer_twoClosed
    {B : Type*} [Group B] [Finite B]
    (hC : (⊤ : Subgroup B).IsCComponent)
    (hQ : IsSQTK KnownSimple.IsKnownSimple B) (hO : pCore 2 B = ⊥)
    {p : ℕ} (_hp : p.Prime) (hodd : Odd p)
    (hm : Source.IsSL (B ⧸ pPrimeCore 2 B) 2 p) :
    ChapterE.IsTwoClosed (MulAut.Outer B) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  have htwo : (2 : F) ≠ 0 :=
    GorensteinWalter.two_ne_zero_of_odd_card F (hF ▸ hodd)
  have hn := not_quasisimple_of_SL2_quotient hO htwo
    (e.toMonoidHom.comp (QuotientGroup.mk' _))
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
  let := nonquasisimple_outer_nilpotent hC hQ hO hn
  exact ⟨Classical.arbitrary _, inferInstance⟩

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V}
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)

private theorem original_flag_quotient :
    Nonempty ((f.Li 0 ⧸ pCore 2 (f.Li 0)) ≃* Theory.PSL2.Group S.field.Carrier) := by
  obtain ⟨f₀, hu, _, hm, _⟩ := LocalGeometry.exists_unique_marked_flag D S c
  have he : f.Li 0 = f₀.Li 0 := congrArg
    (fun U => LocalGeometry.localResidual L (c.preimage U))
    (hu 0 _ (f.dimension 0) (f.invariant 0))
  rw [he]
  exact hm 0

private theorem ofFlag_quotient_inputs
    (h : Comparison.EarlierGeometry (ofFlag S f X z H)) :
    (⊤ : Subgroup ((ofFlag S f X z H).K ⧸ pCore 2 (ofFlag S f X z H).K)).IsCComponent ∧
      IsSQTK KnownSimple.IsKnownSimple
        ((ofFlag S f X z H).K ⧸ pCore 2 (ofFlag S f X z H).K) := by
  let K := (ofFlag S f X z H).K
  have ht : (⊤ : Subgroup K).IsCComponent := by
    have hh := h.line_component.2.subgroupOf le_rfl
    rw [subgroupOf_self] at hh
    have he := hh.map_equiv (subgroupOfEquivOfLe h.line_component.1)
    rwa [map_top_of_surjective _ (subgroupOfEquivOfLe h.line_component.1).surjective] at he
  let := pCore_isNilpotent (p := 2) (G := K)
  have hquot : (⊤ : Subgroup (K ⧸ pCore 2 K)).IsCComponent := by
    have hh := ht.map_quotient (pCore 2 K)
    rwa [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hh
  have hlocal : IsSQTK KnownSimple.IsKnownSimple K :=
    (IsSQTK.equiv (subgroupOfEquivOfLe h.line_component.1)).mp
      ((S.source.simpleQTKE.twoLocal_sqtk (f.normalizer_twoLocal 0)).subgroup
        (K.subgroupOf (ofFlag S f X z H).G₁))
  refine ⟨hquot, ⟨?_, hlocal.isKGroup.quotient _⟩⟩
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
    (hlocal.stronglyQuasithin p hp ho)

/-- Every row of the surviving 11.4.1(2) list has two-closed outer group.
The source survivor list remains an earlier geometry input, not an assertion
that the partial predicate itself proves exhaustive classification. -/
theorem ofFlag_surviving_outer_twoClosed
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (hs : Source.ClassicalRefinementCase L (f.Li 0) (ofFlag S f X z H).K 1 S.field.degree) :
    ChapterE.IsTwoClosed
      (MulAut.Outer ((ofFlag S f X z H).K ⧸ pCore 2 (ofFlag S f X z H).K)) := by
  cases hs with
  | equal he => exact ofFlag_equal_outer_twoClosed S f X z H he.symm (original_flag_quotient S f)
  | sl2Prime _ _ p hp he =>
    obtain ⟨hC, hQ⟩ := ofFlag_quotient_inputs S f X z H h
    have hprime : p.Prime := hp.elim (fun he => he ▸ (by decide)) And.left
    have ho : Odd p := hprime.odd_of_ne_two (by rcases hp with rfl | hp <;> omega)
    exact oddSL2_outer_twoClosed hC hQ (pCore_quotient_pCore_eq_bot 2) hprime ho he
  | psl2Prime _ _ p hp hlarge he _ =>
    exact ofFlag_prime_outer_twoClosed S f X z H hp hlarge he


/-- Both products of 11.4.3 from the surviving source list. The natural and
nilpotent kernel structures, two-closedness and fixed-space premise are discharged. -/
theorem ofFlag_surviving_products
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (hs : Source.ClassicalRefinementCase L (f.Li 0) (ofFlag S f X z H).K 1 S.field.degree)
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (ofFlag S f X z H).point J →
      Proposition1132At D S (ofFlag S f X z H).point J) :
    (∀ g ∈ Gz (ofFlag S f X z H),
      ∃ k ∈ (ofFlag S f X z H).K, ∃ y ∈ Yz (ofFlag S f X z H),
        ∃ m ∈ Mz (ofFlag S f X z H), g = k * y * m) ∧
    (∀ g ∈ (ofFlag S f X z H).G₁,
      ∃ k ∈ (ofFlag S f X z H).K, ∃ y ∈ (ofFlag S f X z H).Y,
        ∃ m ∈ (ofFlag S f X z H).M₁, g = k * y * m) := by
  have hf := (fixed_and_transitive D S _ hlinear h1132).1
  have ho := ofFlag_surviving_outer_twoClosed S f X z H h hs
  exact ⟨point_product _ h he hNT ho, line_product _ h (f.invariant 0) hf hNT ho⟩

/-- The literal H-star choice, with its two-residual alternative, for every
surviving source row and with no extra model action or outer-group premise. -/
theorem ofFlag_surviving_selected_H
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (hs : Source.ClassicalRefinementCase L (f.Li 0) (ofFlag S f X z H).K 1 S.field.degree)
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (h1132 : ∀ J, Hypothesis1131At D S (ofFlag S f X z H).point J →
      Proposition1132At D S (ofFlag S f X z H).point J) :
    ∃ J, J ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      J ≤ Gz (ofFlag S f X z H) ∧ SelectedResidualAlternative (ofFlag S f X z J) :=
  exists_selected_H _ h he hNT
    (ofFlag_surviving_outer_twoClosed S f X z H h hs) h1132

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Models
