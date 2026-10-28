module
public import Theory.Representation.SL3.PointConstituents
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.LinearCentralizerSpan
public import Theory.GroupAction.SubgroupPerfectFixedCover

/-!
# Natural and dual constituents on the original cubic normalizer residual

For E = X₁ and L⁺ = N_{L₁}(E)^∞, coprime fixed-point lifting makes the
centralizer cover L₁/O₂(L₁). Perfectness preserves surjectivity on its
solvable residual. The normalizer of E inside L₁ already centralizes E:
its commutators with E lie both in E and the original two-core. This
identifies L⁺/O₂(L⁺) through the literal inclusion, and proves
O₂(L⁺) = L⁺ intersect O₂(L₁) and L₁ = L⁺ O₂(L₁).

The common Sylow alignment then supplies the original map V -> F², with
kernel exactly V₁. Its conjugation equation and the dual annihilator
embedding use the same lower-right SL₂ block. That block remains surjective
on L⁺ and has kernel exactly O₂(L⁺), so its natural plane is irreducible
among all additive subgroups. Finally L⁺ preserves the original C_U(E).

These results establish the marked local comparison for the natural and
dual three-space models. They do not assert that all chief factors in the
larger ambient two-group have those models, or choose a projective adjoint
extension of a restricted SL₃ action. The selected chief section and its
cubic-fixed lifts retain their original endpoints in LinearChiefFixed.
The ambient constituent comparison, extension selection, centralizer
exclusions, common-normal existence and both triangle orientations remain.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.1.2, printed pp.763--764, the L⁺ and chief-constituent comparison.
-/

open Subgroup Theory.GroupTheory Representation Matrix
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))

/-- The original cubic normalizer residual covers the original local
two-core quotient, with the actual inclusion and both two-cores retained. -/
theorem linear_point_cubic_residual_cover
    (f : InvariantFlag (.sl3 m)) {X : Subgroup G}
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 0) : Subgroup G) = 3) :
    let E := X ⊓ Closure.coreQuotientCentralizer (f.Li 0)
    let H := localResidual (f.Li 0) E
    H ≤ centralizer (E : Set G) ∧
    H.pCoreIn 2 = H ⊓ (f.Li 0).pCoreIn 2 ∧
    H ⊔ (f.Li 0).pCoreIn 2 = f.Li 0 ∧
    ∃ e : (H ⧸ pCore 2 H) ≃* (f.Li 0 ⧸ pCore 2 (f.Li 0)),
      ∀ h : H, e (QuotientGroup.mk' (pCore 2 H) h) =
        QuotientGroup.mk' (pCore 2 (f.Li 0))
          (inclusion (show H ≤ f.Li 0 from (localResidual_le E).trans inf_le_left) h) := by
  intro E H
  let A := f.Li 0
  let N := A ⊓ normalizer (E : Set G)
  let _ : Group.IsPerfect A := localResidual_perfect _
  have hE : IsPGroup 3 E := IsPGroup.of_card (n := 1) (by simpa only [E,pow_one] using hcard)
  have hEA : E ≤ normalizer (A : Set G) := by
    intro x hx
    obtain ⟨a,_,rfl⟩ := hx.2
    exact a.property
  have hm : ⁅A,E⁆ ≤ (pCore 2 A).map A.subtype := by
    rw [commutator_comm]
    exact commutator_le.mpr fun x hx a ha => Closure.coreQuotientCentralizer_commutator hx.2 ha
  have hcop : Nat.Coprime (Nat.card E) (Nat.card (pCore 2 A)) :=
    IsPGroup.coprime_card_of_ne 3 2 (by decide) E (pCore 2 A) hE pCore_isPGroup
  have hNC : N ≤ centralizer (E : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply bot_unique
    have he : ⁅N,E⁆ ≤ E := le_normalizer_iff_commutator_le_right.mp inf_le_right
    have hn : ⁅N,E⁆ ≤ A.pCoreIn 2 := (commutator_mono inf_le_left le_rfl).trans hm
    exact (le_inf he hn).trans
      (hE.disjoint_of_coprime (isPGroup_pCoreIn 2 A) (by decide)).le_bot
  let q := QuotientGroup.mk' (pCore 2 A)
  let n : N →* A ⧸ pCore 2 A := q.comp (inclusion inf_le_left)
  have hn : Function.Surjective n := by
    have hc := centralizer_quotient_surjective_of_solvable_coprime A E (pCore 2 A) hEA
      (by let : Group.IsNilpotent (pCore 2 A) := pCore_isNilpotent; infer_instance) hcop hm
    intro w
    obtain ⟨a,ha⟩ := hc w
    exact ⟨⟨a, a.property.1, Subgroup.centralizer_le_normalizer _ a.property.2⟩,ha⟩
  have hr : (solvableResidual N).map n = ⊤ := by
    rw [map_solvableResidual_eq n hn,solvableResidual_eq_top]
  have hHA : H ≤ A := (localResidual_le E).trans inf_le_left
  let r := q.comp (inclusion hHA)
  have hs : Function.Surjective r := by
    intro w
    obtain ⟨a,ha,haw⟩ := hr.ge (mem_top w)
    exact ⟨⟨a,mem_map_of_mem N.subtype ha⟩,haw⟩
  have hk : IsPGroup 2 r.ker := by
    dsimp only [r,q]
    rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)
  have hker : r.ker = pCore 2 H := by
    have hh := r.comap_pCore_of_ker_isPGroup hs hk
    rw [pCore_quotient_pCore_eq_bot] at hh
    exact hh
  refine ⟨(localResidual_le E).trans hNC,?_,?_,?_⟩
  · change (pCore 2 H).map H.subtype = H ⊓ A.pCoreIn 2
    rw [←hker]
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨a.property,⟨inclusion hHA a,(QuotientGroup.eq_one_iff _).mp ha,rfl⟩⟩
    · rintro ⟨hx,a,ha,rfl⟩
      exact ⟨⟨a,hx⟩,(QuotientGroup.eq_one_iff _).mpr ha,rfl⟩
  · have hmap : (H.subgroupOf A).map q = ⊤ := by
      apply top_unique
      intro w _
      obtain ⟨a,rfl⟩ := hs w
      exact mem_map_of_mem q a.property
    have hh := congrArg (comap q) hmap
    rw [comap_map_eq,QuotientGroup.ker_mk',comap_top] at hh
    have hh := congrArg (map A.subtype) hh
    change H ⊔ (pCore 2 A).map A.subtype = A
    simpa only [Subgroup.map_sup,map_subgroupOf_eq_of_le hHA,
      ←MonoidHom.range_eq_map,range_subtype] using hh
  · exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective r hs),fun _ => rfl⟩
open SL3 SL3.PlaneAction SL3.RadicalAction
open scoped MatrixGroups

/-- The first residual's natural quotient map, using the common flag alignment. -/
def pointConstituentProjection : (flag D S m).Li 0 →* Matrix.SpecialLinearGroup (Fin 2) S.field.Carrier :=
  (SL3PointConstituents.pointProjection S.field.Carrier).comp (localProjection D S m 0)

theorem pointConstituentProjection_surjective : Function.Surjective (pointConstituentProjection D S m) :=
  (SL3PointConstituents.pointProjection_surjective S.field.Carrier).comp
    (localProjection_surjective D S m 0)

theorem pointConstituentProjection_ker :
    (pointConstituentProjection D S m).ker = pCore 2 ((flag D S m).Li 0) := by
  have hc := (localProjection D S m 0).comap_pCore_of_ker_isPGroup
    (localProjection_surjective D S m 0) (localProjection_ker_isTwoGroup D S m 0)
  rw [←hc]
  change _ = (pCore 2 (Matrix.PSL3.LinearThree.pointLocalSL S.field.Carrier)).comap _
  rw [←SL3PointConstituents.pointProjection_ker]
  rfl

/-- The actual V/V₁ projection before quotienting, with no choice of complement. -/
def pointConstituentMap : V →* Multiplicative (Fin 2 → S.field.Carrier) :=
  (SL3PointConstituents.tail S.field.Carrier).toAddMonoidHom.toMultiplicative.comp
    (vectorEquiv D S m).toMonoidHom

theorem pointConstituentMap_surjective : Function.Surjective (pointConstituentMap D S m) :=
  (SL3PointConstituents.tail_surjective S.field.Carrier).comp (vectorEquiv D S m).surjective

theorem pointConstituentMap_ker :
    (pointConstituentMap D S m).ker = ((flag D S m).Vi 0).subgroupOf V := by
  ext v
  change SL3PointConstituents.tail S.field.Carrier (vectorEquiv D S m v).toAdd = 0 ↔
    (v : G) ∈ (flag D S m).Vi 0
  have hv : (v : G) ∈ (flag D S m).Vi 0 ↔
      (vectorEquiv D S m v).toAdd 1 = 0 ∧ (vectorEquiv D S m v).toAdd 2 = 0 :=
    ((SL3.coordinates D S m).mem_preimage ((flag D S m).space 0) v).trans
      (mem_flagFor_iff (alignment D S m) 0 ((SL3.coordinates D S m).projection v).toAdd)
  refine Iff.trans ?_ hv.symm
  constructor
  · intro h
    exact ⟨congrFun h 0,congrFun h 1⟩
  · rintro ⟨h1,h2⟩
    ext i
    fin_cases i <;> simp [SL3PointConstituents.tail,h1,h2]

theorem pointConstituentMap_action (l : (flag D S m).Li 0) (v : V) :
    pointConstituentMap D S m (V.normalizerMonoidHom
      (inclusion D.normalizes ⟨l,(localResidual_le _ l.property).1⟩) v) =
    Matrix.SL2.naturalAction S.field.Carrier (pointConstituentProjection D S m l)
      (pointConstituentMap D S m v) := by
  have he := alignedAction_projection D S m
    (inclusion le_sup_left (⟨l,(localResidual_le _ l.property).1⟩ : L)) v
  rw [alignedAction_component,←localProjection_coe] at he
  apply Multiplicative.toAdd.injective
  exact (congrArg (SL3PointConstituents.tail S.field.Carrier) he).trans
    (SL3PointConstituents.natural_quotient S.field.Carrier
      (localProjection D S m 0 l) (vectorEquiv D S m v).toAdd)

/-- The dual constituent uses the same SL₂ marking as the original natural quotient. -/
theorem pointConstituent_dual_action (l : (flag D S m).Li 0)
    (w : Fin 2 → S.field.Carrier) :
    (alignedQuotient D S m ⟨l,(localResidual_le _ l.property).1⟩)⁻¹.val.transpose *ᵥ
        SL3PointConstituents.dualEmbedding S.field.Carrier w =
      SL3PointConstituents.dualEmbedding S.field.Carrier
        ((pointConstituentProjection D S m l).val *ᵥ w) := by
  rw [←localProjection_coe D S m 0 l]
  exact SL3PointConstituents.dual_submodule S.field.Carrier (localProjection D S m 0 l) w

/-- The original L⁺ still realizes every natural and dual-plane operator. -/
theorem linear_point_cubic_constituent_surjective {X : Subgroup G}
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer ((flag D S m).Li 0) : Subgroup G) = 3) :
    let E := X ⊓ Closure.coreQuotientCentralizer ((flag D S m).Li 0)
    let H := localResidual ((flag D S m).Li 0) E
    Function.Surjective ((pointConstituentProjection D S m).comp
      (inclusion (show H ≤ (flag D S m).Li 0 from (localResidual_le E).trans inf_le_left))) := by
  intro E H
  let A := (flag D S m).Li 0
  let p := pointConstituentProjection D S m
  let q := QuotientGroup.mk' (pCore 2 A)
  let pbar := QuotientGroup.lift (pCore 2 A) p (pointConstituentProjection_ker D S m).ge
  obtain ⟨_,_,_,e,he⟩ := linear_point_cubic_residual_cover D S m (flag D S m) hcard
  intro w
  obtain ⟨a,ha⟩ := pointConstituentProjection_surjective D S m w
  obtain ⟨b,hb⟩ := e.surjective (q a)
  obtain ⟨h,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) b
  refine ⟨h,?_⟩
  have hh := congrArg pbar ((he h).symm.trans hb)
  exact hh.trans ha

/-- On the literal cubic normalizer residual, the common plane is still
irreducible as an elementary abelian group. -/
theorem linear_point_cubic_constituent_irreducible {X : Subgroup G}
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer ((flag D S m).Li 0) : Subgroup G) = 3) :
    let E := X ⊓ Closure.coreQuotientCentralizer ((flag D S m).Li 0)
    let H := localResidual ((flag D S m).Li 0) E
    let p := (pointConstituentProjection D S m).comp
      (inclusion (show H ≤ (flag D S m).Li 0 from (localResidual_le E).trans inf_le_left))
    ∀ W : Subgroup (Multiplicative (Fin 2 → S.field.Carrier)),
      (∀ h w, w ∈ W → Matrix.SL2.naturalAction S.field.Carrier (p h) w ∈ W) →
      W = ⊥ ∨ W = ⊤ := by
  intro E H p W hW
  exact SL3PointConstituents.natural_irreducible S.field.Carrier p
    (linear_point_cubic_constituent_surjective D S m hcard) W hW

/-- Normality of the exact point denominator is witnessed by the actual
natural quotient map. -/
theorem pointConstituentPoint_normal : (((flag D S m).Vi 0).subgroupOf V).Normal := by
  rw [←pointConstituentMap_ker D S m]
  infer_instance

/-- The original quotient V/V₁, retaining the quotient projection. -/
def pointConstituentQuotientEquiv [(((flag D S m).Vi 0).subgroupOf V).Normal] :
    (V ⧸ ((flag D S m).Vi 0).subgroupOf V) ≃* Multiplicative (Fin 2 → S.field.Carrier) :=
  (QuotientGroup.quotientMulEquivOfEq (pointConstituentMap_ker D S m).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (pointConstituentMap D S m)
      (pointConstituentMap_surjective D S m))

theorem pointConstituentQuotientEquiv_mk [(((flag D S m).Vi 0).subgroupOf V).Normal]
    (v : V) :
    pointConstituentQuotientEquiv D S m
      (QuotientGroup.mk' (((flag D S m).Vi 0).subgroupOf V) v) =
        pointConstituentMap D S m v := rfl

/-- The quotient map of L⁺ has precisely its own two-core as kernel. -/
theorem linear_point_cubic_constituent_kernel {X : Subgroup G}
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer ((flag D S m).Li 0) : Subgroup G) = 3) :
    let E := X ⊓ Closure.coreQuotientCentralizer ((flag D S m).Li 0)
    let H := localResidual ((flag D S m).Li 0) E
    let p := (pointConstituentProjection D S m).comp
      (inclusion (show H ≤ (flag D S m).Li 0 from (localResidual_le E).trans inf_le_left))
    p.ker = pCore 2 H := by
  intro E H p
  have hk : IsPGroup 2 p.ker := by
    dsimp only [p]
    rw [←MonoidHom.comap_ker,pointConstituentProjection_ker]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)
  have hh := p.comap_pCore_of_ker_isPGroup
    (linear_point_cubic_constituent_surjective D S m hcard) hk
  rw [Matrix.SL2.twoCore_eq_bot] at hh
  exact hh

/-- The same original cubic normalizer residual preserves the original cubic
fixed subgroup of U, so these local constituent maps apply to its action. -/
theorem linear_point_cubic_fixed_normalized
    (f : InvariantFlag (.sl3 m))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G)) {X : Subgroup G}
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 0) : Subgroup G) = 3) :
    let E := X ⊓ Closure.coreQuotientCentralizer (f.Li 0)
    let U := conjugateSpanBy V (centralizer (f.Vi 0 : Set G))
    localResidual (f.Li 0) E ≤ normalizer (U ⊓ centralizer (E : Set G) : Set G) := by
  intro E U
  have hHU := ((localResidual_le E).trans inf_le_left |>.trans hfix).trans
    (le_normalizer_conjugateSpanBy V (centralizer (f.Vi 0 : Set G)))
  have hHC := (linear_point_cubic_residual_cover D S m f hcard).1
  change localResidual (f.Li 0) E ≤ normalizer ((U ⊓ centralizer (E : Set G) : Subgroup G) : Set G)
  apply le_normalizer_iff.mpr
  intro h hh u hu
  exact ⟨le_normalizer_iff.mp hHU h hh u hu.1,
    le_normalizer_iff.mp ((centralizer (E : Set G)).le_normalizer) h (hHC hh) u hu.2⟩

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
