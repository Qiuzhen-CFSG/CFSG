module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.Cardinalities
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Transport

/-!
# The original vector and field-line residuals

A line stabilizer acts on its field line by scalars. The scalar character has
abelian image, so its solvable residual fixes the line pointwise. When C_V(L)=1,
the actual coordinate projection is injective; the line-normalizer residual
therefore centralizes each original vector on that line. Conversely a vector
fixer preserves its field span. Perfectness of the finite solvable residual
then identifies the two residuals in the original ambient group.

The marked-flag application proves pointResidual L z = L₁ for both surviving
natural actions, including SL₃(4) and its full center. No uniqueness or model
parabolic calculation is required for this equality. The residual-image lemma
retains the original quotient map and the supplied action isomorphism.
Source: Aschbacher--Smith, 11.5.2--3, printed p.779.
-/

open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.PointModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {F : CFSG.Quasithin.ChapterB.QuasisimpleSource.BinaryField}

/-- With no fixed vectors, the original coordinate projection is injective. -/
theorem projection_injective (c : Coordinates D F) (hfixed : V ⊓ centralizer (L : Set G) = ⊥) :
    Function.Injective c.projection := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro v hv
  apply mem_bot.mpr
  apply Subtype.ext
  apply mem_bot.mp
  rw [← hfixed]
  exact ⟨v.property, (c.projection_eq_one_iff v).mp hv⟩

variable (c : Coordinates D F) (U : Submodule F.Carrier c.Space)
    (hU : Module.finrank F.Carrier U = 1) (w : c.Space) (hw : w ∈ U) (hw0 : w ≠ 0)

include hU hw hw0 in
private theorem scalar_exists (g : c.modelStabilizer U) :
    ∃ a : F.Carrier, a • w = c.modelAction g.val w := by
  apply Submodule.mem_span_singleton.mp
  rw [← eq_span_singleton_of_mem_of_finrank_eq_one hU hw hw0]
  exact (g.property w).mpr hw

private def lineScalar : c.modelStabilizer U →* F.Carrier where
  toFun g := (scalar_exists c U hU w hw hw0 g).choose
  map_one' := by
    apply smul_left_injective F.Carrier hw0
    exact (scalar_exists c U hU w hw hw0 1).choose_spec.trans (by simp)
  map_mul' g h := by
    apply smul_left_injective F.Carrier hw0
    dsimp only
    let a := (scalar_exists c U hU w hw hw0 g).choose
    let b := (scalar_exists c U hU w hw hw0 h).choose
    calc
      _ = c.modelAction (g.val * h.val) w :=
        (scalar_exists c U hU w hw hw0 (g * h)).choose_spec
      _ = c.modelAction g.val (c.modelAction h.val w) := by
        rw [map_mul, Module.End.mul_apply]
      _ = c.modelAction g.val (b • w) := congrArg (c.modelAction g.val)
        (scalar_exists c U hU w hw hw0 h).choose_spec.symm
      _ = b • c.modelAction g.val w := map_smul _ _ _
      _ = b • (a • w) := congrArg (b • ·)
        (scalar_exists c U hU w hw hw0 g).choose_spec.symm
      _ = (a * b) • w := by rw [smul_smul, mul_comm]

include hU hw hw0 in
/-- The marked line residual acts trivially on each nonzero vector of the line. -/
theorem model_residual_fixes_line (g : solvableResidual (c.modelStabilizer U)) :
    c.modelAction g.val.val w = w := by
  let f := (lineScalar c U hU w hw hw0).toHomUnits
  have hh := map_solvableResidual_le f (mem_map_of_mem f g.property)
  rw [solvableResidual_eq_bot, mem_bot] at hh
  have hs : lineScalar c U hU w hw hw0 g.val = 1 :=
    congrArg (fun a : F.Carrierˣ => (a : F.Carrier)) hh
  have he := (scalar_exists c U hU w hw hw0 g.val).choose_spec
  change lineScalar c U hU w hw hw0 g.val • w = _ at he
  rwa [hs, one_smul, eq_comm] at he

include hU in
/-- The literal point and field-line residuals coincide inside G. -/
theorem pointResidual_eq_localResidual
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (z : V) (hz : (c.projection z).toAdd ∈ U) (hz1 : z ≠ 1) :
    pointResidual L z.val = localResidual L (c.preimage U) := by
  let w := (c.projection z).toAdd
  have hw0 : w ≠ 0 := by
    intro he
    apply hz1
    apply projection_injective c hfixed
    exact he.trans (map_one c.projection).symm
  have hspan : U = Submodule.span F.Carrier {w} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hU hz hw0
  have hCL : L ⊓ centralizer ({z.val} : Set G) ≤
      L ⊓ normalizer (c.preimage U : Set G) := by
    rintro l ⟨hl, hc⟩
    refine ⟨hl, (c.mem_normalizer_preimage_iff U ⟨l, hl⟩).mpr ?_⟩
    have he : V.normalizerMonoidHom (inclusion D.normalizes ⟨l, hl⟩) z = z := by
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hc)
    have hf : c.modelAction (c.quotientMap ⟨l, hl⟩) w = w := by
      rw [← c.projection_component_conjugation, he]
    intro x
    rw [hspan, Submodule.mem_span_singleton, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨a, ?_⟩
      have hh : c.modelAction (c.quotientMap ⟨l, hl⟩) (a • w) =
          c.modelAction (c.quotientMap ⟨l, hl⟩) x := by rw [map_smul, hf, ha]
      have hi := congrArg (c.modelAction (c.quotientMap ⟨l, hl⟩)⁻¹) hh
      simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
        map_one, Module.End.one_apply] using hi
    · rintro ⟨a, rfl⟩
      exact ⟨a, by rw [map_smul, hf]⟩
  apply le_antisymm (map_solvableResidual_mono hCL)
  change localResidual L (c.preimage U) ≤ _
  let := localResidual_perfect (L := L) (c.preimage U)
  apply le_map_solvableResidual_of_isPerfect
  intro x hx
  refine ⟨(localResidual_le _ hx).1, ?_⟩
  have hmodel := model_residual_fixes_line c U hU w hz hw0
    (c.residualProjection U ⟨x, hx⟩)
  rw [c.residualProjection_coe] at hmodel
  have he : V.normalizerMonoidHom
      (inclusion D.normalizes ⟨x, (localResidual_le _ hx).1⟩) z = z := by
    apply projection_injective c hfixed
    apply Multiplicative.toAdd.injective
    rw [c.projection_component_conjugation]
    exact hmodel
  apply mem_centralizer_singleton_iff.mpr
  exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val he)

/-- The residual image uses the literal L/O₂(L) marking. -/
theorem model_residual_image (c : Coordinates D F) (U : Submodule F.Carrier c.Space) :
    ((localResidual L (c.preimage U)).subgroupOf L).map c.quotientMap =
      residualIn (c.modelStabilizer U) := by
  ext g
  constructor
  · rintro ⟨l, hl, rfl⟩
    let r := c.residualProjection U ⟨l.val, hl⟩
    refine ⟨r.val, r.property, ?_⟩
    exact c.residualProjection_coe U ⟨l.val, hl⟩
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨x, hx⟩ := c.residualProjection_surjective U ⟨r, hr⟩
    refine ⟨⟨x.val, (localResidual_le _ x.property).1⟩, x.property, ?_⟩
    exact (c.residualProjection_coe U x).symm.trans
      (congrArg (fun t : solvableResidual (c.modelStabilizer U) => t.val.val) hx)

/-- The marked source point discharges the residual-identification premise of
`intersection_and_rank_of_quotient`, without any extra model hypothesis. -/
theorem pointResidual_eq {E : Geometry D} (F₀ : MarkedFlag E)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hz : E.z ∈ E.V₁) (hz1 : E.z ≠ 1) :
    pointResidual L E.z = E.L₁ := by
  let c := F₀.action.coordinates
  have hline : E.V₁ = c.preimage (F₀.flag.space 0) := by
    change D.centralQuotientPreimage E.point = _
    rw [F₀.point_eq]
    rfl
  change pointResidual L E.z = localResidual L E.V₁
  rw [hline]
  exact pointResidual_eq_localResidual c _ (F₀.flag.dimension 0) hfixed
    ⟨E.z, E.V₁_le hz⟩ ((c.mem_preimage _ _).mp (hline ▸ hz))
    (fun he => hz1 (congrArg Subtype.val he))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.PointModels
