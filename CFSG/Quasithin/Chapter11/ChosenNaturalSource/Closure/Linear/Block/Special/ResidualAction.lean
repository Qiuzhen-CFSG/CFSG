module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Special.ResidualModel
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Sections
public import Theory.GroupTheory.NormalizedIntersectionImage

/-!
# The natural action of the original Chapter 11 residual

The literal star projection followed by the given SL₃ marking sends
N_L(V₁) onto the full point stabilizer. Functoriality of the finite
solvable residual identifies the image of the original E.L₁. The point
stabilizer calculation gives C_V(E.L₁)=V₁. Mutual normalization and
natural action differences put all of V in E.L₁, without identifying
this solvable residual with G.2's two-residual or assuming U≤L.

These are the two natural-action inputs to the closure-center argument
in ResidualConsequences, and hence the exceptional-K consumer.
Source: Aschbacher--Smith, 11.5.7, refs/quasithin.pdf, printed p.782.
-/

@[expose] public noncomputable section
open Subgroup Matrix
open scoped MatrixGroups
open Matrix.PSL3.PointRadicalGeneration
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterG.Section02.LinearThree
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Special
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D) {x y : G}
  (d : Hypothesis (setup E) E.input.field.Carrier E.input.field.degree x y)

/-- The original component map, with its star quotient kernel retained. -/
def componentModel : L →* SL(3,E.input.field.Carrier) :=
  d.model.toMonoidHom.comp (starProjection (setup E))

private theorem residual_image_map {A B : Type*} [Group A] [Group B] [Finite A]
    (f : A →* B) (P : Subgroup A) :
    residualIn (P.map f) = (residualIn P).map f := by
  have h := congrArg (map (P.map f).subtype)
    (map_solvableResidual_eq (f.subgroupMap P) (f.subgroupMap_surjective P))
  have he : (P.map f).subtype.comp (f.subgroupMap P) = f.comp P.subtype := rfl
  simpa only [residualIn, Subgroup.map_map, he] using h.symm

include d

/-- The original solvable residual maps onto the marked parabolic residual. -/
theorem original_residual_model :
    (E.L₁.subgroupOf L).map (componentModel E d) = residualIn (parabolic d.point) := by
  have hpre : ((parabolic d.point).comap (componentModel E d)).map L.subtype =
      L ⊓ E.G₁ := by
    ext l
    constructor
    · rintro ⟨l,hl,rfl⟩
      exact ⟨l.property, (d.model_mem_pointStabilizer_iff l).mp hl⟩
    · intro hl
      exact ⟨⟨l,hl.1⟩, (d.model_mem_pointStabilizer_iff ⟨l,hl.1⟩).mpr hl.2,rfl⟩
  change ((residualIn (L ⊓ E.G₁)).subgroupOf L).map _ = _
  rw [← hpre, residual_image_map, subgroupOf,
    comap_map_eq_self_of_injective L.subtype_injective]
  exact map_solvableResidual_comap (componentModel E d)
    (d.model.surjective.comp (starProjection_surjective (setup E))) _

private theorem field_card_four : 4 ≤ Nat.card E.input.field.Carrier := by
  rw [d.field_card]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) E.input.nonbinary

/-- The original solvable residual fixes exactly the original point on V. -/
theorem chosen_residual_fixed : V ⊓ centralizer (E.L₁ : Set G) = E.V₁ := by
  apply le_antisymm
  · intro v hv
    let vv : (setup E).V := ⟨v,hv.1⟩
    apply (d.point_mem vv).mpr
    apply (parabolic_residual_fixed (field_card_four E d) d.point d.point_dimension _).mp
    intro a ha
    obtain ⟨l,hl,rfl⟩ := (original_residual_model E d).ge ha
    change (d.model (starProjection (setup E) l)).val *ᵥ (d.coordinates vv).toAdd = _
    rw [← d.equivariant l vv]
    congr 2
    apply Subtype.ext
    change (l : G) * v * (l : G)⁻¹ = v
    rw [hv.2 l hl, mul_inv_cancel_right]
  · intro v hv
    refine ⟨E.V₁_le hv, ?_⟩
    intro l hl
    let ll : (setup E).L := ⟨l,E.L₁_le hl⟩
    let vv : (setup E).V := ⟨v,E.V₁_le hv⟩
    have hm : componentModel E d ll ∈ residualIn (parabolic d.point) :=
      (original_residual_model E d).le (mem_map_of_mem _ hl)
    have hh := (parabolic_residual_fixed (field_card_four E d) d.point d.point_dimension
      (d.coordinates vv).toAdd).mpr ((d.point_mem vv).mp hv) _ hm
    change (d.model (starProjection (setup E) ll)).val *ᵥ (d.coordinates vv).toAdd = _ at hh
    rw [← d.equivariant ll vv] at hh
    have he : l * v * l⁻¹ = v := congrArg Subtype.val (d.coordinates.injective hh)
    exact (mul_inv_eq_iff_eq_mul.mp he)

/-- Natural displacements from the original solvable residual retain all of V. -/
theorem chosen_le_residual : V ≤ E.L₁ := by
  have hJV : E.L₁ ≤ normalizer (V : Set G) :=
    E.L₁_le.trans (normalizes_of_span (setup E) d.span_eq)
  have hVJ : V ≤ normalizer (E.L₁ : Set G) := by
    have hVM : V ≤ L ⊓ E.G₁ := le_inf D.le_component
      (d.setup.V_le_T.trans d.setup.T_normalizes_point)
    exact hVM.trans ((L ⊓ E.G₁).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (solvableResidual _)))
  have hs := NormalizedIntersection.surjective_of_differences E.L₁ V hJV hVJ
    d.coordinates.toMonoidHom d.coordinates.surjective
    (fun l v => (componentModel E d ⟨l,E.L₁_le l.property⟩).val *ᵥ v)
    (fun l v => d.equivariant ⟨l,E.L₁_le l.property⟩ v) (by
      intro C hC
      apply parabolic_residual_full (field_card_four E d) d.point d.point_dimension C
      intro a ha v
      obtain ⟨l,hl,rfl⟩ := (original_residual_model E d).ge ha
      exact hC ⟨l,hl⟩ v)
  intro v hv
  obtain ⟨w,hw⟩ := hs (d.coordinates ⟨v,hv⟩)
  have he : (w : G) = v := congrArg Subtype.val (d.coordinates.injective hw)
  exact he ▸ w.property.1

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Special
