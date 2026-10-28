module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.G2.SourceFlag
public import Theory.AtlasPort.LinearGroups.G2.HigherFieldResiduals

/-!
# Point and plane stabilizers in the nonbinary G₂ natural model

The octonion point and null-plane parabolics preserve their literal images in
trace-zero octonions modulo scalars. Each stabilizer is proper, as witnessed
by the other Weyl generator; maximality therefore identifies it exactly.
Conjugation transports the stabilizers with the original natural action.
The concrete solvable residuals and their PSL₂ quotients retain source order:
the source point group is ATLAS local₂, and the plane group is local₁.

Source: Aschbacher--Smith, opening §11.1, printed pp.760--761.
The octonion and root APIs are from the attributed ATLAS port; see
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff. No new ATLAS source is copied.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.G2.ResidualIncidence
open Atlas.G2 Atlas.G2.Natural Atlas.G2.Natural.OrthogonalCover
open Atlas.G2.Natural.OrthogonalCover.SylowFlag Atlas.G2.LieParabolicSetup
open Atlas.SplitOctonion Representation.BinaryOffender
variable (F : Type*) [Field F] [CharP F 2] [Algebra (ZMod 2) F]

def stabilizer (W : Submodule F (Space F)) : Subgroup (Model F) :=
  subspaceStabilizer (restrictScalars (k := ZMod 2) (Natural.action F))
    (W.restrictScalars (ZMod 2))

omit [Algebra (ZMod 2) F] in
private theorem point_invariant (g : Model F) (hg : g ∈ parabolic₂)
    (x : Space F) (hx : x ∈ N1 F) : Natural.action F g x ∈ N1 F := by
  rw [N1_eq_span, Submodule.mem_span_singleton] at hx ⊢
  obtain ⟨a,rfl⟩ := hx
  obtain ⟨b,hb⟩ := (mem_pointStabilizer_iff g).mp
    ((parabolic_eq_pointStabilizer (F := F)).le hg)
  refine ⟨a * (b : F), ?_⟩
  have he : traceZeroAction F g (pointVector F) = (b : F) • pointVector F := by
    apply Subtype.ext
    have hp : (pointVector F).val = (basisVector 0 : Carrier F) := by
      ext i
      fin_cases i <;> simp [pointVector, planeLift, basisVector]
    change g.val (pointVector F).val = (b : F) • (pointVector F).val
    rw [hp]
    exact hb
  rw [map_smul, action_mk, he, map_smul, SemigroupAction.mul_smul]

omit [Algebra (ZMod 2) F] in
private theorem plane_invariant (g : Model F) (hg : g ∈ parabolic₁)
    (x : Space F) (hx : x ∈ naturalPlane F) : Natural.action F g x ∈ naturalPlane F := by
  obtain ⟨_,⟨a,rfl⟩,rfl⟩ := hx
  have ha : (planeLift F a).val ∈ shortPlane := by
    intro i hi
    fin_cases i <;> simp_all [planeLift]
  have hb := (parabolic₁_le_shortPlaneStabilizer hg).1 _ ha
  refine ⟨traceZeroAction F g (planeLift F a), ?_, rfl⟩
  refine ⟨![(g.val (planeLift F a).val) 0, (g.val (planeLift F a).val) 1], ?_⟩
  apply Subtype.ext
  exact (shortPlane_coordinates hb).symm

omit [Algebra (ZMod 2) F] in
private theorem coord_action (g : Model F) (x : Space F) :
    coord F (Natural.action F g x) = Restricted.NaturalCoordinates.action F g (coord F x) :=
  LinearMap.congr_fun ((Restricted.NaturalCoordinates.repEquiv F).isIntertwining' g) x

theorem point_stabilizer : stabilizer F (N1 F) = parabolic₂ := by
  have hle : parabolic₂ ≤ stabilizer F (N1 F) :=
    le_subspaceStabilizer _ _ (point_invariant F)
  apply ((isCoatom_iff_ge_of_le.mp HigherFieldResiduals.parabolic₂_isCoatom).2 _ ?_ hle).antisymm hle
  intro ht
  have h := ((show (weylS : Model F) ∈ stabilizer F (N1 F) from ht.symm ▸ mem_top _) _).mpr
    (show (coord F).symm ![1,0,0,0,0,0] ∈ N1 F from
      (mem_N1 F _).mpr ⟨1, (coord F).apply_symm_apply _⟩)
  obtain ⟨a,ha⟩ := (mem_N1 F _).mp h
  change coord F (Natural.action F weylS ((coord F).symm ![1,0,0,0,0,0])) = _ at ha
  rw [coord_action, LinearEquiv.apply_symm_apply, Restricted.NaturalCoordinates.action_weylS] at ha
  have hh := congrFun ha 1
  exact one_ne_zero hh

theorem plane_stabilizer : stabilizer F (naturalPlane F) = parabolic₁ := by
  have hle : parabolic₁ ≤ stabilizer F (naturalPlane F) :=
    le_subspaceStabilizer _ _ (plane_invariant F)
  apply ((isCoatom_iff_ge_of_le.mp HigherFieldResiduals.parabolic₁_isCoatom).2 _ ?_ hle).antisymm hle
  intro ht
  have h := ((show (weylR : Model F) ∈ stabilizer F (naturalPlane F) from ht.symm ▸ mem_top _) _).mpr
    (show (coord F).symm ![0,1,0,0,0,0] ∈ naturalPlane F from
      (mem_naturalPlane F _).mpr ⟨0,1, (coord F).apply_symm_apply _⟩)
  obtain ⟨a,b,ha⟩ := (mem_naturalPlane F _).mp h
  change coord F (Natural.action F weylR ((coord F).symm ![0,1,0,0,0,0])) = _ at ha
  rw [coord_action, LinearEquiv.apply_symm_apply, Restricted.NaturalCoordinates.action_weylR] at ha
  have hh := congrFun ha 2
  exact one_ne_zero hh

/-- Transport by one actual actor, with the original conjugation orientation. -/
theorem stabilizer_map (g : Model F) (W : Submodule F (Space F)) :
    stabilizer F (W.map (Natural.action F g)) =
      (stabilizer F W).map (MulAut.conj g).toMonoidHom := by
  ext a
  rw [Subgroup.mem_map_equiv]
  change (∀ x, Natural.action F a x ∈ W.map (Natural.action F g) ↔
    x ∈ W.map (Natural.action F g)) ↔
      ∀ x, Natural.action F (g⁻¹ * a * g) x ∈ W ↔ x ∈ W
  have he (x : Space F) :
      Natural.action F a (Natural.action F g x) =
        Natural.action F g (Natural.action F (g⁻¹ * a * g) x) := by
    simp only [map_mul, Module.End.mul_apply, self_inv_apply]
  have hm (x : Space F) : Natural.action F g x ∈ W.map (Natural.action F g) ↔ x ∈ W :=
    by
      change x ∈ (W.map (Natural.action F g)).comap (Natural.action F g) ↔ x ∈ W
      rw [Submodule.comap_map_eq_of_injective ((Natural.action F).apply_bijective g).injective]
  constructor
  · intro h x
    simpa only [he, hm] using h (Natural.action F g x)
  · intro h x
    obtain ⟨y,rfl⟩ := ((Natural.action F).apply_bijective g).surjective x
    simpa only [he, hm] using h y


/-- Source order: point first, plane second. -/
def standardParabolic (i : Fin 2) : Subgroup (Model F) :=
  if i = 0 then parabolic₂ else parabolic₁

/-- The two concrete residuals, in source order. -/
def standardLocal (i : Fin 2) : Subgroup (Model F) :=
  if i = 0 then local₂ else local₁

omit [Algebra (ZMod 2) F] in
/-- The literal standard residual, before quotienting by its two-core. -/
theorem standard_residual [Finite F] (hq : 2 < Nat.card F) (i : Fin 2) :
    (solvableResidual (standardParabolic F i)).map (standardParabolic F i).subtype =
      standardLocal F i := by
  fin_cases i
  · exact HigherFieldResiduals.parabolic₂_residual hq
  · exact HigherFieldResiduals.parabolic₁_residual hq

open scoped MatrixGroups
/-- The standard quotients use this same defining field. -/
def standardCoreQuotientEquiv [Finite F] (i : Fin 2) :
    (standardLocal F i ⧸ pCore 2 (standardLocal F i)) ≃* PSL(2,F) := by
  classical
  by_cases hi : i = 0
  · subst i
    exact local₂CoreQuotientEquivPSL
  · have hi' : i = 1 := by omega
    subst i
    exact local₁CoreQuotientEquivPSL

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.G2.ResidualIncidence
