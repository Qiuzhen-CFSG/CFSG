module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.SL3.Natural
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.SL3.Quotients
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.ParabolicResiduals
public import Theory.GroupTheory.PCoreInRestriction
public import Theory.SpecificGroups.PSL3.PointRadicalGeneration.ParabolicCore

/-!
# The literal SL₃ point core and its fixed line

The original local residual maps onto the residual of its marked parabolic.
A conjugator for the caller's actual field line identifies that image with
the standard point local. The projection kernel is a two-group, so the same
map identifies their two-cores. Two explicit root matrices force the fixed
vectors onto the original point. The proved vanishing of C_V(L) lifts
fixedness through the original coordinate projection.

Source: Aschbacher–Smith 11.1.5, printed pp.765–766, using the flag of
pp.760–761 and the degree-three local calculations of F.1.12.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Matrix
open scoped MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.PointGeometry.SL3Core
open LocalGeometry Matrix.PSL3.PointRadicalGeneration
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
  (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))

private def residualIn (A : Subgroup SL(3,S.field.Carrier)) :=
  (solvableResidual A).map A.subtype

private theorem residualIn_map (A : Subgroup SL(3,S.field.Carrier))
    (e : MulAut SL(3,S.field.Carrier)) :
    (residualIn D S A).map e.toMonoidHom = residualIn D S (A.map e.toMonoidHom) := by
  let j := e.subgroupMap A
  have hm := congrArg (Subgroup.map (A.map e.toMonoidHom).subtype)
    (map_solvableResidual_eq j.toMonoidHom j.surjective)
  have hc : (A.map e.toMonoidHom).subtype.comp j.toMonoidHom =
      e.toMonoidHom.comp A.subtype := rfl
  change ((solvableResidual A).map j.toMonoidHom).map (A.map e.toMonoidHom).subtype =
    (solvableResidual (A.map e.toMonoidHom)).map (A.map e.toMonoidHom).subtype at hm
  change ((solvableResidual A).map A.subtype).map e.toMonoidHom = _
  rw [Subgroup.map_map,hc] at hm
  rw [Subgroup.map_map]
  exact hm

/-- The original component projection through its supplied natural marking. -/
def componentMap : L →* SL(3, S.field.Carrier) :=
  (Coordinates.sl3 m).quotientMap

/-- Image of an ambient subgroup under the literal component projection. -/
def componentImage (A : Subgroup G) : Subgroup SL(3, S.field.Carrier) :=
  (A.subgroupOf L).map (componentMap D S m)

/-- The marked component projection has the original two-core as its kernel. -/
theorem componentMap_ker : (componentMap D S m).ker = pCore 2 L := by
  ext l
  change m.groupEquiv (QuotientGroup.mk' (pCore 2 L) l) = 1 ↔ l ∈ pCore 2 L
  rw [← m.groupEquiv.map_one, m.groupEquiv.injective.eq_iff]
  exact QuotientGroup.eq_one_iff l

/-- The two-group projection kernel preserves the actual local two-core image. -/
theorem componentImage_core (A : Subgroup G) (hA : A ≤ L) :
    componentImage D S m (A.pCoreIn 2) = (componentImage D S m A).pCoreIn 2 := by
  have hk : IsPGroup 2 (componentMap D S m).ker := by
    rw [componentMap_ker]; exact pCore_isPGroup
  change ((A.pCoreIn 2).subgroupOf L).map _ = _
  rw [← pCoreIn_subgroupOf 2 A L hA]
  exact map_pCoreIn_of_ker_isPGroup _ hk _

private theorem residual_image (P : Submodule S.field.Carrier
    (Fin 3 → S.field.Carrier)) :
    componentImage D S m (localResidual L ((Coordinates.sl3 m).preimage P)) =
      residualIn D S ((Coordinates.sl3 m).modelStabilizer P) := by
  let c := Coordinates.sl3 m
  ext x
  constructor
  · rintro ⟨l,hl,rfl⟩
    let y : localResidual L (c.preimage P) := ⟨l,hl⟩
    refine ⟨(c.residualProjection P y).val,(c.residualProjection P y).property,?_⟩
    exact c.residualProjection_coe P y
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨y,hy⟩ := (c.residualProjection_surjective P) ⟨x,hx⟩
    refine ⟨⟨y,(localResidual_le _ y.property).1⟩,y.property,?_⟩
    exact (c.residualProjection_coe P y).symm.trans (congrArg (fun z => z.val.val) hy)

private theorem modelStabilizer_eq (P : Submodule S.field.Carrier
    (Fin 3 → S.field.Carrier)) :
    (Coordinates.sl3 m).modelStabilizer P = parabolic P := by
  ext a
  change (∀ x, a.val *ᵥ x ∈ P ↔ x ∈ P) ↔ a ∈ parabolic P
  exact (@MulAction.mem_stabilizer_set SL(3,S.field.Carrier)
    (Fin 3 → S.field.Carrier) _ _ a (P : Set _)).symm

/-- The chosen solvable residual maps onto the genuine point-parabolic residual. -/
private theorem componentImage_residual
    (f : InvariantFlag (Coordinates.sl3 m)) :
    componentImage D S m (f.Li 0) = residualIn D S (parabolic (f.space 0)) := by
  change componentImage D S m (localResidual L ((Coordinates.sl3 m).preimage (f.space 0))) = _
  rw [residual_image, modelStabilizer_eq]

/-- A genuine coordinate change identifies the original residual with the
standard vector stabilizer. This retains the solvable residual convention. -/
theorem componentImage_residual_conjugate
    (f : InvariantFlag (Coordinates.sl3 m))
    (a : SL(3, S.field.Carrier))
    (ha : conjugatePoint standardPoint a = f.space 0) :
    componentImage D S m (f.Li 0) =
      (Matrix.PSL3.LinearThree.pointLocalSL S.field.Carrier).map
        (MulAut.conj a⁻¹).toMonoidHom := by
  rw [componentImage_residual D S m f, ← ha, ← parabolic_conjugate]
  calc
    _ = (residualIn D S (parabolic standardPoint)).map (MulAut.conj a⁻¹).toMonoidHom :=
      (residualIn_map D S (parabolic standardPoint) (MulAut.conj a⁻¹)).symm
    _ = _ := ?_
  rw [parabolic_standardPoint]
  apply congrArg (Subgroup.map (MulAut.conj a⁻¹).toMonoidHom)
  apply Matrix.PSL3.LinearThree.ParabolicResiduals.pointParabolicSL_residual
  rw [S.field.card_eq]
  change 2 ^ 2 ≤ 2 ^ S.field.degree
  exact Nat.pow_le_pow_right (by decide : 0 < 2) S.nonbinary

open Matrix.PSL3.LinearThree Matrix.PSL3Even.UnipotentGeometry

private theorem standard_core_fixed (x : Fin 3 → S.field.Carrier) :
    (∀ g ∈ (pointLocalSL S.field.Carrier).pCoreIn 2, g.val *ᵥ x = x) ↔
      x ∈ standardPoint := by
  constructor
  · intro hx
    have hr (a c : S.field.Carrier) : specialLinear S.field.Carrier ⟨a,0,c⟩ ∈
        (pointLocalSL S.field.Carrier).pCoreIn 2 := by
      let u := specialLinear S.field.Carrier ⟨a,0,c⟩
      have hu : u ∈ pointLocalSL S.field.Carrier :=
        (mem_pointLocalSL_iff _ _).mpr ⟨rfl,rfl,rfl⟩
      refine ⟨⟨u,hu⟩,?_,rfl⟩
      rw [pointLocalSL_twoCore_eq]
      exact (mem_pointRadicalSL_iff _ _).mpr ⟨rfl,rfl,rfl,rfl⟩
    have h1 := congrFun (hx _ (hr 1 0)) 0
    have h2 := congrFun (hx _ (hr 0 1)) 0
    change (matrix S.field.Carrier ⟨1,0,0⟩ *ᵥ x) 0 = x 0 at h1
    change (matrix S.field.Carrier ⟨0,0,1⟩ *ᵥ x) 0 = x 0 at h2
    apply (mem_standardPoint _).mpr
    simpa [matrix,mulVec,dotProduct,Fin.sum_univ_three] using And.intro h1 h2
  · intro hx g hg
    obtain ⟨u,hu,rfl⟩ := hg
    obtain ⟨h00,h10,h20⟩ := (mem_pointLocalSL_iff _ u.val).mp u.property
    obtain ⟨h1,h2⟩ := (mem_standardPoint _).mp hx
    ext i
    fin_cases i <;> simp [mulVec,dotProduct,Fin.sum_univ_three,h1,h2,h00,h10,h20]

/-- The marked local two-core fixes exactly the caller's original field line. -/
theorem model_core_fixed_iff (f : InvariantFlag (Coordinates.sl3 m))
    (x : Fin 3 → S.field.Carrier) :
    (∀ g ∈ componentImage D S m ((f.Li 0).pCoreIn 2), g.val *ᵥ x = x) ↔ x ∈ f.space 0 := by
  obtain ⟨a,ha⟩ := exists_standardPoint_conjugator (f.space 0) (f.dimension 0)
  rw [componentImage_core D S m (f.Li 0) ((localResidual_le _).trans inf_le_left),
    componentImage_residual_conjugate D S m f a ha,
    ←map_pCoreIn_of_injective 2 _ _ (MulAut.conj a⁻¹).injective,←ha,mem_conjugatePoint,
    ←standard_core_fixed D S]
  let ρ := specialLinearNatural (k := S.field.Carrier) 3
  change (∀ g ∈ _, ρ g x = x) ↔ ∀ g ∈ _, ρ g (ρ a x) = ρ a x
  constructor
  · intro hx g hg
    have hh := hx (a⁻¹*g*a) ⟨g,hg,by simp⟩
    rw [map_mul,map_mul,Module.End.mul_apply,Module.End.mul_apply] at hh
    have he := congrArg (fun w => ρ a w) hh
    rw [Representation.self_inv_apply] at he
    exact he
  · rintro hx _ ⟨g,hg,rfl⟩
    change ρ (a⁻¹*g*a⁻¹⁻¹) x = x
    rw [inv_inv,map_mul,map_mul,Module.End.mul_apply,Module.End.mul_apply,
      hx g hg,Representation.inv_self_apply]

/-- Fixedness lifts through the original SL₃ projection, whose kernel has been proved trivial. -/
theorem projection_fixed_iff (l : L) (v : V) :
    (Coordinates.sl3 m).modelAction ((Coordinates.sl3 m).quotientMap l)
        ((Coordinates.sl3 m).projection v).toAdd = ((Coordinates.sl3 m).projection v).toAdd ↔
      V.normalizerMonoidHom (inclusion D.normalizes l) v = v := by
  rw [←(Coordinates.sl3 m).projection_component_conjugation]
  exact ⟨fun h => SL3.projection_injective D S m (congrArg Multiplicative.ofAdd h),
    fun h => congrArg (fun v => ((Coordinates.sl3 m).projection v).toAdd) h⟩

/-- The original SL₃ point-core fixed space, without an assumed central-kernel splitting. -/
theorem local_core_fixed (f : InvariantFlag (Coordinates.sl3 m)) :
    V ⊓ centralizer ((f.Li 0).pCoreIn 2 : Set G) = f.Vi 0 := by
  ext v
  constructor
  · rintro ⟨hv,hfix⟩
    let v' : V := ⟨v,hv⟩
    apply ((Coordinates.sl3 m).mem_preimage (f.space 0) v').mpr
    apply (model_core_fixed_iff D S m f _).mp
    rintro g ⟨l,hl,rfl⟩
    apply (projection_fixed_iff D S m l v').mpr
    apply Subtype.ext
    change (l : G)*v*(l : G)⁻¹ = v
    rw [hfix l hl,mul_inv_cancel_right]
  · intro hv
    have hvV : v ∈ V := D.centralQuotientPreimage_le _ hv
    let v' : V := ⟨v,hvV⟩
    refine ⟨hvV,?_⟩
    intro l hl
    have hlL : l ∈ L := (pCoreIn_le _ _).trans ((localResidual_le _).trans inf_le_left) hl
    let l' : L := ⟨l,hlL⟩
    have hx := (model_core_fixed_iff D S m f _).mpr
      (((Coordinates.sl3 m).mem_preimage (f.space 0) v').mp hv)
    have he := congrArg Subtype.val ((projection_fixed_iff D S m l' v').mp
      (hx _ ⟨l',hl,rfl⟩))
    change l*v*l⁻¹=v at he
    exact (mul_inv_eq_iff_eq_mul).mp he

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.PointGeometry.SL3Core
