module
public import Theory.Representation.BinaryAlternatingNaturalCohomology.PointCoreFixed
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.MovingLayer
public import Theory.Representation.NormalElementaryEmbedding
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.MaximalOffenders
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.PointImage
/-!
# Fixed vectors of the maximum-order family in the symplectic source

In the full point-core branch, the maximum-order small-mover family generates
R. The actual elementary layer X is an extension of the marked natural layer
W by a component-trivial module. Its point-core fixed vectors lie in W times
the component-fixed subgroup, even when that extension has no fixed complement.
The proof uses the displacement cocycle on A6 and the original natural
coordinates; the quotient action is the literal source projection.

Mapping this containment into the holomorph gives C_X(J) <= U D. The last
application uses the same characteristic replacement, projection and relabeler
as the original SourceData. It discharges MS93 (5.3) in the full point-core
branch; no bound on the critical distance is asserted here.

Source: Meierfrankenfeld--Stellmacher (1993), (5.3), printed p.915.
-/

@[expose] public section
open Subgroup BinaryPermutation Representation Representation.OneCohomology
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
namespace Source
variable {M : Type*} [Group M] [Finite M]
variable {L R W : Subgroup M} [L.Normal] [W.Normal] (s : Source L R W)
include s

/-- The central-layer calculation descends through the injective source embedding. -/
theorem ambientX_commutator (h : NativeCentralLayer s) :
 ⁅Source.ambientX (M:=M),L⁆ = W := by
 apply (map_injective (embedM_injective R))
 rw [map_commutator,←s.X_alpha_eq,←s.residual,←Ltilde_alpha]
 exact h.X_commutator.trans h.U_eq_module

set_option backward.isDefEq.respectTransparency false in
/-- Point-core fixed vectors in the actual elementary layer lie in the marked
natural layer times its component-fixed subgroup. -/
theorem ambientX_fixed_point_le (hq : Function.Surjective s.projection)
 (h : NativeCentralLayer s) (t : S)
 (hR : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom) :
 Source.ambientX (M:=M) ⊓ centralizer (R : Set M) ≤
 W ⊔ (Source.ambientX (M:=M) ⊓ centralizer (L : Set M)) := by
 classical
 let X := Source.ambientX (M:=M)
 let := s.ambientX_normal
 let := omegaCenter_elementary (pCore 2 M)
 let := s.module_elementary
 have hker : s.projection.ker = centralizer (X : Set M) := by
  rw [s.projection_kernel,s.ambientX_centralizer]
 let σ := Representation.NormalElementaryQuotient.representation X s.projection hq hker
 let j : natural (Fin 6) →+ Additive W := {
  toFun := fun v => Additive.ofMul (s.coordinates.symm (Multiplicative.ofAdd v))
  map_zero' := by
   change s.coordinates.symm 1=1
   exact map_one _
  map_add' := by
   intro v w
   change s.coordinates.symm (Multiplicative.ofAdd v * Multiplicative.ofAdd w) =
    s.coordinates.symm (Multiplicative.ofAdd v)*s.coordinates.symm (Multiplicative.ofAdd w)
   exact map_mul _ _ _ }
 let inc := Representation.NormalElementaryQuotient.inclusionLinear W X s.module_le_ambientX
 let i : (naturalRepresentation (Fin 6)).IntertwiningMap σ := {
  toLinearMap := inc.comp (j.toZModLinearMap 2)
  isIntertwining' := by
   intro a
   apply LinearMap.ext
   intro v
   obtain ⟨m,rfl⟩ := hq a
   have he : s.coordinates.symm (Multiplicative.ofAdd
       (naturalRepresentation (Fin 6) (s.projection m) v)) =
       MulAut.conjNormal m (s.coordinates.symm (Multiplicative.ofAdd v)) := by
    apply s.coordinates.injective
    apply Multiplicative.toAdd.injective
    rw [MulEquiv.apply_symm_apply,s.action,MulEquiv.apply_symm_apply]
    rfl
   apply Additive.toMul.injective
   apply Subtype.ext
   change (s.coordinates.symm (Multiplicative.ofAdd
     (naturalRepresentation (Fin 6) (s.projection m) v)) : M) =
    ((σ (s.projection m) (Additive.ofMul
      ⟨s.coordinates.symm (Multiplicative.ofAdd v),s.module_le_ambientX
        (s.coordinates.symm (Multiplicative.ofAdd v)).property⟩)).toMul : M)
   rw [Representation.NormalElementaryQuotient.representation_apply,he]
   rfl }
 have hi : Function.Injective i := by
  intro v w he
  have hj := Representation.NormalElementaryQuotient.inclusionLinear_injective
    W X s.module_le_ambientX he
  exact Multiplicative.ofAdd.injective (s.coordinates.symm.injective (Additive.ofMul.injective hj))
 have hm (g : alternatingGroup (Fin 6)) (x : Additive X) :
   ∃u : natural (Fin 6),i u=σ g.val x-x := by
  obtain ⟨l,hl,he⟩ := s.component_image.ge g.property
  have hc : ⁅l,(x.toMul : M)⁆ ∈ W := by
   rw [←ambientX_commutator s h,commutator_comm]
   exact commutator_mem_commutator hl x.toMul.property
  let w : W := ⟨⁅l,(x.toMul:M)⁆,hc⟩
  refine ⟨(s.coordinates w).toAdd,?_⟩
  apply Additive.toMul.injective
  rw [toMul_sub,div_eq_mul_inv]
  apply Subtype.ext
  change (s.coordinates.symm (Multiplicative.ofAdd (s.coordinates w).toAdd):M)=
   ((σ g.val x).toMul:M)*(x.toMul:M)⁻¹
  rw [ofAdd_toAdd,MulEquiv.symm_apply_apply,←he,
   Representation.NormalElementaryQuotient.representation_apply]
  rfl
 intro x hx
 let v : Additive X := Additive.ofMul ⟨x,hx.1⟩
 have hv : v ∈ Representation.BinaryOffender.fixedSpace σ
   (pointCore.map (MulAut.conj t).toMonoidHom) := by
  rw [←hR]
  exact (Representation.NormalElementaryQuotient.mem_fixedSpace_image
   X s.projection hq hker R v).mpr hx.2
 have hb := BinaryPermutation.PointCoreFixed.fixed_conjugate_le_natural_sup_alternating σ i hi hm t hv
 obtain ⟨u,⟨w,rfl⟩,y,hy,he⟩ := Submodule.mem_sup.mp hb
 have hu : ((i w).toMul : M) ∈ W := (s.coordinates.symm (Multiplicative.ofAdd w)).property
 have hyM : (y.toMul : M) ∈ X ⊓ centralizer (L : Set M) := by
  refine ⟨y.toMul.property,?_⟩
  apply (Representation.NormalElementaryQuotient.mem_fixedSpace_image
   X s.projection hq hker L y).mp
  rw [s.component_image]
  exact hy
 have heM : ((i w).toMul:M)*(y.toMul:M)=x := congrArg (fun z:Additive X => (z.toMul:M)) he
 rw [←heM]
 exact mul_mem (mem_sup_left hu) (mem_sup_right hyM)

/-- The same fixed-vector bound in the literal source holomorph. -/
theorem fixed_point_le_moving_fixed (h : NativeCentralLayer s) (t : S)
 (hR : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom) :
 X R (alpha R) ⊓ centralizer (R.map (embedM R) : Set (FreeAmalgam R)) ≤
 U R (alpha R) ⊔ fixedCore R (alpha R) := by
 have hRE : R.map s.projection = CFSG.Quasithin.ChapterC.NaturalSixControl.Model.E.map
    (MulAut.conj t).toMonoidHom := by
  rwa [CFSG.Quasithin.ChapterC.NaturalSixControl.Model.pointCore_eq_exceptional] at hR
 have hq := s.projection_surjective_of_radical_image_le_conjugate t hRE.le
 have hD : (Source.ambientX (M:=M) ⊓ centralizer (L : Set M)).map (embedM R) ≤
   fixedCore R (alpha R) := by
  rintro x ⟨v,⟨hv,hc⟩,rfl⟩
  refine ⟨?_,?_⟩
  · rw [Q_alpha R s.two_group s.core_le]
    exact mem_map_of_mem _ ((omegaCenter_le (pCore 2 M)) hv)
  · rw [Ltilde_alpha,s.residual]
    rintro l ⟨m,hm,rfl⟩
    simpa only [←map_mul] using congrArg (embedM R) (hc m hm)
 have hb : (Source.ambientX (M:=M) ⊓ centralizer (R : Set M)).map (embedM R) ≤
   U R (alpha R) ⊔ fixedCore R (alpha R) := by
  apply (map_mono (ambientX_fixed_point_le s hq h t hR)).trans
  rw [Subgroup.map_sup,h.U_eq_module]
  exact sup_le_sup le_rfl hD
 rintro x ⟨hx,hc⟩
 rw [s.X_alpha_eq] at hx
 obtain ⟨v,hv,rfl⟩ := hx
 have hcM : v ∈ centralizer (R : Set M) := by
  intro r hr
  apply embedM_injective R
  simpa only [map_mul] using hc (embedM R r) (mem_map_of_mem _ hr)
 exact hb (mem_map_of_mem _ ⟨hv,hcM⟩)

/-- Source (5.3) uses the literal maximum-order family, whose join is the radical. -/
theorem fixed_offenderJoin_le_moving_fixed (h : NativeCentralLayer s) (t : S)
 (hR : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom) :
 X R (alpha R) ⊓ centralizer (s.offenderJoin.map (embedM R) : Set (FreeAmalgam R)) ≤
 U R (alpha R) ⊔ fixedCore R (alpha R) := by
 have hRE : R.map s.projection = CFSG.Quasithin.ChapterC.NaturalSixControl.Model.E.map
    (MulAut.conj t).toMonoidHom := by
  rwa [CFSG.Quasithin.ChapterC.NaturalSixControl.Model.pointCore_eq_exceptional] at hR
 rw [s.offenderJoin_eq t hRE]
 exact fixed_point_le_moving_fixed s h t hR

end Source
namespace SourceData
variable {K : Type*} [Group K] [Finite K]
  {L V : Subgroup K} [L.Normal] [V.Normal] {T : Sylow 2 K}
  (d : CFSG.Quasithin.ChapterC.NaturalSixControl.SourceData L V T)

/-- The original characteristic replacement supplies the central-layer and
quotient-action premises internally. -/
theorem reducedSource_fixed_offenderJoin (h : IntrinsicMSPair d)
 (c : CharacteristicReduction (L.subgroupOf (L ⊔ d.B))
   (d.B.subgroupOf (L ⊔ d.B)))
 (hfull : c.radical.map ((originalSource d h).reduce c).projection =
   pointCore.map (MulAut.conj d.relabeler.val⁻¹).toMonoidHom) :
 X c.radical (alpha c.radical) ⊓ centralizer
   (((originalSource d h).reduce c).offenderJoin.map (embedM c.radical) : Set (FreeAmalgam c.radical)) ≤
 U c.radical (alpha c.radical) ⊔ fixedCore c.radical (alpha c.radical) :=
 Source.fixed_offenderJoin_le_moving_fixed ((originalSource d h).reduce c)
   (CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData.reduced_nativeCentralLayer d h c) d.relabeler.val⁻¹ hfull
end SourceData
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
