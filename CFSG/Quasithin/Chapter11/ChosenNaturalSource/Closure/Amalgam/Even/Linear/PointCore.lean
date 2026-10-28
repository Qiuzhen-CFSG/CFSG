module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.SL3.PlaneAction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Linear.Source
public import Theory.GroupAction.IrreducibleTwoCoreKernel
public import Theory.GroupAction.SubgroupQuotientFullAction

/-!
# The actual SL₃ point core and the even critical pair

In coordinates adapted to the Sylow-invariant point, the quotient V/V₁
has the natural two-dimensional SL₂ action. Every invariant binary subgroup
of that quotient is trivial or the whole quotient. Hence the normal two-core
of L₁T acts trivially there. Transporting its kernel through the literal
quotient map proves [V,R₁] ≤ V₁, retaining the kernel of the original marking.

Uniqueness of the Sylow-invariant flag identifies the canonical point with
the original E.V₁. The bound then discharges the only local action premise
in the SL₃ critical-pair theorem and proves odd distance when W is abelian.
Fixed-space vanishing is the preceding source conclusion from 11.4.1,
owned by qt-d-1222-shadow-components. The full K=L₁ assembly remains with
qt-d-1222-natural-closure-amalgam.
Source: Aschbacher--Smith, §11.1 and 11.5.8, printed pp.760–761 and 784.
-/

set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Matrix
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.SL3
open Matrix.PSL3.LinearThree
open scoped MatrixGroups IsMulCommutative
public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Linear.PointCore

def tailMap {F : Type*} [Field F] : (Fin 3 → F) →+ (Fin 2 → F) where
  toFun v i := v i.succ
  map_zero' := rfl
  map_add' _ _ := rfl

def pointLevi {F : Type*} [Field F] (g : SL(2,F)) : pointLocalSL F :=
  ⟨⟨!![1,0,0; 0,g.val 0 0,g.val 0 1; 0,g.val 1 0,g.val 1 1], by
    have hg := g.property
    rw [det_fin_two] at hg
    simpa [det_fin_three] using hg⟩,
    (mem_pointLocalSL_iff F _).mpr ⟨rfl,rfl,rfl⟩⟩

theorem pointLevi_action {F : Type*} [Field F] (g : SL(2,F)) (v : Fin 3 → F) :
    tailMap (specialLinearNatural 3 (pointLevi g).val v) =
      specialLinearNatural 2 g (tailMap v) := by
  ext i
  change ((pointLevi g).val.val *ᵥ v) i.succ = (g.val *ᵥ fun j => v j.succ) i
  fin_cases i <;> simp [pointLevi,mulVec,dotProduct,Fin.sum_univ_three,Fin.sum_univ_two]

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))

def pointProjection : V →* Multiplicative (Fin 2 → S.field.Carrier) :=
  (tailMap.toMultiplicative.comp
    (specialLinearNatural 3 (alignment D S m)⁻¹).toAddMonoidHom.toMultiplicative).comp
      (coordinates D S m).projection

theorem pointProjection_surjective : Function.Surjective (pointProjection D S m) := by
  intro w
  obtain ⟨v,hv⟩ := (coordinates D S m).projection_surjective
    (Multiplicative.ofAdd (specialLinearNatural 3 (alignment D S m) ![0,w.toAdd 0,w.toAdd 1]))
  refine ⟨v,?_⟩
  apply Multiplicative.toAdd.injective
  change tailMap (specialLinearNatural 3 (alignment D S m)⁻¹
    ((coordinates D S m).projection v).toAdd) = w.toAdd
  rw [hv]
  simp only [toAdd_ofAdd]
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  ext i
  fin_cases i <;> rfl

theorem pointProjection_kernel : (pointProjection D S m).ker =
    ((flag D S m).Vi 0).subgroupOf V := by
  ext v
  rw [MonoidHom.mem_ker]
  change pointProjection D S m v = 1 ↔ (v : G) ∈ (flag D S m).Vi 0
  change _ ↔ (v : G) ∈ (coordinates D S m).preimage (Model.flagFor (alignment D S m) 0)
  rw [(coordinates D S m).mem_preimage]
  rw [PlaneAction.mem_flagFor_iff]
  change Multiplicative.ofAdd (tailMap (specialLinearNatural 3 (alignment D S m)⁻¹
    ((coordinates D S m).projection v).toAdd)) = 1 ↔ _
  change tailMap (specialLinearNatural 3 (alignment D S m)⁻¹
    ((coordinates D S m).projection v).toAdd) = 0 ↔ _
  let w := specialLinearNatural 3 (alignment D S m)⁻¹
    ((coordinates D S m).projection v).toAdd
  change (fun i : Fin 2 => w i.succ) = 0 ↔ w 1 = 0 ∧ w 2 = 0
  exact ⟨fun h => ⟨congrFun h 0,congrFun h 1⟩, fun h => by
    ext i; fin_cases i; exact h.1; exact h.2⟩

theorem pointProjection_intertwines (l : (flag D S m).Li 0)
    (g : SL(2,S.field.Carrier)) (hg : PlaneAction.localProjection D S m 0 l = pointLevi g)
    (v : V) :
    pointProjection D S m
      (V.normalizerMonoidHom (inclusion D.normalizes
        ⟨l,(localResidual_le _ l.property).1⟩) v) =
      Matrix.SL2.naturalAction S.field.Carrier g (pointProjection D S m v) := by
  let a := alignment D S m
  let c := coordinates D S m
  let l' : L := ⟨l,(localResidual_le _ l.property).1⟩
  let w := specialLinearNatural 3 a⁻¹ (c.projection v).toAdd
  have he : specialLinearNatural 3 a⁻¹
      (c.projection (V.normalizerMonoidHom (inclusion D.normalizes l') v)).toAdd =
      specialLinearNatural 3 (PlaneAction.localProjection D S m 0 l).val w := by
    rw [c.projection_component_conjugation,PlaneAction.localProjection_coe]
    change specialLinearNatural 3 a⁻¹ (specialLinearNatural 3 (c.quotientMap l')
      (c.projection v).toAdd) =
      specialLinearNatural 3 (a⁻¹ * (show SL(3,S.field.Carrier) from c.quotientMap l') * (a⁻¹)⁻¹) w
    simp [w,map_mul]
  apply Multiplicative.toAdd.injective
  change tailMap (specialLinearNatural 3 a⁻¹
    (c.projection (V.normalizerMonoidHom (inclusion D.normalizes l') v)).toAdd) =
      specialLinearNatural 2 g (tailMap w)
  rw [he,hg]
  exact pointLevi_action g w

theorem point_core_bound : ⁅V, (flag D S m).Ri 0⁆ ≤ (flag D S m).Vi 0 := by
  let U := (flag D S m).Vi 0
  let A := (flag D S m).Li 0
  let J := A ⊔ (T : Subgroup G)
  let p := pointProjection D S m
  have hp := pointProjection_surjective D S m
  have hk : p.ker = U.subgroupOf V := pointProjection_kernel D S m
  have hJV : J ≤ normalizer (V : Set G) :=
    sup_le ((localResidual_le _).trans (inf_le_left.trans D.normalizes)) S.sylow_normalizes
  have hJU : J ≤ normalizer (U : Set G) :=
    sup_le ((localResidual_le _).trans inf_le_right) ((flag D S m).invariant 0)
  let := D.elementary
  have hN : (U.subgroupOf V).Normal := inferInstance
  obtain ⟨α,hα⟩ := exists_quotient_conjugation_action J V U hJV hJU hN
  let e : (V ⧸ U.subgroupOf V) ≃* Multiplicative (Fin 2 → S.field.Carrier) :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective p hp)
  have he (v : V) : e (QuotientGroup.mk' (U.subgroupOf V) v) = p v := rfl
  let ρ := (MulAut.congr e).toMonoidHom.comp α
  have hρ (j : J) (v : V) : ρ j (p v) =
      p (V.normalizerMonoidHom (inclusion hJV j) v) := by
    rw [← he]
    change e (α j (e.symm (e (QuotientGroup.mk' (U.subgroupOf V) v)))) = _
    rw [e.symm_apply_apply,hα]
    rfl
  have hirr (B : Subgroup (Multiplicative (Fin 2 → S.field.Carrier)))
      (hB : ∀ g : ρ.range, ∀ w, w ∈ B → g • w ∈ B) : B = ⊥ ∨ B = ⊤ := by
    apply Matrix.SL2.naturalAction_irreducible S.field.Carrier B
    intro g w hw
    obtain ⟨l,hl⟩ := PlaneAction.localProjection_surjective D S m 0 (pointLevi g)
    let j : J := ⟨l,(le_sup_left : A ≤ J) l.property⟩
    have heq : ρ j w = Matrix.SL2.naturalAction S.field.Carrier g w := by
      obtain ⟨v,rfl⟩ := hp w
      rw [hρ]
      exact pointProjection_intertwines D S m l g hl v
    rw [← heq]
    exact hB ⟨ρ j,⟨j,rfl⟩⟩ w hw
  have hc := irreducible_range_core_le_ker ρ hirr
  rw [commutator_comm]
  apply commutator_le.mpr
  rintro r ⟨j,hj,rfl⟩ v hv
  let v' : V := ⟨v,hv⟩
  have ht : ρ j = 1 := hc hj
  have hd : p (V.normalizerMonoidHom (inclusion hJV j) v' * v'⁻¹) = 1 := by
    rw [map_mul,map_inv,← hρ,ht]
    exact mul_inv_cancel (p v')
  have hm : V.normalizerMonoidHom (inclusion hJV j) v' * v'⁻¹ ∈ U.subgroupOf V := by
    rw [← hk]
    exact hd
  exact hm

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Linear.PointCore

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Linear
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} {E : Closure.Geometry D}
  (m : ActionEquiv D.centralQuotientAction (linearNatural E.input.field 3))
  (f : InvariantFlag (.sl3 m)) (hm : FlagMatch E f)

include m f hm

theorem point_core_bound : ⁅V, E.R₁⁆ ≤ E.V₁ := by
  have hp : (SL3.flag D E.input m).Vi 0 = E.V₁ := by
    rw [← hm.point_eq]
    apply congrArg (Coordinates.sl3 m).preimage
    exact (SL3.flag_unique D E.input m 0 (f.space 0) (f.dimension 0) (f.invariant 0)).symm
  have hr : (SL3.flag D E.input m).Ri 0 = E.R₁ := by
    change LocalGeometry.localRadical T L ((SL3.flag D E.input m).Vi 0) = E.R₁
    rw [hp]
    rfl
  simpa only [hp, hr] using PointCore.point_core_bound D E.input m

theorem critical_pair_geometry
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (g : G) (hg : V.map (MulAut.conj g).toMonoidHom ≤ E.R₁)
    (hne : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (hle : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≤
      V ⊓ V.map (MulAut.conj g).toMonoidHom) :
    ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = E.V₁ ∧
      IsFieldLine E (.sl3 m) (E.V₁.map (MulAut.conj g⁻¹).toMonoidHom) :=
  critical_pair_geometry_of_core_bound m f hm hfixed (point_core_bound m f hm) g hg hne hle

theorem odd_distance
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) (hab : IsMulCommutative E.W)
    (h : LocalInputs E) (hout : ¬ E.K ≤ E.M) :
    Odd (distance E h hout) := by
  exact Nat.not_even_iff_odd.mp
    (not_even_of_core_bound m f hm hfixed (point_core_bound m f hm) hab h hout)
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Linear

