module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.Xi
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The source Xi residual has no fixed vector on the doubled module

A diagonal pair of binary-plane cubics preserves any two-space of the
natural four-space and has no nonzero fixed vector on either the natural
space or its dual. Its odd order places it in the two-residual of that
plane parabolic. The Sylow-compatible source coordinates identify this
parabolic with the inner normalizer of the actual marked offender.
Consequently the full marked normalizer residual has zero fixed space.

Thompson normalizer transport through the original LT action quotient
then lifts this calculation to the literal X constructed in Xi: C_W(X)=1.
The final chosen-module application discharges Thompson movement from the
original contrary ambient Sylow branch, without an MS or splitting premise.
This is the fixed-space input to the remaining R2(LQ) decomposition and
omega-center argument in qt-d-double-natural-pure-fusion. The parent
qt-d-double-natural-centralizers retains the earlier-input assembly.

Source: Aschbacher--Smith, 12.1.4, printed p.790, using the two-space
parabolic in B.4.9(2iii), pp.92,94.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi
private abbrev Plane := Fin 2 → ZMod 2
private def cubic : Plane ≃ₗ[ZMod 2] Plane where
  toFun v := ![v 1, v 0 + v 1]
  invFun v := ![v 0 + v 1, v 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by decide +kernel
  map_smul' := by decide +kernel
private theorem cubic_cube : cubic ^ 3 = 1 := by
  ext v i
  exact (by decide +kernel : ∀ v : Plane, ∀ i : Fin 2, cubic (cubic (cubic v)) i = v i) v i
private theorem cubic_fixed : ∀ v, cubic v = v → v = 0 := by decide +kernel

private theorem parabolic_cubic {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E] (U : Submodule (ZMod 2) E)
    (hE : Module.finrank (ZMod 2) E = 4) (hU : Module.finrank (ZMod 2) U = 2) :
    ∃ g : BinaryLinear.parabolic U, g ^ 3 = 1 ∧ ∀ v : E, (g : E ≃ₗ[ZMod 2] E) v = v → v = 0 := by
  obtain ⟨Q,hQ⟩ := U.exists_isCompl
  have hQd : Module.finrank (ZMod 2) Q = 2 := by
    have hh := Submodule.finrank_add_eq_of_isCompl hQ
    omega
  let eU : U ≃ₗ[ZMod 2] Plane := LinearEquiv.ofFinrankEq _ _ (by simpa using hU)
  let eQ : Q ≃ₗ[ZMod 2] Plane := LinearEquiv.ofFinrankEq _ _ (by simpa using hQd)
  let e := (U.prodEquivOfIsCompl Q hQ).symm.trans (eU.prodCongr eQ)
  let c := cubic.prodCongr cubic
  let g : E ≃ₗ[ZMod 2] E := e.trans (c.trans e.symm)
  have hg : g ∈ BinaryLinear.parabolic U := by
    intro v
    have hh (x : E) : (e x).2 = 0 ↔ x ∈ U := by
      change eQ (((U.prodEquivOfIsCompl Q hQ).symm x).2) = 0 ↔ x ∈ U
      rw [eQ.map_eq_zero_iff]
      exact Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero U Q hQ
    have he (v : E) : e (g v) = c (e v) := e.apply_symm_apply _
    rw [←hh,he,←hh]
    exact cubic.map_eq_zero_iff
  have hc : ∀ v : E, g (g (g v)) = v := by
    intro v
    apply e.injective
    have he (x : E) : e (g x) = c (e x) := e.apply_symm_apply _
    rw [he, he, he]
    have h (x : Plane) : cubic (cubic (cubic x)) = x := LinearEquiv.congr_fun cubic_cube x
    exact Prod.ext (h (e v).1) (h (e v).2)
  refine ⟨⟨g,hg⟩,?_,?_⟩
  · apply Subtype.ext
    ext v
    exact hc v
  · intro v hv
    have hh := congrArg e hv
    change e (e.symm (c (e v))) = e v at hh
    rw [e.apply_symm_apply] at hh
    have he : e v = 0 := Prod.ext (cubic_fixed _ (congrArg Prod.fst hh))
      (cubic_fixed _ (congrArg Prod.snd hh))
    exact e.injective (he.trans e.map_zero.symm)

private theorem naturalDual_fixed_of_cubic
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
    (g : E ≃ₗ[ZMod 2] E) (hg : ∀ v, g v = v → v = 0)
    (v : E × Module.Dual (ZMod 2) E)
    (hv : BinaryNaturalDual.naturalDualRepresentation g v = v) : v = 0 := by
  rw [BinaryNaturalDual.naturalDualRepresentation_apply] at hv
  have hx : v.1 = 0 := hg _ (congrArg Prod.fst hv)
  have hi : Function.Injective (g.toLinearMap - (LinearMap.id : E →ₗ[ZMod 2] E)) := by
    apply (LinearMap.ker_eq_bot (f := g.toLinearMap - (LinearMap.id : E →ₗ[ZMod 2] E))).mp
    apply bot_unique
    intro x hx
    exact hg x (sub_eq_zero.mp hx)
  have hs := (LinearMap.injective_iff_surjective (f :=
    g.toLinearMap - (LinearMap.id : E →ₗ[ZMod 2] E))).mp hi
  have hf : v.2 = 0 := by
    ext x
    obtain ⟨y,rfl⟩ := hs x
    change v.2 (g y - y) = 0
    rw [map_sub,sub_eq_zero]
    have hh := congrArg (fun z : E × Module.Dual (ZMod 2) E => z.2 (g y)) hv
    change v.2 (g.symm (g y)) = v.2 (g y) at hh
    simpa only [LinearEquiv.symm_apply_apply] using hh.symm
  exact Prod.ext hx hf

/-- The two-residual of the marked plane parabolic has no fixed vectors
on the natural-plus-dual module. -/
private theorem plane_residual_fixed
    (U : Submodule (ZMod 2) BinaryNaturalDual.FourActors.X)
    (hU : Module.finrank (ZMod 2) U = 2)
    (v : BinaryNaturalDual.FourActors.V)
    (hv : ∀ g : BinaryLinear.parabolic U, g ∈ pResidual 2 (BinaryLinear.parabolic U) →
      BinaryNaturalDual.naturalDualRepresentation g.val v = v) : v = 0 := by
  obtain ⟨g,hg,hfix⟩ := parabolic_cubic U (by simp) hU
  have hm : g ∈ pResidual 2 (BinaryLinear.parabolic U) :=
    mem_pResidual_of_orderOf_coprime
      ((by decide : Nat.Coprime 2 3).of_dvd_right (orderOf_dvd_of_pow_eq_one hg))
  exact naturalDual_fixed_of_cubic g.val hfix v (hv g hm)
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi

namespace CFSG.Quasithin.ChapterH.NaturalDual.SourceSetup
open SourceFourActors
variable {M E : Type*} [Group M] [AddCommGroup E] [Module (ZMod 2) E]
  (S : SourceSetup 4 M E) (P : Sylow 2 M)

/-- The actual residual of the full marked normalizer fixes no vector. -/
theorem four_A0_normalizer_residual_fixed (v : E)
    (hv : ∀ g : normalizer (A0 S P : Set M),
      g ∈ pResidual 2 (normalizer (A0 S P : Set M)) →
        S.representation g.val v = v) : v = 0 := by
  let := S.finite_group
  let I := normalizer ((A0 S P).subgroupOf (componentLayer M) : Set (componentLayer M))
  let N := normalizer (A0 S P : Set M)
  let e : I ≃* BinaryLinear.parabolic BinaryNaturalDual.FourActors.A0Plane :=
    ((layerCoordinates S P).subgroupMap I).trans
      (MulEquiv.subgroupCongr (S.four_A0_inner_normalizer P))
  let f : I →* N := {
    toFun := fun x => ⟨x.val.val, (subgroupOf_normalizer_eq (A0_le_layer S P)).ge x.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  apply (coordinates S P).injective
  rw [map_zero]
  apply Chapter12.Section01.DoubleNaturalSource.PureFourXi.plane_residual_fixed
    _ BinaryNaturalDual.FourActors.A0Plane_finrank
  intro g hg
  let i := e.symm g
  have hi : i ∈ pResidual 2 I :=
    map_pResidual_le 2 e.symm.toMonoidHom (mem_map_of_mem e.symm.toMonoidHom hg)
  have hf : f i ∈ pResidual 2 N :=
    map_pResidual_le 2 f (mem_map_of_mem f hi)
  have hh := congrArg (coordinates S P) (hv (f i) hf)
  rw [equivariant, show (f i : M) = (i.val : M) from rfl, group_layer,
    BinaryNaturalDual.CoordinateAction.on_inner] at hh
  have he : layerCoordinates S P i.val = g.val := congrArg Subtype.val (e.apply_symm_apply g)
  rwa [he] at hh
end CFSG.Quasithin.ChapterH.NaturalDual.SourceSetup

namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel
open Stellmacher ChapterH.NaturalDual.SourceFourActors
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {B : DoubledBranch T L V 4}
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]
  (S : B.SourceModel)

include S in
/-- The image of the original LT-normalizer is the full marked normalizer. -/
theorem four_thompson_normalizer_image
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hWT : componentOrbit V (T : Subgroup G) ≤ (T : Subgroup G))
    (hm : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (componentOrbit V (T : Subgroup G) : Set G)) :
    ((normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)).subgroupOf
      (L ⊔ (T : Subgroup G))).map (B.joinActionProjection hTM) =
      normalizer (A0 S.setup
        ((T.subtype hTM).mapSurjective B.actionProjection_surjective) : Set B.ActionQuotient) := by
  let H := L ⊔ (T : Subgroup G)
  let R := (T : Subgroup G).subgroupOf H
  let f := B.joinActionProjection hTM
  let P := (T.subtype hTM).mapSurjective B.actionProjection_surjective
  obtain ⟨hf,_,hkR⟩ := S.four_join_action hTM
  have hJR : (elementaryAbelianMaxJ R).map H.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,
      map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ H from le_sup_right)]
  have hJH : elementaryAbelianMaxJ (T : Subgroup G) ≤ H :=
    (show elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) from
      sSup_le fun _ hA => hA.1).trans le_sup_right
  have hJR' : elementaryAbelianMaxJ R =
      (elementaryAbelianMaxJ (T : Subgroup G)).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hJR,map_subgroupOf_eq_of_le hJH]
  have himage : (elementaryAbelianMaxJ R).map f = A0 S.setup P := by
    rw [hJR']
    have he : ((elementaryAbelianMaxJ (T : Subgroup G)).subgroupOf H).map f =
        ((elementaryAbelianMaxJ (T : Subgroup G)).subgroupOf (normalizer (L : Set G))).map
          B.actionProjection := by
      ext a
      constructor <;> rintro ⟨x,hx,rfl⟩
      · exact ⟨⟨x,(sup_le L.le_normalizer hTM) x.property⟩,hx,rfl⟩
      · exact ⟨⟨x,hJH hx⟩,hx,rfl⟩
    rw [he]
    exact S.four_thompson_image hTM hWT hm
  change ((normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)).subgroupOf H).map f = _
  rw [subgroupOf_normalizer_eq hJH,←hJR',normalizer_map_maxJ R f hf hkR,himage]

include S in
/-- The source residual X has trivial centralizer on the original W. -/
theorem four_xi_centralizer_eq_bot
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hWT : componentOrbit V (T : Subgroup G) ≤ (T : Subgroup G))
    (hm : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (componentOrbit V (T : Subgroup G) : Set G)) :
    componentOrbit V (T : Subgroup G) ⊓ centralizer (PureFourXi.residual T L : Set G) = ⊥ := by
  let H := L ⊔ (T : Subgroup G)
  let N := (normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)).subgroupOf H
  let P := (T.subtype hTM).mapSurjective B.actionProjection_surjective
  let A := normalizer (A0 S.setup P : Set B.ActionQuotient)
  let f := B.joinActionProjection hTM
  have hN : N.map f = A := S.four_thompson_normalizer_image hTM hWT hm
  let q : N →* A := (MulEquiv.subgroupCongr hN).toMonoidHom.comp (f.subgroupMap N)
  have hq : Function.Surjective q := (MulEquiv.subgroupCongr hN).surjective.comp
    (f.subgroupMap_surjective N)
  let e : N ≃* PureFourXi.normalizerJoin T L := {
    toFun := fun x => ⟨x.val.val,x.property,x.val.property⟩
    invFun := fun x => ⟨⟨x.val,x.property.2⟩,x.property.1⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }
  apply bot_unique
  intro w hw
  have hz : Additive.ofMul (⟨w,hw.1⟩ : componentOrbit V (T : Subgroup G)) = 0 := by
    apply S.setup.four_A0_normalizer_residual_fixed P
    intro a ha
    have ha' : a ∈ (pResidual 2 N).map q := (map_pResidual_of_surjective 2 q hq).symm ▸ ha
    obtain ⟨u,hu,rfl⟩ := ha'
    have hx : u.val.val ∈ PureFourXi.residual T L :=
      mem_map_of_mem (PureFourXi.normalizerJoin T L).subtype
        (map_pResidual_le 2 e.toMonoidHom (mem_map_of_mem e.toMonoidHom hu))
    rw [S.representation_eq]
    apply Additive.toMul.injective
    apply Subtype.ext
    change (B.quotientAction (B.actionProjection
      (inclusion (sup_le L.le_normalizer hTM) u.val)) ⟨w,hw.1⟩ : G) = w
    rw [B.quotientAction_projection_apply]
    exact mul_inv_eq_of_eq_mul (hw.2 u.val.val hx)
  exact congrArg (fun z : Additive (componentOrbit V (T : Subgroup G)) => (z.toMul : G)) hz
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource Stellmacher
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- In the original contrary Sylow branch, X has no nonidentity fixed point
on the doubled module. No MS or whole-module splitting premise is used. -/
theorem doubleNatural_four_pure_xi_centralizer_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      ¬ Chapter1.IsSylowIn 2 (B.pointSylow w) (B.pointCentralizer w) →
      componentOrbit V (T : Subgroup G) ⊓ centralizer (PureFourXi.residual T L : Set G) = ⊥ := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix hf
  exact S.four_xi_centralizer_eq_bot D.sylow_normalizes_component
    (D.doubledOrbit_E322 h).le_sylow
    (D.doubleNatural_four_pure_thompson_moves_of_many h hmany B S w hw hp hfix hf).2
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
