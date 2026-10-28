module
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.A5.FixedSpace
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.Coordinates
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.Constituents.Images
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.FiniteImages.Borel
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Natural.Placements.Transport
public import Theory.Representation.BinaryPermutation.ThreeTensor

/-!
# The deleted tensor Borel on the literal quotient images

Every Sylow normalizer in A₅ fixes the Sylow-fixed vectors of the binary
five-point module. Tensor coordinates transfer this to the actual image
of the Borel of H∞. The two-residual therefore fixes the binary quotient
line, and the commuting tensor factors make it fix the first moved plane.
Vanishing in these prescribed coordinates lifts to the actual center of U.

Only the A₅ restriction of the constituent is marked. The Sylow, Borel and
point coordinates are constructed, and U = O₂(H) is not assumed. The
original source application is in Tensor.DeletedSource.
Source: Aschbacher--Smith 14.4.10(3), printed p.1011.
-/

public section

open Subgroup TensorProduct Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.TensorDeleted
open LargerDimension.Tensor
open BinaryPermutation
open BinaryPermutation.CubicFixedSpace.Five

private theorem klein_card : Nat.card klein = 4 := by
  let w : Fin 4 → AltFive := ![1, first, second, first * second]
  have hw : Function.Injective w := by decide +kernel
  have hm (i : Fin 4) : w i ∈ klein := by
    fin_cases i
    · exact klein.one_mem
    · exact first_mem
    · exact second_mem
    · exact klein.mul_mem first_mem second_mem
  let f : Fin 4 → klein := fun i => ⟨w i, hm i⟩
  have hf : Function.Injective f := fun i j he => hw (congrArg Subtype.val he)
  have hlo := Nat.card_le_card_of_injective f hf
  rw [Nat.card_fin] at hlo
  obtain ⟨S, hS⟩ := klein_isPGroup.exists_le_sylow
  have hc : Nat.card S = 4 := by
    rw [S.card_eq_multiplicity, nat_card_alternatingGroup, Nat.card_fin]
    decide +kernel
  exact le_antisymm ((card_le_of_le hS).trans hc.le) hlo

/-- Every A₅ Sylow normalizer fixes its fixed vectors in the deleted module. -/
theorem normalizer_fixes_core (P : Sylow 2 AltFive) (a : AltFive)
    (ha : a ∈ normalizer (P : Set AltFive)) (v : core (Fin 5))
    (hv : ∀ b ∈ P, coreRepresentation (Fin 5) b.val v = v) :
    coreRepresentation (Fin 5) a.val v = v := by
  let ρ := (coreRepresentation (Fin 5)).comp AltFive.subtype
  let Q : Sylow 2 AltFive := Sylow.ofCard klein (by
    rw [klein_card, nat_card_alternatingGroup, Nat.card_fin]
    decide +kernel)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq AltFive Q P
  have hP : klein.map (MulAut.conj g).toMonoidHom = (P : Subgroup AltFive) := by
    rw [← hg, Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
    rfl
  have ha' : a ∈ (normalizer (klein : Set AltFive)).map (MulAut.conj g).toMonoidHom := by
    rw [map_equiv_normalizer_eq, hP]
    exact ha
  obtain ⟨b, hb, rfl⟩ := ha'
  have hinv (w : core (Fin 5)) : ρ g⁻¹ (ρ g w) = w := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hvk : ρ g⁻¹ v ∈ fixedSpace ρ klein := by
    intro k
    change ρ k.val (ρ g⁻¹ v) = ρ g⁻¹ v
    have hk : g * k.val * g⁻¹ ∈ (P : Subgroup AltFive) := by
      rw [← hP]
      exact mem_map_of_mem (MulAut.conj g).toMonoidHom k.property
    have hh := congrArg (ρ g⁻¹) (hv _ hk)
    change ρ g⁻¹ (ρ (g * k.val * g⁻¹) v) = _ at hh
    simpa only [map_mul, Module.End.mul_apply, hinv] using hh
  have hfix := LargerDimension.Tensor.A5.borel_fixes_core b hb (ρ g⁻¹ v) hvk
  change ρ (g * b * g⁻¹) v = v
  change ρ b (ρ g⁻¹ v) = ρ g⁻¹ v at hfix
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hfix,
    ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

private noncomputable def reversed {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (f : W ≃ₗ[ZMod 2] core (Fin 5)) :
    (core (Fin 3) ⊗[ZMod 2] W) ≃ₗ[ZMod 2] (core (Fin 5) ⊗[ZMod 2] core (Fin 3)) :=
  (TensorProduct.comm (ZMod 2) _ _).trans
    (TensorProduct.congr f (LinearEquiv.refl (ZMod 2) _))

/-- Restriction to A₅ suffices for the tensor Borel fixed-space calculation. -/
theorem normalizer_fixes_tensor {D : Subgroup Five} (hAD : AltFive ≤ D)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) D W) (hdel : IsDeletedFour hAD σ)
    (P : Sylow 2 AltFive) (a : AltFive) (ha : a ∈ normalizer (P : Set AltFive))
    (v : core (Fin 3) ⊗[ZMod 2] W)
    (hv : ∀ b ∈ P, sourceTensorAction σ (1, inclusion hAD b) v = v) :
    sourceTensorAction σ (1, inclusion hAD a) v = v := by
  obtain ⟨f, hf⟩ := hdel
  let e := reversed f
  have he (b : AltFive) (w : core (Fin 3) ⊗[ZMod 2] W) :
      e (sourceTensorAction σ (1, inclusion hAD b) w) =
        ThreeTensor.action (coreRepresentation (Fin 5)) (b.val, 1) (e w) := by
    induction w using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul n w =>
      change f (σ (inclusion hAD b) w) ⊗ₜ[ZMod 2] _ = _
      rw [hf]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  let p := ThreeTensor.pairEquiv (e v)
  have hp (b : AltFive) (hb : b ∈ P) :
      (coreRepresentation (Fin 5) b.val p.1, coreRepresentation (Fin 5) b.val p.2) = p := by
    have hh := congrArg (fun z => ThreeTensor.pairEquiv (e z)) (hv b hb)
    rw [he, ThreeTensor.pairEquiv_equivariant] at hh
    exact hh
  apply e.injective
  rw [he]
  apply ThreeTensor.pairEquiv.injective
  rw [ThreeTensor.pairEquiv_equivariant]
  exact Prod.ext (normalizer_fixes_core P a ha p.1 (fun b hb => congrArg Prod.fst (hp b hb)))
    (normalizer_fixes_core P a ha p.2 (fun b hb => congrArg Prod.snd (hp b hb)))

variable {G : Type*} [Group G] [Finite G]
  {D : Subgroup Five} {hAD : AltFive ≤ D}
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {H U T P : Subgroup G}

/-- The original Borel image fixes the original binary quotient line. -/
theorem borel_fixes_image (c : CaseFiveCoordinates hAD (V := W) H U)
    (hdel : IsDeletedFour hAD c.constituent)
    (S : Sylow 2 H) (hS : (S : Subgroup H).map H.subtype = T)
    (hn : T ≤ normalizer (P : Set G)) (hr : Module.finrank (ZMod 2) (c.image P) = 1) :
    c.image P ≤ fixedSpace (sourceTensorAction c.constituent)
      ((star H (borel H T)).map c.actor.toMonoidHom) := by
  let K := star H (component H)
  let eK : K ≃* AltFive := starComponentEquiv hAD c.actor
  let : K.Normal := by
    dsimp [K]
    rw [Placements.star_component]
    infer_instance
  obtain ⟨Q, hQ⟩ := exists_star_sylow S hS
  obtain ⟨R, hR⟩ := Q.exists_subgroupOf_eq_of_normal K
  let R' : Sylow 2 AltFive := R.mapSurjective (f := eK.toMonoidHom) eK.surjective
  have hmark (k : K) : c.actor k.val = (1, inclusion hAD (eK k)) := by
    have hk := mem_map_of_mem c.actor.toMonoidHom k.property
    rw [star_component_marked hAD c.actor] at hk
    exact Prod.ext hk.1 rfl
  have ht : T ≤ H := hS ▸ map_subtype_le _
  have hfixed := c.point_fixed_of_normalizes ht hn hr
  intro v hv a
  change sourceTensorAction c.constituent a.val v = v
  obtain ⟨b, hb, hab⟩ := a.property
  change c.actor b = a.val at hab
  have hbK : b ∈ K := (map_mono (subgroupOf_mono H (show borel H T ≤ component H from inf_le_left))) hb
  let k : K := ⟨b, hbK⟩
  have hnR : k ∈ normalizer (R : Set K) := by
    change k ∈ normalizer ((R : Subgroup K) : Set K)
    rw [hR, hQ]
    have hbN := (star_borel_eq_relative_normalizer S hS).le hb
    rw [← inf_subgroupOf_right (star H T) K, ← subgroupOf_normalizer_eq inf_le_right]
    exact hbN.2
  have hnR' : eK k ∈ normalizer (R' : Set AltFive) := by
    exact le_normalizer_map eK.toMonoidHom (mem_map_of_mem eK.toMonoidHom hnR)
  rw [← hab, hmark k]
  apply normalizer_fixes_tensor hAD c.constituent hdel R' (eK k) hnR' v
  intro r hrR
  obtain ⟨s, hs, rfl⟩ := hrR
  have hsT : s.val ∈ star H T := by
    rw [hR, hQ] at hs
    exact hs
  change sourceTensorAction c.constituent (1, inclusion hAD (eK s)) v = v
  rw [← hmark s]
  exact hfixed hv ⟨c.actor s.val, mem_map_of_mem c.actor.toMonoidHom hsT⟩

/-- In particular the literal two-residual of that Borel fixes the line. -/
theorem second_fixes_image (c : CaseFiveCoordinates hAD (V := W) H U)
    (hdel : IsDeletedFour hAD c.constituent)
    (S : Sylow 2 H) (hS : (S : Subgroup H).map H.subtype = T)
    (hn : T ≤ normalizer (P : Set G)) (hr : Module.finrank (ZMod 2) (c.image P) = 1) :
    c.image P ≤ fixedSpace (sourceTensorAction c.constituent)
      ((star H (LargerDimension.Tensor.second H T)).map c.actor.toMonoidHom) := by
  intro v hv a
  exact borel_fixes_image c hdel S hS hn hr hv
    ⟨a.val, map_mono (map_mono (subgroupOf_mono H (map_subtype_le _))) a.property⟩

/-- Commuting tensor factors propagate fixation to the first moved plane. -/
theorem second_fixes_first_moved_image (c : CaseFiveCoordinates hAD (V := W) H U)
    (hdel : IsDeletedFour hAD c.constituent)
    (S : Sylow 2 H) (hS : (S : Subgroup H).map H.subtype = T)
    (hn : T ≤ normalizer (P : Set G)) (hr : Module.finrank (ZMod 2) (c.image P) = 1)
    (hPU : P ≤ U) :
    c.image (LargerDimension.movedSpace P (LargerDimension.Tensor.first H)) ≤
      fixedSpace (sourceTensorAction c.constituent)
        ((star H (LargerDimension.Tensor.second H T)).map c.actor.toMonoidHom) := by
  have hp := second_fixes_image c hdel S hS hn hr
  rw [c.image_commutator hPU (first_le H)]
  apply Submodule.span_le.mpr
  rintro _ ⟨a, ha, v, hv, rfl⟩ b
  change sourceTensorAction c.constituent b.val
    (sourceTensorAction c.constituent a v - v) = _
  have ha2 : a.2 = 1 := by
    rw [c.first_actor_image] at ha
    rcases cubicActor_words ha with rfl | rfl | rfl <;> rfl
  have hb1 : b.val.1 = 1 := by
    have hb := map_mono (map_mono (subgroupOf_mono H
      (show LargerDimension.Tensor.second H T ≤ component H from
        (map_subtype_le _).trans inf_le_left))) b.property
    change b.val ∈ (star H (component H)).map c.actor.toMonoidHom at hb
    rw [star_component_marked hAD c.actor] at hb
    exact hb.1
  have hcomm : b.val * a = a * b.val := by
    apply Prod.ext
    · simp only [Prod.fst_mul, hb1, one_mul, mul_one]
    · simp only [Prod.snd_mul, ha2, one_mul, mul_one]
  have hfix : sourceTensorAction c.constituent b.val v = v := hp hv b
  rw [map_sub, ← Module.End.mul_apply, ← map_mul, hcomm,
    map_mul, Module.End.mul_apply, hfix]

omit [Finite G] in
/-- Vanishing in the prescribed coordinates lifts to the actual central kernel. -/
theorem commutator_le_center_of_fixed_image
    (c : CaseFiveCoordinates hAD (V := W) H U) {A X : Subgroup G}
    (hAU : A ≤ U) (hX : X ≤ H)
    (hf : c.image A ≤ fixedSpace (sourceTensorAction c.constituent)
      ((star H X).map c.actor.toMonoidHom)) :
    ⁅X, A⁆ ≤ (center U).map U.subtype := by
  have hu : LargerDimension.movedSpace A X ≤ U :=
    (commutator_mono hAU le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hX.trans c.H_normalizes_U))
  have hm : c.image (LargerDimension.movedSpace A X) = ⊥ := by
    rw [c.image_commutator hAU hX]
    exact (subspaceCommutator_eq_bot_iff _ _ _).mpr hf
  rw [commutator_comm]
  intro x hx
  let xU : U := ⟨x, hu hx⟩
  have hv : (c.quotientMap xU).toAdd ∈ c.image (LargerDimension.movedSpace A X) :=
    (c.mem_image _ _).mpr ⟨xU, hx, rfl⟩
  rw [hm, Submodule.mem_bot] at hv
  have hk : xU ∈ c.quotientMap.ker := congrArg Multiplicative.ofAdd hv
  rw [c.quotientMap_ker] at hk
  exact mem_map_of_mem U.subtype hk

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.TensorDeleted
