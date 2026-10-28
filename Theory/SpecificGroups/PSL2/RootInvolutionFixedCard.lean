module
public import Theory.SpecificGroups.PSL2.RootSemilinearFixedBound
public import Theory.SpecificGroups.PSL2.SemilinearCoverage
public import Theory.Representation.SemilinearInvolutionFixedCard

/-!
# Fixed Sylow subgroups of outer involutions in binary PSL₂

A root-preserving automorphism is scalar-semilinear on the additive root line.
For an outer involution its field coefficient is nontrivial and involutory,
so the trace-one displacement argument gives a square-root fixed subgroup.
Sylow conjugacy and a marked group isomorphism transport the same count to
any invariant Sylow subgroup, without selecting a pure-field representative.

Source application: Aschbacher–Smith, Lemma 2.4.12(2), printed p.532.
-/

public section
open Subgroup BenderSuzuki.Converse
namespace Theory.PSL2.RootSemilinear
open Matrix.ProjectiveSpecialLinearGroup.OddBorel
open Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem fixed_card_sq
    (a : MulAut (Group F)) (hnorm : (kernel F).map a.toMonoidHom = kernel F)
    (ha : a ^ 2 = 1) (houter : ¬ ∃ g : Group F, a = MulAut.conj g) :
    Nat.card {u : kernel F // a u = u} ^ 2 = Nat.card (kernel F) := by
  obtain ⟨g,σ,he⟩ := Theory.PSL2.semilinear_coverage a
  have hs := (semilinear_involution_data σ g (he ▸ ha)).1
  have hne : σ ≠ RingEquiv.refl F := by
    intro h
    exact houter ⟨g,by simpa only [h,fieldAut_refl,mul_one] using he⟩
  obtain ⟨c,hc⟩ := scalar_action a hnorm g σ he
  let T : F →+ F :=
    { toFun x := c * σ x
      map_zero' := by simp
      map_add' x y := by simp [mul_add] }
  have hT : Function.Involutive T := by
    intro x
    apply Multiplicative.ofAdd.injective
    apply unipotentHom_injective F
    change unipotentHom F (Multiplicative.ofAdd (c * σ (c * σ x))) = unipotentHom F (Multiplicative.ofAdd x)
    have h1 := hc (Multiplicative.ofAdd x)
    have h2 := hc (Multiplicative.ofAdd (c * σ x))
    change a (unipotentHom F (Multiplicative.ofAdd x)) = unipotentHom F (Multiplicative.ofAdd (c*σ x)) at h1
    change a (unipotentHom F (Multiplicative.ofAdd (c*σ x))) = unipotentHom F (Multiplicative.ofAdd (c*σ (c*σ x))) at h2
    rw [←h2,←h1]
    exact DFunLike.congr_fun ha (unipotentHom F (Multiplicative.ofAdd x))
  have hsemi (d x : F) : T (d • x) = σ d • T x := by
    change c * σ (d*x)=σ d*(c*σ x)
    rw [map_mul]
    ring
  let e : Multiplicative F ≃* kernel F := MonoidHom.ofInjective (unipotentHom_injective F)
  have heval (u : kernel F) : unipotentHom F (e.symm u) = u :=
    congrArg Subtype.val (e.apply_symm_apply u)
  let ef : {u : kernel F // a u = u} ≃ T.eqLocus (AddMonoidHom.id F) :=
    (e.symm.toEquiv.trans Multiplicative.toAdd).subtypeEquiv (fun u => by
      change a u = u ↔ c * σ (e.symm u).toAdd = (e.symm u).toAdd
      have hh := hc (e.symm u)
      rw [heval] at hh
      constructor
      · intro hu
        apply Multiplicative.ofAdd.injective
        apply unipotentHom_injective F
        exact hh.symm.trans (hu.trans (heval u).symm)
      · intro hu
        rw [hh,hu]
        exact heval u)
  calc
    Nat.card {u : kernel F // a u = u} ^ 2 = Nat.card (T.eqLocus (AddMonoidHom.id F)) ^ 2 := by rw [Nat.card_congr ef]
    _ = Nat.card F := Representation.SemilinearInvolution.fixed_card_sq σ hs hne T hT hsemi
    _ = Nat.card (kernel F) := by simpa only [Nat.card_congr Multiplicative.toAdd] using Nat.card_congr e.toEquiv

theorem sylow_fixed_card_sq
    (P : Sylow 2 (Group F)) (a : MulAut (Group F))
    (hnorm : (P : Subgroup (Group F)).map a.toMonoidHom = P)
    (ha : a ^ 2 = 1) (houter : ¬ ∃ g : Group F, a = MulAut.conj g) :
    Nat.card {u : P // a u = u} ^ 2 = Nat.card P := by
  classical
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Group F) P (standardSylow F)
  let eG := MulAut.conj g
  have hmap : (P : Subgroup (Group F)).map eG.toMonoidHom = kernel F := by
    have hh := congrArg (fun P : Sylow 2 (Group F) => (P : Subgroup (Group F))) hg
    have hf : (MulDistribMulAction.toMonoidEnd (MulAut (Group F)) (Group F)) (MulAut.conj g) = eG.toMonoidHom := by
      ext x
      rfl
    simpa only [Sylow.smul_def,Sylow.pointwise_smul_def,Subgroup.pointwise_smul_def,coe_standardSylow,hf] using hh
  let b := MulAut.congr eG a
  have hcomp : b.toMonoidHom.comp eG.toMonoidHom = eG.toMonoidHom.comp a.toMonoidHom := by
    ext x
    change eG (a (eG.symm (eG x)))=eG (a x)
    rw [eG.symm_apply_apply]
  have hbnorm : (kernel F).map b.toMonoidHom = kernel F := by
    rw [←hmap,map_map,hcomp,←map_map,hnorm]
  have hb : b^2=1 := by dsimp only [b]; rw [←map_pow,ha,map_one]
  have hbo : ¬∃g,b=MulAut.conj g := fun h => houter ((MulAut.congr_inner_iff eG a).mp h)
  let eP : P ≃* kernel F := (eG.subgroupMap (P:Subgroup (Group F))).trans (MulEquiv.subgroupCongr hmap)
  let ef : {u : P // a u = u} ≃ {u : kernel F // b u = u} :=
    eP.toEquiv.subtypeEquiv (fun u => by
      change a u = u ↔ eG (a (eG.symm (eG u))) = eG u
      rw [eG.symm_apply_apply]
      exact eG.injective.eq_iff.symm)
  rw [Nat.card_congr ef,Nat.card_congr eP.toEquiv]
  exact fixed_card_sq b hbnorm hb hbo
theorem sylow_fixed_card_sq_of_equiv {K : Type*} [_root_.Group K]
    (e : K ≃* Group F) (P : Sylow 2 K) (a : MulAut K)
    (hnorm : (P : Subgroup K).map a.toMonoidHom = P)
    (ha : a ^ 2 = 1) (houter : ¬ ∃ g : K, a = MulAut.conj g) :
    Nat.card {u : P // a u = u} ^ 2 = Nat.card P := by
  let : Finite K := Finite.of_injective e e.injective
  let P' : Sylow 2 (Group F) := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let b := MulAut.congr e a
  have hcomp : b.toMonoidHom.comp e.toMonoidHom = e.toMonoidHom.comp a.toMonoidHom := by
    ext x
    change e (a (e.symm (e x)))=e (a x)
    rw [e.symm_apply_apply]
  have hbnorm : (P' : Subgroup (Group F)).map b.toMonoidHom = P' := by
    change ((P : Subgroup K).map e.toMonoidHom).map b.toMonoidHom = (P : Subgroup K).map e.toMonoidHom
    rw [map_map,hcomp,←map_map,hnorm]
  have hb : b^2=1 := by dsimp only [b]; rw [←map_pow,ha,map_one]
  have hbo : ¬∃g,b=MulAut.conj g := fun h => houter ((MulAut.congr_inner_iff e a).mp h)
  let eP : P ≃* P' := e.subgroupMap (P : Subgroup K)
  let ef : {u : P // a u = u} ≃ {u : P' // b u = u} :=
    eP.toEquiv.subtypeEquiv (fun u => by
      change a u = u ↔ e (a (e.symm (e u))) = e u
      rw [e.symm_apply_apply]
      exact e.injective.eq_iff.symm)
  rw [Nat.card_congr ef,Nat.card_congr eP.toEquiv]
  exact sylow_fixed_card_sq P' b hbnorm hb hbo
end Theory.PSL2.RootSemilinear
