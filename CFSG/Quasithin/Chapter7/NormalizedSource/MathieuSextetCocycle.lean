module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSextetCocycle.Native

/-!
# Fixed cosets for the original Mathieu sextet residual

Conjugacy transports the checked native cocycle calculation to every sextet.
For a marked ambient cocode, displacement by an element fixing the point
residual descends through the literal component map: the full kernel lies in
the original module and centralizes that element. The resulting cocycle is
principal, giving a component-fixed representative in the same module coset.

NonFFSourceMathieuM24Extraspecial supplies the actual chosen-module action and
its complete kernel, then uses the trivial Sylow centralizer to obtain the
full-core center bound. No splitting or extension-classification callback is
assumed. Source: Aschbacher–Smith 8.2.12, printed p.722, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.OneCohomology
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open MathieuCode MathieuCode.CocodeOctad.Involutions MathieuCode.QuadraticActors
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSextet
set_option backward.isDefEq.respectTransparency false
namespace Cocycle
/-- The residual fixed-point obstruction vanishes for every actual native sextet. -/
theorem principal_of_residual (S : Sextet) (c : cocycles cocodeRepresentation)
    (hc : ∀ g ∈ (solvableResidual (sextetStabilizer S)).map
      (sextetStabilizer S).subtype, c.val g = 0) :
    ∃ v, principal cocodeRepresentation v = c := by
  obtain ⟨g,hg⟩ := SextetLayers.CoordinateTransport.exists_sextet_conjugator S
  have hS : Sporadic.Mathieu.M24LocalGeometry.Stabilizers.conjugateSextet g standardSextet = S := by
    cases S
    cases hg
    rfl
  let eG := MulAut.conj g
  let eV := LinearMap.GeneralLinearGroup.toLinearEquiv (cocodeRepresentation.asGroupHom g)
  have he (x : M24) (v : Cocode) : eV (cocodeRepresentation x v) =
      cocodeRepresentation (eG x) (eV v) := by
    change cocodeRepresentation g (cocodeRepresentation x v) =
      cocodeRepresentation (g*x*g⁻¹) (cocodeRepresentation g v)
    simp only [←Module.End.mul_apply,←map_mul,mul_assoc,inv_mul_cancel,mul_one]
  let e := cocyclesCongr cocodeRepresentation cocodeRepresentation eG eV he
  have hmap : (sextetStabilizer standardSextet).map eG.toMonoidHom = sextetStabilizer S := by
    rw [←hS,Sporadic.Mathieu.M24LocalGeometry.Stabilizers.conjugateSextet_stabilizer]
  let eH := (eG.subgroupMap (sextetStabilizer standardSextet)).trans (MulEquiv.subgroupCongr hmap)
  have hzero (x : M24) (hx : x ∈ (solvableResidual (sextetStabilizer standardSextet)).map
      (sextetStabilizer standardSextet).subtype) : (e.symm c).val x = 0 := by
    obtain ⟨r,hr,rfl⟩ := hx
    have hrS : eH r ∈ solvableResidual (sextetStabilizer S) := by
      rw [←map_solvableResidual_eq eH.toMonoidHom eH.surjective]
      exact mem_map_of_mem _ hr
    have hm : eG r.val ∈ (solvableResidual (sextetStabilizer S)).map (sextetStabilizer S).subtype :=
      mem_map_of_mem _ hrS
    change eV.symm (c.val (eG r.val)) = 0
    rw [hc _ hm,map_zero]
  obtain ⟨v,hv⟩ := principal_of_standard_residual (e.symm c) hzero
  refine ⟨eV v,?_⟩
  rw [←cocyclesCongr_principal cocodeRepresentation cocodeRepresentation eG eV he]
  exact (congrArg e hv).trans (e.apply_symm_apply c)

end Cocycle

open Chapter8.Section02.Centralizer
open scoped commutatorElement
variable {G : Type*} [Group G] [Finite G]

/-- An element fixing the original point residual has an L-fixed representative
in its original module coset. The actual action map and its full kernel are retained. -/
theorem residual_fixed_coset
    (W L : Subgroup G) [IsElementaryAbelian 2 W]
    (hLW : L ≤ normalizer (W : Set G))
    (q : L →* M24) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (hker : q.ker ≤ W.subgroupOf L)
    (F : Additive W ≃ₗ[ZMod 2] Cocode)
    (hF : ∀ (l : L) (w : W),
      F (Additive.ofMul (W.normalizerMonoidHom ⟨l,hLW l.property⟩ w)) =
        cocodeRepresentation (q l) (F (Additive.ofMul w)))
    (z : W) (S : Sextet) (hz : F (Additive.ofMul z) = sextetVector S)
    (d : G) (hd : ∀ l ∈ L, ⁅l,d⁆ ∈ W)
    (hWd : d ∈ centralizer (W : Set G))
    (hRd : d ∈ centralizer (localResidual L z : Set G)) :
    ∃ w ∈ W, w*d ∈ centralizer (L : Set G) := by
  let b (l : L) : W := ⟨⁅(l : G),d⁆,hd l l.property⟩
  let c : cocycles (cocodeRepresentation.comp q) := ⟨fun l => F (Additive.ofMul (b l)),by
    intro l m
    have he : b (l*m) = W.normalizerMonoidHom ⟨l,hLW l.property⟩ (b m) * b l := by
      apply Subtype.ext
      exact commutatorElement_mul_left_eq_conj_mul l.val m.val d
    change F (Additive.ofMul (b (l*m))) = _
    rw [he]
    change F (Additive.ofMul (W.normalizerMonoidHom ⟨l,hLW l.property⟩ (b m)) +
      Additive.ofMul (b l)) = _
    rw [map_add,hF]
    rfl⟩
  have hck (l : L) (hl : l ∈ q.ker) : c.val l = 0 := by
    have hb : b l = 1 := Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mpr (hWd l (hker hl)))
    change F (Additive.ofMul (b l)) = 0
    rw [hb]
    exact F.map_zero
  have heq {l m : L} (h : q l = q m) : c.val l = c.val m := by
    have hn : m⁻¹*l ∈ q.ker := by rw [MonoidHom.mem_ker,map_mul,map_inv,h,inv_mul_cancel]
    have hh := c.property m (m⁻¹*l)
    rw [mul_inv_cancel_left,hck _ hn,map_zero,zero_add] at hh
    exact hh
  let lift (x : M24) : L := (hq x).choose
  have hlift (x : M24) : q (lift x) = x := (hq x).choose_spec
  let c0 : cocycles cocodeRepresentation := ⟨fun x => c.val (lift x),by
    intro x y
    have hh := heq (show q (lift (x*y)) = q (lift x * lift y) by rw [map_mul,hlift,hlift,hlift])
    exact hh.trans (by simpa only [MonoidHom.comp_apply,hlift] using c.property (lift x) (lift y))⟩
  have hc0 (l : L) : c0.val (q l) = c.val l := heq (hlift (q l))
  obtain ⟨f,hf,hfk,hfval⟩ := marked_centralizer_action W L hLW q hq hk F hF z S hz
  obtain ⟨r,hr,_,_,hrval⟩ := marked_residual_core_action L z S f hf hfk
  have hzero (x : M24) (hx : x ∈ (solvableResidual (sextetStabilizer S)).map
      (sextetStabilizer S).subtype) : c0.val x = 0 := by
    obtain ⟨y,hy,rfl⟩ := hx
    obtain ⟨l,hl⟩ := (hr.ge hy : y ∈ r.range)
    have hval : q ⟨l,((localResidual_le L z).trans inf_le_left) l.property⟩ = y.val := by
      rw [←hl]
      exact ((congrArg Subtype.val (hrval l)).trans (hfval _)).symm
    change c0.val y.val = 0
    rw [←hval,hc0]
    have hb : b ⟨l,((localResidual_le L z).trans inf_le_left) l.property⟩ = 1 :=
      Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mpr (hRd l l.property))
    change F (Additive.ofMul (b _)) = 0
    rw [hb]
    exact F.map_zero
  obtain ⟨v,hv⟩ := Cocycle.principal_of_residual S c0 hzero
  let w : W := (F.symm v).toMul
  have hcomm (l : L) : ⁅(l : G),d⁆ = ⁅(l : G),(w : G)⁆ := by
    have hh := congrArg (fun t : cocycles cocodeRepresentation => t.val (q l)) hv
    rw [hc0] at hh
    have hw : F (Additive.ofMul w) = v := F.apply_symm_apply v
    have hval : F (Additive.ofMul (b l)) = F (Additive.ofMul
        (W.normalizerMonoidHom ⟨l,hLW l.property⟩ w * w⁻¹)) := by
      rw [ofMul_mul,ofMul_inv,←sub_eq_add_neg,map_sub,hF,hw]
      exact hh.symm
    exact congrArg (fun x : Additive W => (x.toMul : G)) (F.injective hval)
  refine ⟨(w : G)⁻¹,W.inv_mem w.property,?_⟩
  intro l hl
  have hh := hcomm ⟨l,hl⟩
  rw [commutatorElement_def,commutatorElement_def] at hh
  have he : l*d*l⁻¹ = (l*(w : G)*l⁻¹)*(w : G)⁻¹*d := mul_inv_eq_iff_eq_mul.mp hh
  apply mul_inv_eq_iff_eq_mul.mp
  calc
    l*((w : G)⁻¹*d)*l⁻¹ = (l*(w : G)*l⁻¹)⁻¹*(l*d*l⁻¹) := by group
    _ = (w : G)⁻¹*d := by rw [he]; group

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSextet
