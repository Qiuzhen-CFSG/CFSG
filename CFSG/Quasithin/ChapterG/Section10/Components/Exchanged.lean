module
public import CFSG.Quasithin.ChapterG.Section10.Components.Containment
public import Theory.LinearAlgebra.BinaryHyperplaneTransvections
/-!
# Geometry of an exchanged normal-component constituent

An independent X-orbit of constituents of degree at least three has at most
two members. Indeed, a third member would make a second displacement injective
on I intersect v-perp, a space of dimension at least two, while the marked
transvection action forces its rank to be at most one.

For the selected constituent avoiding v, G.10.10 puts v in the two-summand
orbit. The diagonal map u ↦ u + rho(x)u identifies its marked half-point and
transfers the full transvection action to the stabilizer Y = N_X(I). This gives
I intersect W equal to the half-point line and the full center action on
I intersect v-perp. It does not identify the orbit span with V; the source
uses its subsequent non-GL assertion for that further conclusion.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), G.10.15(1)(ii),
printed pp.361--362, up to the use of part (3).
-/

@[expose] public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section10

/-- The geometric part of the exchanged constituent alternative, before
identifying its orbit span with the ambient module. -/
def ExchangedConstituentGeometry
    {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (B : LinearMap.BilinForm (ZMod 2) V)
    (v : V) (W : Submodule (ZMod 2) V) (X : Subgroup G)
    (I : Submodule (ZMod 2) V) : Prop :=
  ∃ x : X, I.map (ρ x) ≠ I ∧
    Homogeneous.orbitSpan ρ X I = I ⊔ I.map (ρ x) ∧
    Disjoint I (I.map (ρ x)) ∧ (subspaceStabilizer ρ I).relIndex X = 2 ∧
    let Y := (subspaceStabilizer ρ I).subgroupOf X
    let U := I ⊓ (B v).ker
    let aY := (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).toMonoidHom.comp
      (ρ.asGroupHom.comp (X.subtype.comp Y.subtype))
    ∃ i : U, (i : V) ≠ 0 ∧ v = (i : V) + ρ x i ∧
      I ⊓ W = Submodule.span (ZMod 2) {(i : V)} ∧
      BinaryTransvection.FullCenterAction aY U i

end CFSG.Quasithin.ChapterG.Section10

namespace CFSG.Quasithin.ChapterG.Section10.Hypothesis
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
 [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
 {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
 {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
 [IsElementaryAbelian 2 X] {X₀ : Subgroup X} (h : Hypothesis ρ B v W X X₀)
include h

omit h [Finite G] [IsElementaryAbelian 2 X] in
private theorem axis_intersection_dim (I : Submodule (ZMod 2) V)
 (hd : 3 ≤ finrank (ZMod 2) I) : 2 ≤ finrank (ZMod 2) (I ⊓ (B v).ker : Submodule (ZMod 2) V) := by
  let f := (B v).comp I.subtype
  have hf : f.ker.map I.subtype = I ⊓ (B v).ker := by
    rw [LinearMap.ker_comp,Submodule.map_comap_subtype]
  have he := f.finrank_range_add_finrank_ker
  have hr : finrank (ZMod 2) f.range ≤ 1 := by simpa using f.range.finrank_le
  have hk : finrank (ZMod 2) f.ker = finrank (ZMod 2) (I ⊓ (B v).ker : Submodule (ZMod 2) V) := by
    rw [← hf]
    exact (Submodule.equivMapOfInjective I.subtype I.subtype_injective f.ker).finrank_eq
  omega

/-- Independent constituent orbits have at most two members: on the axis,
the second displacement has rank at most one, whereas a third orbit member
would make it injective on a space of dimension at least two. -/
theorem independent_orbit_eq_self_or_moving
 (I : Submodule (ZMod 2) V) (hd : 3 ≤ finrank (ZMod 2) I)
 (hind : sSupIndep (subspaceOrbit ρ X I))
 (x : X) (hx : I.map (ρ x) ≠ I) (y : X) :
 I.map (ρ y) = I ∨ I.map (ρ y) = I.map (ρ x) := by
  classical
  by_contra hn
  have hy : I.map (ρ y) ≠ I := fun he => hn (.inl he)
  have hxy : I.map (ρ ((y : G)*(x : G))) ≠ I := by
    intro he
    apply hn
    right
    have hh := congrArg (fun J : Submodule (ZMod 2) V => J.map (ρ x)) he
    rw [← subspace_map_mul] at hh
    have heq : (x : G) * ((y : G)*(x : G)) = y := by
      have hc : (x : G)*(y : G)=(y : G)*(x : G) := congrArg Subtype.val (mul_comm x y)
      have hxx : (x : G)*(x : G)=1 := by
        simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p:=2) (x:G) x.2
      rw [← mul_assoc,hc,mul_assoc,hxx,mul_one]
    rw [heq] at hh
    exact hh
  let U := I ⊓ (B v).ker
  let d : U →ₗ[ZMod 2] W := ((ρ x - LinearMap.id).comp U.subtype).codRestrict W
    (fun u => h.displacement x u u.2.2)
  obtain ⟨f,_,hf⟩ := h.transvections y
  have hk : (f.comp d).ker ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by
    have hh : 2 ≤ finrank (ZMod 2) U := axis_intersection_dim (B:=B) (v:=v) I hd
    simpa only [Module.finrank_self] using (show 1 < finrank (ZMod 2) U by omega))
  obtain ⟨u,hu,hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  have hfix : ρ y (ρ x (u : V) - u) = ρ x (u : V) - u := by
    have he := hf (d u)
    have hz : f (d u) = 0 := hu
    change ρ y (ρ x (u : V) - u) = (ρ x (u : V) - u) + f (d u) • v at he
    simpa only [hz,zero_smul,add_zero] using he
  have hImem : I ∈ subspaceOrbit ρ X I := by
    refine ⟨1,?_⟩
    simp only [Subgroup.coe_one,map_one,Module.End.one_eq_id,Submodule.map_id]
  have hrest (a : G) (ha : a ∈ X) (hne : I.map (ρ a) ≠ I) :
      I.map (ρ a) ≤ sSup (subspaceOrbit ρ X I \ {I}) := le_sSup ⟨⟨⟨a,ha⟩,rfl⟩,hne⟩
  have hxu := hrest x x.2 hx (show ρ x (u:V) ∈ I.map (ρ x) from ⟨u,u.2.1,rfl⟩)
  have hyu := hrest y y.2 hy (show ρ y (u:V) ∈ I.map (ρ y) from ⟨u,u.2.1,rfl⟩)
  have hxyu := hrest ((y:G)*(x:G)) (X.mul_mem y.2 x.2) hxy
    (show ρ ((y:G)*(x:G)) (u:V) ∈ I.map (ρ ((y:G)*(x:G))) from ⟨u,u.2.1,rfl⟩)
  have huR : (u:V) ∈ sSup (subspaceOrbit ρ X I \ {I}) := by
    have he : (u:V) = ρ x (u:V) + ρ y (u:V) - ρ ((y:G)*(x:G)) (u:V) := by
      rw [map_sub,← Module.End.mul_apply,← map_mul] at hfix
      calc
        (u:V) = ρ x (u:V) - (ρ x (u:V) - u) := (sub_sub_cancel _ _).symm
        _ = ρ x (u:V) - (ρ ((y:G)*(x:G)) (u:V) - ρ y (u:V)) := by rw [hfix]
        _ = _ := by abel
    rw [he]
    exact (sSup (subspaceOrbit ρ X I \ {I})).sub_mem
      ((sSup (subspaceOrbit ρ X I \ {I})).add_mem hxu hyu) hxyu
  exact hu0 (Subtype.ext ((Submodule.disjoint_def.mp (hind hImem)) u u.2.1 huR))

/-- The selected exchanged orbit is exactly the direct sum of two translates. -/
theorem independent_orbit_pair
 (I : Submodule (ZMod 2) V) (hd : 3 ≤ finrank (ZMod 2) I)
 (hind : sSupIndep (subspaceOrbit ρ X I)) (x : X) (hx : I.map (ρ x) ≠ I) :
 Homogeneous.orbitSpan ρ X I = I ⊔ I.map (ρ x) ∧
 Disjoint I (I.map (ρ x)) ∧ (subspaceStabilizer ρ I).relIndex X = 2 := by
  have hImem : I ∈ subspaceOrbit ρ X I := by
    refine ⟨1,?_⟩
    simp only [Subgroup.coe_one,map_one,Module.End.one_eq_id,Submodule.map_id]
  refine ⟨le_antisymm (iSup_le fun y => ?_) (sup_le (Homogeneous.le_orbitSpan ρ X I)
    (le_iSup (fun y:X => I.map (ρ y)) x)),
    hind.pairwiseDisjoint hImem ⟨x,rfl⟩ hx.symm,?_⟩
  · rcases h.independent_orbit_eq_self_or_moving I hd hind x hx y with he | he
    · rw [he]; exact le_sup_left
    · rw [he]; exact le_sup_right
  · apply relIndex_eq_two_iff_exists_notMem_and.mpr
    refine ⟨x,x.2,(fun hh => hx ((subspace_map_eq_iff ρ I x).mpr hh)),?_⟩
    intro y hy
    rcases h.independent_orbit_eq_self_or_moving I hd hind x hx ⟨y,hy⟩ with he | he
    · exact Or.inr ((subspace_map_eq_iff ρ I y).mp he)
    · left
      apply (subspace_map_eq_iff ρ I (y*x)).mp
      have hh := congrArg (fun J : Submodule (ZMod 2) V => J.map (ρ x)) he
      rw [← subspace_map_mul,← subspace_map_mul] at hh
      have hxx : (x:G)*(x:G)=1 := by
        simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p:=2) (x:G) x.2
      have hxy : (x:G)*y=y*(x:G) := congrArg Subtype.val (mul_comm x (⟨y,hy⟩:X))
      simpa only [hxy,hxx,map_one,Module.End.one_eq_id,Submodule.map_id] using hh

omit h [Finite G] [IsElementaryAbelian 2 X] [FiniteDimensional (ZMod 2) V] in
private theorem binary_add_self (a : V) : a+a=0 := by
  calc
    a+a = (1:ZMod 2) • a + (1:ZMod 2) • a := by simp
    _ = ((1:ZMod 2)+1) • a := (add_smul _ _ _).symm
    _ = 0 := by rw [show (1:ZMod 2)+1=0 by decide,zero_smul]

/-- The marked point in an exchanged independent orbit has a nonzero
half-point in I∩W fixed by its stabilizer; the stabilizer induces the full
centered transvection group on I∩v-perp. -/
theorem exchanged_center_geometry
 (I : Submodule (ZMod 2) V) (hd : 3 ≤ finrank (ZMod 2) I)
 (hind : sSupIndep (subspaceOrbit ρ X I)) (x : X) (hx : I.map (ρ x) ≠ I)
 (hv : v ∈ Homogeneous.orbitSpan ρ X I) :
 let Y := (subspaceStabilizer ρ I).subgroupOf X
 let U := I ⊓ (B v).ker
 let aY := (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).toMonoidHom.comp
   (ρ.asGroupHom.comp (X.subtype.comp Y.subtype))
 ∃ i : U, (i : V) ∈ W ∧ (i : V) ≠ 0 ∧ v = (i:V)+ρ x i ∧
   BinaryTransvection.FullCenterAction aY U i := by
  let Y := (subspaceStabilizer ρ I).subgroupOf X
  let U := I ⊓ (B v).ker
  let d : I →ₗ[ZMod 2] V := I.subtype + (ρ x).comp I.subtype
  have hd_apply (u:I) : d u = (u:V)+ρ x u := rfl
  have hn (a:V) : -a=a := neg_eq_of_add_eq_zero_left (binary_add_self a)
  have hxx : (x:G)*(x:G)=1 := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p:=2) (x:G) x.2
  have hxxv (a:V) : ρ x (ρ x a)=a := by
    rw [← Module.End.mul_apply,← map_mul,hxx,map_one,Module.End.one_apply]
  obtain ⟨hop,hdis,_⟩ := h.independent_orbit_pair I hd hind x hx
  have hdinj : Function.Injective d := by
    apply LinearMap.ker_eq_bot.mp
    apply le_bot_iff.mp
    intro u hu
    apply Subtype.ext
    have he : (u:V) = -ρ x u := eq_neg_of_add_eq_zero_left hu
    exact Submodule.disjoint_def.mp hdis u u.2 ⟨-(u:V),I.neg_mem u.2,by simpa using he.symm⟩
  have hdx (u:I) : ρ x (d u)=d u := by
    rw [hd_apply,map_add,hxxv,add_comm]
  have hdc (y:X) (u:I) : ρ y (d u) = (ρ y u)+ρ x (ρ y u) := by
    rw [hd_apply,map_add]
    congr 1
    rw [← Module.End.mul_apply,← Module.End.mul_apply,← map_mul,← map_mul]
    exact congrArg (fun g:G => ρ g (u:V)) (congrArg Subtype.val (mul_comm y x))
  have hpair (y:X) : ∃ z:Y, ∀u:I, ρ ((z:X):G) (d u)=ρ y (d u) := by
    by_cases hy : (y:G) ∈ subspaceStabilizer ρ I
    · exact ⟨⟨y,hy⟩,fun _ => rfl⟩
    have he := (h.independent_orbit_eq_self_or_moving I hd hind x hx y).resolve_left
      (fun he => hy ((subspace_map_eq_iff ρ I y).mp he))
    have hyx : ((y*x:X):G) ∈ subspaceStabilizer ρ I := by
      apply (subspace_map_eq_iff ρ I _).mp
      have hh := congrArg (fun J:Submodule (ZMod 2) V => J.map (ρ x)) he
      rw [← subspace_map_mul,← subspace_map_mul] at hh
      have hc : (x:G)*(y:G)=(y:G)*(x:G) := congrArg Subtype.val (mul_comm x y)
      simpa only [Subgroup.coe_mul,hc,hxx,map_one,Module.End.one_eq_id,Submodule.map_id] using hh
    refine ⟨⟨y*x,hyx⟩,?_⟩
    intro u
    change ρ ((y:G)*(x:G)) (d u)=ρ y (d u)
    rw [map_mul,Module.End.mul_apply,hdx]
  have hvi : ∃ i:I, d i=v := by
    rw [hop] at hv
    obtain ⟨a,ha,b,hb,he⟩ := Submodule.mem_sup.mp hv
    obtain ⟨c,hc,rfl⟩ := hb
    have he' := congrArg (ρ x) he
    rw [map_add,hxxv,h.fixes_point x.2] at he'
    have hac : a-c = ρ x a-ρ x c :=
      sub_eq_sub_iff_add_eq_add.mpr (he.trans (by simpa only [add_comm] using he'.symm))
    have hac0 : a-c=0 := Submodule.disjoint_def.mp hdis (a-c) (I.sub_mem ha hc)
      ⟨a-c,I.sub_mem ha hc,by rw [map_sub,hac]⟩
    have hac' := sub_eq_zero.mp hac0
    exact ⟨⟨a,ha⟩,by simpa only [hd_apply,hac'] using he⟩
  obtain ⟨i,hiv⟩ := hvi
  have hi0 : (i:V) ≠ 0 := by
    intro hz
    have hi : i=0 := Subtype.ext hz
    exact h.point_ne_zero (by rw [← hiv,hi,map_zero])
  have hiz (z:Y) : ρ ((z:X):G) (i:V) = i := by
    have hm : ρ ((z:X):G) (i:V) ∈ I := (z.2 i).2 i.2
    apply congrArg Subtype.val (hdinj (a₁:=⟨ρ ((z:X):G) i,hm⟩) (a₂:=i) ?_)
    change ρ ((z:X):G) i+ρ x (ρ ((z:X):G) i)=d i
    rw [← hdc,hiv,h.fixes_point (z:X).2]
  let D : U →ₗ[ZMod 2] W := ((ρ x-LinearMap.id).comp U.subtype).codRestrict W
    (fun u => h.displacement x u u.2.2)
  have hD (u:U) : (D u:V)=d ⟨u,u.2.1⟩ := by
    change ρ x (u:V)-(u:V)=(u:V)+ρ x (u:V)
    rw [sub_eq_add_neg,hn,add_comm]
  have hDinj : Function.Injective D := by
    intro a b hab
    have he := congrArg Subtype.val hab
    rw [hD,hD] at he
    exact Subtype.ext (congrArg (fun z:I => (z:V)) (hdinj he))
  obtain ⟨u,hu⟩ : ∃u:U,(D u:V) ∉ Submodule.span (ZMod 2) {v} := by
    by_contra! hall
    have hle : LinearMap.range (W.subtype.comp D) ≤ Submodule.span (ZMod 2) {v} := by
      rintro _ ⟨u,rfl⟩; exact hall u
    have hr := Submodule.finrank_mono hle
    have hdU : 2 ≤ finrank (ZMod 2) U := axis_intersection_dim (B:=B) (v:=v) I hd
    have hdV : Function.Injective (W.subtype.comp D) := W.subtype_injective.comp hDinj
    rw [LinearMap.finrank_range_of_inj hdV] at hr
    have hs : finrank (ZMod 2) (Submodule.span (ZMod 2) {v}) ≤ 1 := by
      simpa using finrank_span_le_card ({v}:Set V)
    omega
  obtain ⟨f,hfu,hfk⟩ := (Submodule.span (ZMod 2) {v}).exists_le_ker_of_notMem hu
  have hfv := hfk (Submodule.mem_span_singleton_self v)
  obtain ⟨y,hy⟩ := h.full_transvections (f.comp W.subtype) hfv
  have hfu1 : f (D u:V)=1 := by
    have hb : ∀c:ZMod 2,c=0∨c=1 := by decide
    exact (hb _).resolve_left hfu
  have hyu : ρ y (D u:V)=(D u:V)+v := by
    have he := hy (D u)
    simpa only [LinearMap.comp_apply,Submodule.subtype_apply,hfu1,one_smul] using he
  obtain ⟨z,hz⟩ := hpair y
  have hzI : ρ ((z:X):G) (u:V) ∈ I := (z.2 u).2 u.2.1
  have hzui : ρ ((z:X):G) (u:V)=(u:V)+i := by
    have he : d ⟨ρ ((z:X):G) u,hzI⟩=d (⟨u,u.2.1⟩+i) := by
      rw [map_add,hiv]
      change ρ ((z:X):G) (u:V)+ρ x (ρ ((z:X):G) u)=d ⟨u,u.2.1⟩+v
      rw [← hdc (z:X) (⟨u,u.2.1⟩:I),hz,← hD,hyu]
    exact congrArg Subtype.val (hdinj he)
  have hiW : (i:V) ∈ W := by
    have he := h.displacement (z:X) u u.2.2
    rwa [hzui,add_sub_cancel_left] at he
  have hiU : (i:V) ∈ U := ⟨i.2,h.isotropic v h.point_mem i hiW⟩
  refine ⟨⟨i,hiU⟩,hiW,hi0,hiv.symm,hi0,?_,?_,?_⟩
  · exact hiz
  · intro z w
    obtain ⟨f,_,hf⟩ := h.transvections (z:X)
    have hm : ρ ((z:X):G) (w:V) ∈ I := (z.2 w).2 w.2.1
    have he : d ⟨ρ ((z:X):G) w,hm⟩=d (⟨w,w.2.1⟩+f (D w) • i) := by
      rw [map_add,map_smul,hiv]
      change ρ ((z:X):G) (w:V)+ρ x (ρ ((z:X):G) w)=d ⟨w,w.2.1⟩+f (D w) • v
      rw [← hdc (z:X) (⟨w,w.2.1⟩:I),← hD]
      exact hf (D w)
    have he' := congrArg (fun a:I => (a:V)) (hdinj he)
    change ρ ((z:X):G) (w:V) = (w:V) + f (D w) • (i:V) at he'
    change ρ ((z:X):G) (w:V)-(w:V) ∈ Submodule.span (ZMod 2) {(i:V)}
    rw [he',add_sub_cancel_left]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · intro φ hφ
    obtain ⟨ψ,hψ⟩ := (LinearMap.dualMap_surjective_of_injective hDinj) φ
    have hψv : ψ ⟨v,h.point_mem⟩=0 := by
      have he := LinearMap.congr_fun hψ (⟨i,hiU⟩:U)
      have hDi : D (⟨i,hiU⟩:U)=⟨v,h.point_mem⟩ := Subtype.ext ((hD _).trans hiv)
      change ψ (D ⟨i,hiU⟩)=φ ⟨i,hiU⟩ at he
      rw [hDi,hφ] at he
      exact he
    obtain ⟨y,hy⟩ := h.full_transvections ψ hψv
    obtain ⟨z,hz⟩ := hpair y
    refine ⟨z,?_⟩
    intro w
    have hm : ρ ((z:X):G) (w:V) ∈ I := (z.2 w).2 w.2.1
    have he : d ⟨ρ ((z:X):G) w,hm⟩=d (⟨w,w.2.1⟩+φ w • i) := by
      rw [map_add,map_smul,hiv]
      change ρ ((z:X):G) (w:V)+ρ x (ρ ((z:X):G) w)=d ⟨w,w.2.1⟩+φ w • v
      rw [← hdc (z:X) (⟨w,w.2.1⟩:I),hz,← hD,hy]
      exact congrArg (fun a:ZMod 2 => (D w:V)+a • v) (LinearMap.congr_fun hψ w)
    exact congrArg (fun a:I => (a:V)) (hdinj he)
/-- G.10.15(1)(ii), up to its later non-GL argument: an exchanged
homogeneous constituent has exactly two orbit summands and a full center
action about the half-point on its intersection with the marked axis. -/
theorem exchanged_constituent_geometry (hn : ¬ Group.IsSolvable G)
    {L : Subgroup G} (hL : IsComponent G L) (hm : ⁅L,X⁆ ≠ ⊥)
    (S : Sylow 2 G) (hnX : (S : Subgroup G) ≤ normalizer (X : Set G))
    (hind : (normalizer (L : Set G)).index ≤ 2)
    {I : Submodule (ZMod 2) V}
    (hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit L ⊤) X I)
    (hv : v ∉ I) : ExchangedConstituentGeometry ρ B v W X I := by
  let H := componentOrbit L ⊤
  let := componentOrbit_top_normal L
  let : Group.IsPerfect H := hL.orbit_isPerfect ⊤
  have hi := h.irreducible_of_not_solvable hn
  have hfix := fixedSpace_eq_bot_of_normal_faithful_irreducible ρ h.faithful hi H
    hL.componentOrbit_top_ne_bot
  have horb := hI.independent_orbit_of_fixedSpace_eq_bot ρ hfix
  have hd : 3 ≤ finrank (ZMod 2) I := hI.isIrrPlus.finrank_gt_two ρ H
  have hnot : ¬ X ≤ subspaceStabilizer ρ I := fun hx => hv
    ((h.point_mem_iff_stabilizes_component_constituent hn hL hm S hnX hind hI.isIrrPlus).mpr hx)
  obtain ⟨x,hxX,hx⟩ := SetLike.not_le_iff_exists.mp hnot
  have hxm : I.map (ρ x) ≠ I := fun he => hx ((subspace_map_eq_iff ρ I x).mp he)
  have hvo := h.point_mem_normal_component_subspace hn hL hm S hnX hind
    (Homogeneous.orbitSpan ρ X I)
    (Homogeneous.orbitSpan_component_invariant ρ hI.normalizes hI.isIrrPlus)
    (Homogeneous.orbitSpan_invariant ρ X I) (Homogeneous.orbitSpan_ne_bot ρ hI.isIrrPlus)
  obtain ⟨hop,hdis,hindex⟩ := h.independent_orbit_pair I hd horb ⟨x,hxX⟩ hxm
  obtain ⟨i,hiW,hi0,hvi,hcenter⟩ := h.exchanged_center_geometry I hd horb ⟨x,hxX⟩ hxm hvo
  refine ⟨⟨x,hxX⟩,hxm,hop,hdis,hindex,i,hi0,hvi,?_,hcenter⟩
  have hle : Submodule.span (ZMod 2) {(i:V)} ≤ I ⊓ W :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr ⟨i.property.1,hiW⟩
  symm
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hu := h.constituent_inter_W_finrank_le_one hi H hI.isIrrPlus hv
  have hl := Submodule.finrank_mono hle
  rw [finrank_span_singleton hi0] at hl ⊢
  omega

end CFSG.Quasithin.ChapterG.Section10.Hypothesis
