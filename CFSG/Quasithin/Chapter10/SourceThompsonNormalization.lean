module

public import CFSG.Quasithin.Chapter3.Section02.FundamentalActor
public import CFSG.Quasithin.ChapterB.Section01.ComponentNormalization.Thompson
public import Theory.GroupTheory.ReducedNormal.OrbitReduced
public import Stellmacher.ElementaryAbelianMaxJMap

/-!
# Original Chapter 10 Thompson normalization

Use the original module V inside H=L₀T. It is elementary and normal in H,
and O₂(H) centralizes it. The homogeneous Irr⁺ seed ensures the actual actor
L₀ has nontrivial image, hence the seed component L survives as well.
The best-offender component-normalization theorem then proves J(T) ≤ N_G(L),
with the literal Sylow subgroup and original component preserved.

No earlier classification or chosen module marking is an additional premise.
Source: Aschbacher–Smith, 10.1.2(2), printed p.741, using Hypothesis 3.2.1
and B.1.5(4) in the combined manuscript of 1 March 2004.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter3.Section02.FundamentalSetup
open Representation.BinaryOffender.Homogeneous
universe u
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
  {T : Sylow 2 G} {L : Subgroup G} (D : FundamentalSetup K T L)

include D in
/-- Original source 10.1.2(2): J(T) normalizes the actual FSU component L.
Every module, image-survival and two-core premise is derived from the FSU. -/
theorem thompson_normalizes_component :
    elementaryAbelianMaxJ (T : Subgroup G) ≤ normalizer (L : Set G) := by
  let H := localJoin T L
  let X := (localOrbit T L).subgroupOf H
  let B := L.subgroupOf H
  let V := D.moduleSubgroup.subgroupOf H
  let S := (T : Subgroup G).subgroupOf H
  have hLH : L ≤ H := (le_componentOrbit L T).trans le_sup_left
  have hVH : D.moduleSubgroup ≤ H := D.module_le_sylow.trans le_sup_right
  let : V.Normal := normal_subgroupOf_of_le_normalizer D.join_normalizes_module
  let := D.module_elementary
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.subgroupOf hVH
  let C := centralizer (V : Set H)
  let q := QuotientGroup.mk' C
  have hk : q.ker = centralizer (V : Set H) := QuotientGroup.ker_mk' C
  have hB : B.IsCComponent := by
    change (L.subgroupOf (componentOrbit L (T : Subgroup G) ⊔ (T : Subgroup G))).IsCComponent
    rw [componentOrbit_sup]
    exact D.maximal.1.1
  let e := subgroupOfEquivOfLe hLH
  let eqt := e.toMonoidHom.pCoreQuotientEquiv (p := 2) e.surjective
    (by rw [e.toMonoidHom.ker_eq_bot e.injective]; exact IsPGroup.of_bot)
  let := D.quasisimple
  have hBq : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv eqt.symm
  have hc : pCore 2 H ≤ q.ker := by
    rw [hk]
    intro x hx v hv
    exact Subtype.ext (D.core_centralizes_module (mem_map_of_mem H.subtype hx) v hv)
  have hXorbit : X = componentOrbit B S := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le (show localOrbit T L ≤ H from le_sup_left),
      map_componentOrbit, map_subgroupOf_eq_of_le hLH,
      map_subgroupOf_eq_of_le le_sup_right]
  have hXne : X.map q ≠ ⊥ := by
    intro hz
    have hXC := (map_eq_bot_iff X).mp hz
    apply D.homogeneous.isIrrPlus.not_le_fixedSpace
      (ReducedNormal.representation H)
    intro w hw x
    have hxC : (x : H) ∈ C := by
      change (x : H) ∈ centralizer (V : Set H)
      rw [← hk]
      exact hXC x.property
    have hxambient : ((x : H) : G) ∈ centralizer (D.seed : Set G) := by
      intro v hv
      have hvV : v ∈ D.moduleSubgroup := le_componentOrbit D.seed T hv
      have hh := hxC ⟨v, hVH hvV⟩ hvV
      exact congrArg H.subtype hh
    exact ReducedNormal.representation_fixes_of_centralizes_subspaceImage H
      D.seedSpace (x : H) hxambient w hw
  have hBne : B.map q ≠ ⊥ :=
    componentOrbit_map_seed_ne_bot B S q (hXorbit ▸ hXne)
  have hn := ChapterB.thompson_normalizes_surviving_cComponent V S B
    (fun _ hv => D.module_le_sylow hv) hB hBq q (QuotientGroup.mk'_surjective C)
    hk hc hBne
  have hjmap : (elementaryAbelianMaxJ S).map H.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective]
    congr 1
    exact map_subgroupOf_eq_of_le le_sup_right
  rw [← hjmap]
  have hh := (map_mono hn).trans (B.le_normalizer_map H.subtype)
  rwa [map_subgroupOf_eq_of_le hLH] at hh
end CFSG.Quasithin.Chapter3.Section02.FundamentalSetup
