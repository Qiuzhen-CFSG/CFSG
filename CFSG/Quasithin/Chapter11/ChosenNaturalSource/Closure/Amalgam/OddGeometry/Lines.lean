module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.OddGeometry.Endpoints
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PGroup.NormalChain
public import Theory.GroupTheory.PGroup.Subnormal

/-!
# Disjoint field lines at an odd critical pair

A nonzero point in both field lines identifies their point closures using
L-transitivity and the preceding 11.4.2 comparison. If the two components
coincided, U=⟨V^(KT)⟩ would be normalized by the opposite vertex's actual
two-residual K^g. A two-subgroup normalized by O²(H) is subnormal in H,
hence lies in O₂(H). This contradicts the critical seed's escape.

The residual calculation uses perfectness of L₁ and its conjugate span K,
relative normality in KT, and the original Sylow. No ambient normality or
identification of O² with O₂ is used. PointClosures retains the preceding
point comparison and its Cartan transport; the source assembly owns them.
Source: Aschbacher--Smith 11.4.2 and 11.5.8, printed pp.776--777,784.
-/

@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.OddGeometry
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterF.Section07
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] [Finite G]

private theorem le_core_of_residual_normalizes (A : Subgroup G) (hp : IsPGroup 2 A)
    (hn : pResidual 2 G ≤ normalizer (A : Set G)) : A ≤ pCore 2 G := by
  let q := QuotientGroup.mk' (pResidual 2 G)
  let N := normalizer (A : Set G)
  have hN : N.IsSubnormal := by
    have hh := (isPGroup_quotient_pResidual (G := G) 2).subgroup_isSubnormal (N.map q)
    have he : (N.map q).comap q = N := by
      rw [comap_map_eq_self]
      simpa only [q,QuotientGroup.ker_mk'] using hn
    exact he ▸ hh.comap q
  have hA : A.IsSubnormal := .step A N A.le_normalizer hN inferInstance
  have he := isPGroup_le_pCoreAmbient_of_isSubnormalIn (⊤ : Subgroup G) A 2 le_top
    hA.subgroupOf hp
  change A ≤ (pCore 2 (⊤ : Subgroup G)).map Subgroup.topEquiv.toMonoidHom at he
  rwa [pCore_map_iso] at he

/-- A two-subgroup normalized by the literal residual of H lies in its core. -/
private theorem le_core_of_embedded_residual_normalizes (H A : Subgroup G)
    (hAH : A ≤ H) (hp : IsPGroup 2 A)
    (hn : (pResidual 2 H).map H.subtype ≤ normalizer (A : Set G)) : A ≤ H.pCoreIn 2 := by
  have hnorm : pResidual 2 H ≤ normalizer (A.subgroupOf H : Set H) := by
    intro r hr
    apply mem_normalizer_iff.mpr
    intro a
    exact mem_normalizer_iff.mp (hn (mem_map_of_mem H.subtype hr)) a
  have hh := le_core_of_residual_normalizes (A.subgroupOf H) hp.comap_subtype hnorm
  have hm := map_mono (f := H.subtype) hh
  rwa [map_subgroupOf_eq_of_le hAH] at hm

variable {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Closure.Geometry D)

/-- KT has the source residual K; no relative core is substituted for O². -/
theorem residual_KT (h : LocalInputs E) :
    (pResidual 2 (KT E)).map (KT E).subtype = E.K := by
  let : Group.IsPerfect E.L₁ := by
    change Group.IsPerfect ((solvableResidual (L ⊓ E.G₁ : Subgroup G)).map (L ⊓ E.G₁).subtype)
    let e := (solvableResidual (L ⊓ E.G₁ : Subgroup G)).equivMapOfInjective
      (L ⊓ E.G₁).subtype (L ⊓ E.G₁).subtype_injective
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let : Group.IsPerfect E.K := conjugateSpanBy_isPerfect E.L₁ E.G₁
  have hp : IsPPerfect 2 E.K := by
    intro N hN hq
    let := hN
    let : Group.IsNilpotent (E.K ⧸ N) := hq.isNilpotent
    exact top_le_iff.mp (by
      rw [←solvableResidual_eq_top (G := E.K)]
      exact solvableResidual_le_of_solvable_quotient N)
  exact embedded_pResidual_join_pGroup E.K (T : Subgroup G) hp T.isPGroup'
    (h.point_invariant.trans E.G₁_normalizes_K)

/-- The point-closure formulation of preceding 11.4.2, after the source
Cartan transports its central involution to every nonzero point of V₁.
The original comparison and point-Cartan orbit supply this via
`pointClosures_of_comparison`. -/
def PointClosures : Prop := ∀ u ∈ E.V₁, u ≠ 1 → pointClosure L u = E.K

/-- Transport the literal 11.4.2 comparison at the original chosen z along
its point-Cartan orbit. Both L and K are preserved by the same transporter. -/
theorem pointClosures_of_comparison
    (hres : pointResidual L E.z = E.L₁) (hcomp : E.Kz = E.K)
    (horbit : ∀ u ∈ E.V₁, u ≠ 1 → ∃ x ∈ L ⊓ E.G₁, (MulAut.conj x) E.z = u) :
    PointClosures E := by
  intro u hu hu1
  obtain ⟨x,hx,hxu⟩ := horbit u hu hu1
  have hL : L.map (MulAut.conj x).toMonoidHom = L :=
    mem_normalizer_iff_map_conj_eq.mp (L.le_normalizer hx.1)
  have hK : E.K.map (MulAut.conj x).toMonoidHom = E.K :=
    mem_normalizer_iff_map_conj_eq.mp (E.G₁_normalizes_K hx.2)
  have hm := pointClosure_map L E.z (MulAut.conj x)
  change (pointClosure L E.z).map (MulAut.conj x).toMonoidHom =
    pointClosure (L.map (MulAut.conj x).toMonoidHom) ((MulAut.conj x) E.z) at hm
  rw [E.pointClosure_eq_K hres hcomp,hxu,hL,hK] at hm
  exact hm.symm

/-- A common nonzero point identifies the two literal conjugate-generated
components. The adjustment of the seed uses actual L-transitivity. -/
theorem component_eq_of_lines_meet (hp : PointClosures E)
    (ht : ∀ u ∈ V, u ≠ 1 → ∀ v ∈ V, v ≠ 1 → ∃ l ∈ L, (MulAut.conj l) u = v)
    (g : G) (hi : E.V₁ ⊓ E.V₁.map (MulAut.conj g).toMonoidHom ≠ ⊥) :
    E.K.map (MulAut.conj g).toMonoidHom = E.K := by
  obtain ⟨u,hu,hu1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hi
  obtain ⟨v,hv,hvu⟩ := hu.2
  change (MulAut.conj g) v = u at hvu
  have hv1 : v ≠ 1 := by
    intro he
    exact hu1 (by simpa only [he,map_one] using hvu.symm)
  have hpu := hp u hu.1 hu1
  have hpv := hp v hv hv1
  have hh := pointClosure_eq_of_common_point L V ht u g (E.V₁_le hu.1) hu1
    (map_mono E.V₁_le hu.2)
  have he := pointClosure_map L v (MulAut.conj g)
  rw [hpv,hvu,hh,hpu] at he
  exact he

namespace Endpoint
variable {E} {h : LocalInputs E} {hout : ¬ E.K ≤ E.M}
  (i : Endpoint E h hout)

/-- If the two components coincided, U would be a two-subgroup of the
opposite vertex normalized by its two-residual, contradicting criticality. -/
theorem component_ne (hab : IsMulCommutative E.W) (hb : 3 ≤ distance E h hout) :
    E.K.map (MulAut.conj ((i : generated E) : G)).toMonoidHom ≠ E.K := by
  intro he
  have hU : localClosure E ≤
      (KT E).map (MulAut.conj ((i : generated E) : G)).toMonoidHom := by
    have hm := map_mono (f := (generated E).subtype) (i.reverse_module_le hb)
    change moduleAt E h hout (base (family E) true) ≤ actor E i.vertex at hm
    simpa only [moduleAt_base,CriticalPairs.NormalizedEndpoint.vertex,
      actor_translate,actor_base,if_true] using hm
  have hr : (pResidual 2 ((KT E).map (MulAut.conj ((i : generated E) : G)).toMonoidHom)).map
      ((KT E).map (MulAut.conj ((i : generated E) : G)).toMonoidHom).subtype = E.K := by
    rw [←map_embedded_pResidual,residual_KT E h,he]
  have hn : (pResidual 2 ((KT E).map (MulAut.conj ((i : generated E) : G)).toMonoidHom)).map
      ((KT E).map (MulAut.conj ((i : generated E) : G)).toMonoidHom).subtype ≤
        normalizer (localClosure E : Set G) := by
    rw [hr]
    exact (le_sup_left : E.K ≤ KT E).trans (le_normalizer_conjugateSpanBy V (KT E))
  let := localClosure_elementary E h hab
  have hc := le_core_of_embedded_residual_normalizes _ _ hU
    (IsElementaryAbelian.isPGroup 2 (localClosure E)) hn
  exact i.seed_not_core ((le_conjugateSpanBy V (KT E)).trans hc)

/-- The two source field lines are disjoint, with no equality of arbitrary
binary subspaces substituted for the point-closure comparison. -/
theorem lines_disjoint (hab : IsMulCommutative E.W) (hb : 3 ≤ distance E h hout)
    (hp : PointClosures E)
    (ht : ∀ u ∈ V, u ≠ 1 → ∀ v ∈ V, v ≠ 1 → ∃ l ∈ L, (MulAut.conj l) u = v) :
    E.V₁ ⊓ E.V₁.map (MulAut.conj ((i : generated E) : G)).toMonoidHom = ⊥ := by
  by_contra hi
  exact i.component_ne hab hb (component_eq_of_lines_meet E hp ht _ hi)

end Endpoint


end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.OddGeometry
