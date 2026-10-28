module

public import CFSG.Quasithin.Chapter3.Section02.Setup
public import CFSG.Quasithin.ChapterD.Section03.InternalSetup
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.GroupTheory.PResidual.ConjugateGeneration
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# The original FSU actor inside its normalizer

The local C-component restricts to L₀ and then embeds into M=N_G(L₀),
where L₀ is normal. This preserves the actual C-component and its intrinsic
quasisimple two-core quotient. Its original T-orbit is exactly L₀ inside
M. Perfectness of the local component identifies L₀ with the embedded
two-residual of L₀T, so L₀ is two-perfect.

These facts supply the actor alternative and residual hypothesis of D.3.2
from the actual FSU, without retaining either as a new assumption.
Source: Aschbacher–Smith, Hypothesis 3.2.1 and Lemmas 3.2.2–3.2.3,
combined manuscript of 1 March 2004, printed pp.579–580.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter3.Section02.FundamentalSetup
open ChapterD.Section03
universe u
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
  {T : Sylow 2 G} {L : Subgroup G} (D : FundamentalSetup K T L)

/-- The original Sylow subgroup, viewed inside M=N_G(L₀). -/
abbrev ambientSylow : Sylow 2 D.maximalLocal :=
  T.subtype (show (T : Subgroup G) ≤ D.maximalLocal from le_normalizer_componentOrbit L T)

instance orbit_normal_in_maximalLocal :
    ((localOrbit T L).subgroupOf D.maximalLocal).Normal := by
  exact normal_in_normalizer

private theorem perfect_twoPerfect {A : Type*} [Group A] [Finite A]
    [Group.IsPerfect A] : IsPPerfect 2 A := by
  intro N hN hp
  let := hN
  by_contra hne
  let : Nontrivial (A ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  let : Group.IsNilpotent (A ⧸ N) := hp.isNilpotent
  exact Group.IsPerfect.not_isSolvable (A ⧸ N) inferInstance

/-- The local component is still a genuine C-component in M. -/
theorem component_in_maximalLocal : (L.subgroupOf D.maximalLocal).IsCComponent := by
  let X := localOrbit T L
  let R := X.subgroupOf D.maximalLocal
  have hLX : L ≤ X := le_componentOrbit L T
  have hXM : X ≤ D.maximalLocal := X.le_normalizer
  have hcX : (L.subgroupOf X).IsCComponent :=
    D.maximal.1.1.subgroupOf_of_le hLX (componentOrbit_le_sup L T)
  let e : R ≃* X := subgroupOfEquivOfLe hXM
  have hc := (hcX.map_equiv e.symm).map_subtype
    (inferInstance : R.Normal).isSubnormal
  have he : ((L.subgroupOf X).map e.symm.toMonoidHom).map R.subtype =
      L.subgroupOf D.maximalLocal := by
    ext m
    constructor
    · rintro ⟨_, ⟨l, hl, rfl⟩, rfl⟩
      exact hl
    · intro hm
      exact ⟨e.symm ⟨m, hLX hm⟩, ⟨⟨m, hLX hm⟩, hm, rfl⟩, rfl⟩
  rwa [he] at hc

include D in
/-- The actor L₀ is two-perfect in its original intrinsic group. -/
theorem orbit_residual : pResidual 2 (localOrbit T L) = ⊤ := by
  let H := L ⊔ (T : Subgroup G)
  let A := L.subgroupOf H
  let S := (T : Subgroup G).subgroupOf H
  let : Group.IsPerfect A := D.maximal.1.1.perfect
  have hgen : A ⊔ S = ⊤ := by
    change L.subgroupOf H ⊔ (T : Subgroup G).subgroupOf H = ⊤
    rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  have hr := pResidual_eq_iSup_conjugates A S perfect_twoPerfect
    T.isPGroup'.comap_subtype hgen
  have hm : (pResidual 2 H).map H.subtype = localOrbit T L := by
    rw [hr]
    change (componentOrbit A S).map H.subtype = _
    rw [map_componentOrbit, map_subgroupOf_eq_of_le le_sup_left,
      map_subgroupOf_eq_of_le le_sup_right]
  apply (pResidual_eq_top_iff 2 (localOrbit T L)).mpr
  rw [← hm]
  exact isPPerfect_embedded_pResidual 2 H

/-- The actual actor and actual restricted Sylow satisfy the component
alternative of the internal D.3.2 setup. -/
theorem internal_actor_cases :
    InternalActorCases D.ambientSylow ((localOrbit T L).subgroupOf D.maximalLocal)
      (by rw [normalizer_eq_top]; exact le_top) := by
  have hLM : L ≤ D.maximalLocal := (le_componentOrbit L T).trans
    (localOrbit T L).le_normalizer
  let e := subgroupOfEquivOfLe hLM
  let q := e.toMonoidHom.pCoreQuotientEquiv (p := 2) e.surjective
    (by rw [e.toMonoidHom.ker_eq_bot e.injective]; exact IsPGroup.of_bot)
  let := D.quasisimple
  have hq : IsQuasisimple ((L.subgroupOf D.maximalLocal) ⧸
      pCore 2 (L.subgroupOf D.maximalLocal)) := IsQuasisimple.of_mulEquiv q.symm
  refine Or.inl ⟨L.subgroupOf D.maximalLocal, D.component_in_maximalLocal, hq, ?_⟩
  apply map_injective D.maximalLocal.subtype_injective
  rw [map_subgroupOf_eq_of_le (localOrbit T L).le_normalizer, map_componentOrbit,
    map_subgroupOf_eq_of_le hLM]
  change localOrbit T L = componentOrbit L
    (((T : Subgroup G).subgroupOf D.maximalLocal).map D.maximalLocal.subtype)
  rw [map_subgroupOf_eq_of_le (le_normalizer_componentOrbit L T)]

/-- The residual assertion in the precise subgroup type used by D.3.2. -/
theorem internal_actor_residual :
    pResidual 2 ((localOrbit T L).subgroupOf D.maximalLocal) = ⊤ := by
  apply (pResidual_eq_top_iff 2 _).mpr
  exact ((pResidual_eq_top_iff 2 _).mp D.orbit_residual).of_surjective
    (subgroupOfEquivOfLe (localOrbit T L).le_normalizer).symm.toMonoidHom
    (subgroupOfEquivOfLe (localOrbit T L).le_normalizer).symm.surjective

end CFSG.Quasithin.Chapter3.Section02.FundamentalSetup
