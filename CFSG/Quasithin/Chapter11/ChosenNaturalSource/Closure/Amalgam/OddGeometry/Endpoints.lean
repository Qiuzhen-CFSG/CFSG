module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Centralization
public import CFSG.Quasithin.ChapterF.Section07.CriticalPairs.Endpoints

/-!
# The actual odd endpoint and both index-two bounds

Normalize an odd F.7 critical endpoint and map its vertex groups and neighbor
modules from ⟨LT,KT⟩ into the original ambient group. Both endpoint edge cores
are actual conjugates of R₁. The literal conclusion of 11.5.6(6), retained as
`RadicalCorank`, therefore bounds both U∩O₂((KT)^g) and U^g∩O₂(KT).
The seed escapes the opposite core because that core fixes the first ball.
The same normalized endpoint supplies mutual normalization of the closures.

Here U is ⟨V^(KT)⟩ throughout, rather than Geometry.U=⟨V₃^G₁⟩. This module
constructs the endpoint and index fields, not the remaining commutator fields
of OddPair. Source: Aschbacher--Smith 11.5.8, printed p.784, using F.7.11(5--6)
and 11.5.6(6), printed pp.313--314 and 780--781.
-/

@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.OddGeometry
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterF.Section07
open Subgroup.CosetGeometry.RankTwo
open Subgroup.CosetGeometry (stabilizer_base incident_base)
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Closure.Geometry D)

omit [Finite G] in
private theorem map_conj_subtype (H : Subgroup G) (A : Subgroup H) (g : H) :
    (A.map (MulAut.conj g).toMonoidHom).map H.subtype =
      (A.map H.subtype).map (MulAut.conj (g : G)).toMonoidHom := by
  rw [map_map, map_map]
  rfl

omit [Finite G] in
private theorem conjugate_cancel (A : Subgroup G) (g : G) :
    (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = A := by
  rw [map_map]
  have he : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id G := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [he, map_id]

/-- The vertex stabilizer embedded in the original ambient group. -/
def actor (v : Vertex (family E)) : Subgroup G :=
  (stabilizer (family E) v).map (generated E).subtype

/-- The actual F.7 neighbor module embedded in the original ambient group. -/
def moduleAt (h : LocalInputs E) (hout : ¬ E.K ≤ E.M)
    (v : Vertex (family E)) : Subgroup G :=
  (CriticalPairs.vertexModule (family E) (sourceSetup E h hout).seed v).map
    (generated E).subtype

theorem actor_base (i : Bool) : actor E (base (family E) i) =
    if i then KT E else LT E := by
  rw [actor, show stabilizer (family E) (base (family E) i) = family E i from
    stabilizer_base (family E) i]
  cases i
  · exact map_subgroupOf_eq_of_le (show LT E ≤ generated E from le_sup_left)
  · exact map_subgroupOf_eq_of_le (show KT E ≤ generated E from le_sup_right)

theorem actor_translate (g : generated E) (v : Vertex (family E)) :
    actor E (g • v) = (actor E v).map (MulAut.conj (g : G)).toMonoidHom := by
  rw [actor, stabilizer_translate, map_conj_subtype]
  rfl

theorem moduleAt_base (h : LocalInputs E) (hout : ¬ E.K ≤ E.M) :
    moduleAt E h hout (base (family E) true) = localClosure E :=
  secondModule_map E h hout

theorem moduleAt_translate (h : LocalInputs E) (hout : ¬ E.K ≤ E.M)
    (g : generated E) (v : Vertex (family E)) :
    moduleAt E h hout (g • v) =
      (moduleAt E h hout v).map (MulAut.conj (g : G)).toMonoidHom := by
  rw [moduleAt, CriticalPairs.vertexModule_translate _ _
    (sourceSetup E h hout).seed_normalized, map_conj_subtype]
  rfl

abbrev Endpoint (h : LocalInputs E) (hout : ¬ E.K ≤ E.M) :=
  CriticalPairs.NormalizedEndpoint (sourceSetup E h hout) (sourceV_ne_bot E h hout)

/-- The literal elementary-corank conclusion of 11.5.6(6) at H₁=KT. -/
def RadicalCorank : Prop := ∀ A : Subgroup G, IsElementaryAbelian 2 A → A ≤ E.R₁ →
  ChapterE.subgroupCorank A (A ⊓ (KT E).pCoreIn 2) ≤ 1

private theorem index_le_two_of_corank (A B : Subgroup G) [IsElementaryAbelian 2 A]
    (hc : ChapterE.subgroupCorank A B ≤ 1) : B.relIndex A ≤ 2 := by
  have he : B.relIndex A = 2 ^ ChapterE.subgroupCorank A B := by
    rw [ChapterE.subgroupCorank_eq_quotient_finrank]
    exact relIndex_eq_two_pow_quotient_finrank A B
  rw [he]
  exact (Nat.pow_le_pow_right (by decide : 0 < 2) hc).trans (by decide)

/-- Transport the original radical corank bound to any incident edge.
The map on its core is the very same map as that on the vertex group. -/
theorem edge_index (h : LocalInputs E) (hc : RadicalCorank E)
    {v w : Vertex (family E)} (hv : v.type = true) (hw : w.type = false)
    (hadj : (graph (family E)).Adj w v)
    (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : A ≤ (actor E w ⊓ actor E v).pCoreIn 2) :
    (A ⊓ (actor E v).pCoreIn 2).relIndex A ≤ 2 := by
  obtain ⟨g,hg₀,hg₁⟩ := incident_common_translate (family E) hadj.2
  rw [hw] at hg₀
  rw [hv] at hg₁
  have he : actor E w ⊓ actor E v =
      (E.L₁ ⊔ (T : Subgroup G)).map (MulAut.conj (g : G)).toMonoidHom := by
    rw [←hg₀,←hg₁,actor_translate,actor_translate,actor_base,actor_base]
    simp only [Bool.false_eq_true,if_false,if_true]
    rw [←map_inf _ _ _ (MulAut.conj (g : G)).injective,overlap E h]
  have hq : actor E v = (KT E).map (MulAut.conj (g : G)).toMonoidHom := by
    rw [←hg₁,actor_translate,actor_base]
    rfl
  let B := A.map (MulAut.conj (g : G)⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hBR : B ≤ E.R₁ := by
    rw [he,Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective _ _
      (MulAut.conj (g : G)).injective] at hA
    have hh := map_mono (f := (MulAut.conj (g : G)⁻¹).toMonoidHom) hA
    rwa [conjugate_cancel] at hh
  have hi := index_le_two_of_corank B (B ⊓ (KT E).pCoreIn 2) (hc B inferInstance hBR)
  have hB : B.map (MulAut.conj (g : G)).toMonoidHom = A := by
    simpa only [inv_inv] using conjugate_cancel A (g : G)⁻¹
  rw [←relIndex_map_map_of_injective _ _ (f := (MulAut.conj (g : G)).toMonoidHom)
      (MulAut.conj (g : G)).injective,
    map_inf _ _ _ (MulAut.conj (g : G)).injective,hB,
    ←Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective _ _
      (MulAut.conj (g : G)).injective,←hq] at hi
  exact hi

namespace Endpoint
variable {E} {h : LocalInputs E} {hout : ¬ E.K ≤ E.M}
  (i : Endpoint E h hout)

theorem seed_le_actor : V ≤ (KT E).map (MulAut.conj ((i : generated E) : G)).toMonoidHom := by
  have hm := map_mono (f := (generated E).subtype) i.seed_le_stabilizer
  rw [sourceSeed_map] at hm
  change V ≤ actor E i.vertex at hm
  simpa only [CriticalPairs.NormalizedEndpoint.vertex, actor_translate, actor_base,
    Bool.true_eq, if_true] using hm

theorem seed_not_core : ¬ V ≤
    ((KT E).map (MulAut.conj ((i : generated E) : G)).toMonoidHom).pCoreIn 2 := by
  intro hc
  apply i.property.2.2
  have hcore : (stabilizer (family E) i.vertex).pCoreIn 2 ≤
      ballKernel (family E) i.vertex 1 := by
    change (stabilizer (family E) ((i : generated E) • base (family E) true)).pCoreIn 2 ≤ _
    rw [stabilizer_translate,
      show stabilizer (family E) (base (family E) true) = family E true from
        stabilizer_base (family E) true, ballKernel_translate,
      Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective _ _
        (MulAut.conj (i : generated E)).injective]
    exact map_mono (CriticalPairs.Completion.base_core_le_kernel (family E)
      (sourceSetup E h hout) true)
  apply le_trans ?_ hcore
  apply (map_le_map_iff_of_injective (generated E).subtype_injective).mp
  rw [sourceSeed_map, ← Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective _ _
    (generated E).subtype_injective]
  change V ≤ (actor E i.vertex).pCoreIn 2
  simpa only [CriticalPairs.NormalizedEndpoint.vertex, actor_translate, actor_base,
    Bool.true_eq, if_true] using hc

theorem mutual_commutator (hb : 3 ≤ distance E h hout) :
    ⁅localClosure E, (localClosure E).map (MulAut.conj ((i : generated E) : G)).toMonoidHom⁆ ≤
      localClosure E ⊓ (localClosure E).map (MulAut.conj ((i : generated E) : G)).toMonoidHom := by
  have hm := map_mono (f := (generated E).subtype) (i.commutator_le hb)
  rw [map_commutator, map_inf _ _ _ (generated E).subtype_injective] at hm
  change ⁅moduleAt E h hout (base (family E) true), moduleAt E h hout i.vertex⁆ ≤
    moduleAt E h hout (base (family E) true) ⊓ moduleAt E h hout i.vertex at hm
  simpa only [CriticalPairs.NormalizedEndpoint.vertex, moduleAt_translate, moduleAt_base] using hm

/-- The second index bound, on the conjugate of ⟨V^(KT)⟩ itself. -/
theorem second_index (hab : IsMulCommutative E.W) (hb : 3 ≤ distance E h hout)
    (hc : RadicalCorank E) :
    (U₀ E ((i : generated E) : G)).relIndex
      ((localClosure E).map (MulAut.conj ((i : generated E) : G)).toMonoidHom) ≤ 2 := by
  let := localClosure_elementary E h hab
  let : IsElementaryAbelian 2
      ((localClosure E).map (MulAut.conj ((i : generated E) : G)).toMonoidHom) :=
    IsElementaryAbelian.map _
  obtain ⟨w,hw,hadj,hA⟩ := i.exists_base_edge hb
  have hm := map_mono (f := (generated E).subtype) hA
  rw [←Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective _ _
    (generated E).subtype_injective,map_inf _ _ _ (generated E).subtype_injective] at hm
  change moduleAt E h hout i.vertex ≤ (actor E (base (family E) true) ⊓ actor E w).pCoreIn 2 at hm
  rw [CriticalPairs.NormalizedEndpoint.vertex,moduleAt_translate,moduleAt_base] at hm
  have hi := edge_index E h hc rfl hw hadj.symm _ (by simpa only [inf_comm] using hm)
  simpa only [actor_base,if_true,U₀] using hi

/-- The reverse edge gives the first index bound with the original U carrier. -/
theorem first_index (hab : IsMulCommutative E.W) (hb : 3 ≤ distance E h hout)
    (hc : RadicalCorank E) :
    (U₁ E ((i : generated E) : G)).relIndex (localClosure E) ≤ 2 := by
  let := localClosure_elementary E h hab
  obtain ⟨w,hadj,hA⟩ := i.exists_opposite_edge hb
  have hw : w.type = false := by
    have ht := hadj.1
    change w.type ≠ true at ht
    cases hwt : w.type <;> simp_all
  have hm := map_mono (f := (generated E).subtype) hA
  rw [←Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective _ _
    (generated E).subtype_injective,map_inf _ _ _ (generated E).subtype_injective] at hm
  change moduleAt E h hout (base (family E) true) ≤
    (actor E w ⊓ actor E i.vertex).pCoreIn 2 at hm
  rw [moduleAt_base] at hm
  have hi := edge_index E h hc rfl hw hadj _ hm
  simpa only [CriticalPairs.NormalizedEndpoint.vertex,actor_translate,actor_base,if_true,U₁] using hi

end Endpoint
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.OddGeometry
