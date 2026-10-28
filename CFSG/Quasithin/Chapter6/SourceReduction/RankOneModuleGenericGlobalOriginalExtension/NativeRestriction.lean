module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.Marked

/-!
# Restricting an original endpoint to its marked native base

Pulling a native endpoint back through an injective original endpoint map
constructs an actual subgroup equivalence. Exact residual markings likewise
restrict to the original selected factor, with an equation on every element.

For the right endpoint, the original normal layer R ∩ O₂(O²(H)) stays normal
when restricted to that base. Perfectness and the native core dichotomy then
exclude two noncentral layers, without removing outer automorphisms from the
whole endpoint. The adjacent unitary-four extension applies this transport to
both native parabolics; no R=O²(H), S=T, or ambient normality is assumed.

Source: Aschbacher--Smith F.1.12, pp.263--264, and the normal-layer comparison
in 5.2.6, pp.650--651 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
namespace OriginalExtension
variable {P X E : Type*} [Group P] [Group X] [Group E]

/-- Pull a native endpoint back through the original endpoint embedding. -/
private def baseEndpointEquiv (f : P →* E) (hf : Function.Injective f)
    (j : X →* E) (hj : Function.Injective j) (hb : j.range ≤ f.range) :
    j.range.comap f ≃* X :=
  ((j.range.comap f).equivMapOfInjective f hf).trans
    ((MulEquiv.subgroupCongr (by rw [map_comap_eq]; exact inf_eq_right.mpr hb)).trans
      (MonoidHom.ofInjective hj).symm)

end OriginalExtension

namespace Preparation
variable {G X E : Type*} [Group G] [Finite G] [Group X] [Group E]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)

/-- Restrict the same marked residual before removing any outer automorphisms. -/
def originalEndpointResidualEquiv (i : Fin 2)
    (f : ChapterF.Source.parabolic ![L,R] (sourceS L H) i →* E)
    (hf : Function.Injective f) (j : X →* E) (hj : Function.Injective j)
    (hr : (solvableResidual (ChapterF.Source.parabolic ![L,R] (sourceS L H) i)).map f =
      (solvableResidual X).map j) : ![L,R] i ≃* solvableResidual X := by
  let P := ChapterF.Source.parabolic ![L,R] (sourceS L H) i
  let a : ![L,R] i ≃* solvableResidual P :=
    (subgroupOfEquivOfLe (show ![L,R] i ≤ P from le_sup_left.trans le_sup_left)).symm.trans
      (MulEquiv.subgroupCongr (d.original_local_eq_residual h hTH hp i))
  exact a.trans (((solvableResidual P).equivMapOfInjective f hf).trans
    ((MulEquiv.subgroupCongr hr).trans ((solvableResidual X).equivMapOfInjective j hj).symm))

/-- The residual restriction commutes with the actual original and native
embeddings, on each original factor element. -/
theorem originalEndpointResidualEquiv_apply (i : Fin 2)
    (f : ChapterF.Source.parabolic ![L,R] (sourceS L H) i →* E)
    (hf : Function.Injective f) (j : X →* E) (hj : Function.Injective j)
    (hr : (solvableResidual (ChapterF.Source.parabolic ![L,R] (sourceS L H) i)).map f =
      (solvableResidual X).map j) (x : ![L,R] i) :
    j (d.originalEndpointResidualEquiv h hTH hp i f hf j hj hr x).val =
      f (inclusion (show ![L,R] i ≤ ChapterF.Source.parabolic ![L,R] (sourceS L H) i from
        le_sup_left.trans le_sup_left) x) := by
  exact congrArg Subtype.val
    (((solvableResidual X).equivMapOfInjective j hj).apply_symm_apply _)

include d h hp in
/-- A native base endpoint containing the marked right residual inherits the
original normal core layer. Its core dichotomy excludes that selected factor;
no equality between the full endpoint and its native base is needed. -/
theorem not_original_right_extension_of_core_dichotomy [Finite X]
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hl : NoncentralCoreLayer (((residual H).pCoreIn 2).subgroupOf R))
    (f : ChapterF.Source.parabolic ![L,R] (sourceS L H) 1 →* E)
    (hf : Function.Injective f) (j : X →* E) (hj : Function.Injective j)
    (hb : j.range ≤ f.range)
    (hr : (R.subgroupOf (ChapterF.Source.parabolic ![L,R] (sourceS L H) 1)).map f ≤ j.range)
    (hc : ∀ Q : Subgroup X, Q.Normal → Q ≤ pCore 2 X →
      ⁅Q,solvableResidual X⁆ = ⊥ ∨ Q = pCore 2 X) : False := by
  let := hp
  let P := ChapterF.Source.parabolic ![L,R] (sourceS L H) 1
  let N := ((residual H).pCoreIn 2).subgroupOf R
  have hRP : R ≤ P := le_sup_left.trans le_sup_left
  let r : R →* P := inclusion hRP
  have hnr : P ≤ normalizer (R : Set G) := by
    dsimp only [P]
    rw [d.parabolic_one h.sylow_normalizes]
    exact sup_le (sup_le R.le_normalizer d.S_normalizes_right) d.cartan_normalizes_right
  have hrr : r.range = R.subgroupOf P := inclusion_range hRP
  have hnormal : r.range.Normal := by
    rw [hrr]
    exact normal_subgroupOf_of_le_normalizer hnr
  have hnmap : N.map r = ((residual H).pCoreIn 2 ⊓ R).subgroupOf P := by
    apply map_injective P.subtype_injective
    rw [map_map,map_subgroupOf_eq_of_le (inf_le_right.trans hRP)]
    exact subgroupOf_map_subtype _ _
  have hn : (N.map r).Normal := by
    rw [hnmap]
    apply normal_subgroupOf_of_le_normalizer
    dsimp only [P]
    rw [d.parabolic_one h.sylow_normalizes]
    exact d.right_parabolic_normalizes_layer hN
  let D := j.range.comap f
  have hrD : r.range ≤ D := by
    rw [hrr]
    intro x hx
    exact hr (mem_map_of_mem f hx)
  let e := OriginalExtension.baseEndpointEquiv f hf j hj hb
  apply restrict_perfect_layer hl r (inclusion_injective _) hn hnormal D hrD
  intro Q hQ hle
  let := hQ
  let Q' := Q.map e.toMonoidHom
  have hn' : Q'.Normal := Normal.map hQ e.toMonoidHom e.surjective
  have hle' : Q' ≤ pCore 2 X := by
    rw [←pCore_map_iso 2 e]
    exact map_mono hle
  rcases hc Q' hn' hle' with hz | he
  · left
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_commutator,map_solvableResidual_eq e.toMonoidHom e.surjective,Subgroup.map_bot]
    exact hz
  · right
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [pCore_map_iso]
    exact he
end Preparation
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
