module

public import Theory.GroupTheory.WeakClosureSetFusion
public import Theory.GroupTheory.SubgroupConjugation
public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Fusion for a unique maximum-order abelian subgroup

Uniqueness among abelian subgroups of a Sylow group forces weak closure.
Burnside set fusion then transports conjugacy of subgroups in the abelian
subgroup to its actual normalizer. Cardinality and commutativity are carried
through the original conjugation map.
Source: Aschbacher, Sporadic Groups (1994),45.9,printed p246.
-/

public section
open Subgroup
namespace Sylow
variable {G:Type*} [Group G] [Finite G] {p:ℕ} [Fact p.Prime]
omit [Finite G] [Fact p.Prime] in
theorem weakly_closed_of_unique_maximum_abelian (T:Sylow p G) (V:Subgroup G)
    [IsMulCommutative V]
    (hmax:∀B:Subgroup G,IsMulCommutative B→B≤(T:Subgroup G)→Nat.card V≤Nat.card B→B=V) :
    ∀g:G,V.map (MulAut.conj g).toMonoidHom≤(T:Subgroup G)→g∈normalizer (V:Set G) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply hmax _ inferInstance hg
  rw [card_map_of_injective (MulAut.conj g).injective]

theorem subgroup_fusion_of_unique_maximum_abelian (T:Sylow p G) (V:Subgroup G)
    [IsMulCommutative V] (hVT:V≤(T:Subgroup G))
    (hmax:∀B:Subgroup G,IsMulCommutative B→B≤(T:Subgroup G)→Nat.card V≤Nat.card B→B=V)
    (B C:Subgroup G) (hBV:B≤V) (hCV:C≤V)
    (g:G) (hg:B.map (MulAut.conj g).toMonoidHom=C) :
    ∃n∈normalizer (V:Set G),B.map (MulAut.conj n).toMonoidHom=C := by
  have hn (B:Subgroup G) (hBV:B≤V):V≤normalizer (B:Set G):=
    (V.le_centralizer.trans (centralizer_le hBV)).trans (centralizer_le_normalizer _)
  obtain ⟨n,hnV,he⟩:=T.weakly_closed_normalizer_controls_set_fusion V hVT
    (T.weakly_closed_of_unique_maximum_abelian V hmax) (B:Set G) (C:Set G) (hn B hBV) (hn C hCV) g
    (congrArg (fun D:Subgroup G=>(D:Set G)) hg)
  exact ⟨n,hnV,SetLike.coe_injective he⟩
end Sylow
