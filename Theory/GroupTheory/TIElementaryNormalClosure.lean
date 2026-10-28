module
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Theory.GroupTheory.TINormalizerControl
public import Theory.GroupTheory.PCoreLocalSetup
public import Mathlib.GroupTheory.Commutator.Basic
/-!
# Elementary normal closure from the original TI hypothesis

An elementary subgroup V contained in a normal subgroup Q, and normalized
by Q, has commuting conjugates if distinct conjugates intersect trivially.
Indeed each conjugate is normal in Q, so mixed commutators lie in the
intersection. The normal closure is consequently elementary abelian.

The Sylow-overgroup application uses the original M and V: V≤O₂(M) and
V normal in T imply normalization by O₂(M). The resulting elementary normal
closure can be mapped through an actual quotient without assuming that TI
itself descends. This is the source-compatible reduction for the small odd
PSL₃ branch under Aschbacher–Smith E.2.8 and E.2.15, pp.222 and 228.
-/
public section
open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {G:Type*} [Group G]
/-- A TI elementary subgroup normalized by an ambient normal subgroup has
an elementary normal closure whenever it lies in that normal subgroup. -/
theorem elementary_normalClosure_of_ti {p:ℕ} (V Q:Subgroup G)
    [IsElementaryAbelian p V] [Q.Normal] (hVQ:V≤Q) (hQV:Q≤normalizer (V:Set G))
    (hTI:∀g:G,V⊓V.map (MulAut.conj g).toMonoidHom=⊥ ∨
      V.map (MulAut.conj g).toMonoidHom=V) :
    IsElementaryAbelian p (normalClosure (V:Set G)) := by
  have hcomm (g:G) : V.map (MulAut.conj g).toMonoidHom≤centralizer (V:Set G) := by
    rcases hTI g with hd|he
    · let W:=V.map (MulAut.conj g).toMonoidHom
      have hQg:Q.map (MulAut.conj g).toMonoidHom=Q :=
        normal_iff_map_conj_eq.mp (inferInstance:Q.Normal) g
      have hWQ:W≤Q := hQg ▸ map_mono hVQ
      have hQW:Q≤normalizer (W:Set G) := by
        rw [←hQg]
        exact (map_mono hQV).trans (le_normalizer_map _)
      have hc:⁅V,W⁆≤V⊓W := le_inf
        (le_normalizer_iff_commutator_le_left.mp (hWQ.trans hQV))
        (le_normalizer_iff_commutator_le_right.mp (hVQ.trans hQW))
      have hz:⁅V,W⁆=⊥ := le_bot_iff.mp (hd ▸ hc)
      exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz)
    · rw [he]
      exact le_centralizer_iff_isMulCommutative.mpr inferInstance
  let E:=normalClosure (V:Set G)
  have hEV:E≤centralizer (V:Set G) := by
    apply (closure_le _).mpr
    intro x hx
    obtain ⟨v,hv,hc⟩:=Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨g,rfl⟩:=isConj_iff.mp hc
    exact hcomm g (mem_map_of_mem (MulAut.conj g).toMonoidHom hv)
  have hVE:V≤centralizer (E:Set G) := le_centralizer_iff.mp hEV
  have hEE:E≤centralizer (E:Set G) := normalClosure_le_normal hVE
  let : IsMulCommutative E := le_centralizer_iff_isMulCommutative.mp hEE
  exact IsElementaryAbelian.normalClosure_of_isMulCommutative V

/-- The original elementary TI subgroup in a Sylow overgroup has elementary
normal closure inside that overgroup, before taking any source quotient. -/
theorem elementary_normalClosure_subgroupOf_ti [Finite G]
    (T:Sylow 2 G) (M V:Subgroup G) [IsElementaryAbelian 2 V]
    (hTM:(T:Subgroup G)≤M) (hVT:V≤T)
    (hn:(V.subgroupOf (T:Subgroup G)).Normal) (hVcore:V≤M.pCoreIn 2)
    (hTI:∀g∈M,V⊓V.map (MulAut.conj g).toMonoidHom=⊥ ∨
      V.map (MulAut.conj g).toMonoidHom=V) :
    IsElementaryAbelian 2 (normalClosure (V.subgroupOf M:Set M)) := by
  have hVM:V≤M := hVT.trans hTM
  let W:=V.subgroupOf M
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hVM
  have hWQ:W≤pCore 2 M := by
    intro v hv
    obtain ⟨q,hq,he⟩:=hVcore hv
    exact (Subtype.ext he) ▸ hq
  have hNV:(T:Subgroup G)≤normalizer (V:Set G) :=
    (normal_subgroupOf_iff_le_normalizer hVT).mp hn
  have hQW:pCore 2 M≤normalizer (W:Set M) := by
    have hQT:pCore 2 M≤(T.subtype hTM:Subgroup M) :=
      pCore_isPGroup.le_sylow_of_normal (T.subtype hTM)
    intro q hq
    apply mem_normalizer_iff.mpr
    intro x
    change (x:G)∈V ↔ ((q*x*q⁻¹:M):G)∈V
    exact mem_normalizer_iff.mp (hNV (hQT hq)) (x:G)
  have hmap (g:M) : (W.map (MulAut.conj g).toMonoidHom).map M.subtype=
      V.map (MulAut.conj (g:G)).toMonoidHom := by
    rw [map_map]
    have he:M.subtype.comp (MulAut.conj g).toMonoidHom=
        (MulAut.conj (g:G)).toMonoidHom.comp M.subtype := by ext x; rfl
    rw [he,←map_map,map_subgroupOf_eq_of_le hVM]
  apply elementary_normalClosure_of_ti W (pCore 2 M) hWQ hQW
  intro g
  rcases hTI g g.property with hd|he
  · left
    apply map_injective M.subtype_injective
    rw [map_inf _ _ _ M.subtype_injective,map_bot,
      map_subgroupOf_eq_of_le hVM,hmap]
    exact hd
  · right
    apply map_injective M.subtype_injective
    rw [hmap,map_subgroupOf_eq_of_le hVM]
    exact he
end Subgroup
