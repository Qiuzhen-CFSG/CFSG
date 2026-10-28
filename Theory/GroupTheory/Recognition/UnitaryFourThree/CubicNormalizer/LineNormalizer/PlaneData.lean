module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.PlaneCubicNormalizer
/-!
# The actual local plane normalizer in ambient subgroup coordinates.
Both nested subtype maps and the exact cubic kernel are retained.
Source: Aschbacher, Sporadic Groups (1994),45.7(3),printed p.245.
-/
public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair
variable {G:Type*} [Group G] [Finite G] {z:G}
theorem plane_cubic_ambient_data (R:RootPair z) (h:IsType z)
    (A:Subgroup G) (hA:A≤R.T ∧ IsElementaryAbelian 2 A ∧ Nat.card A=16)
    (U:Subgroup G) (hU:Nat.card U=3) (hUM:U≤normalizer (A:Set G))
    (hfixed:Nat.card (A⊓Subgroup.centralizer (U:Set G):Subgroup G)=4) :
    let L:=normalizer (A:Set G)⊓normalizer (U:Set G)
    Nat.card L=72 ∧ (pCore 3 L).map L.subtype=U ∧
      (∃f:L→*Equiv.Perm (Fin 4),Function.Surjective f ∧ f.ker=U.subgroupOf L) ∧
      ∀x y:G,x∈A⊓Subgroup.centralizer (U:Set G)→y∈A⊓Subgroup.centralizer (U:Set G)→
        x≠1→y≠1→∃w∈L,w*x*w⁻¹=y := by
  let M:=normalizer (A:Set G)
  let N:=normalizer (U.subgroupOf M:Set M)
  let L:=M⊓normalizer (U:Set G)
  have hmap:N.map M.subtype=L:=by
    have he:(normalizer (U:Set G)).subgroupOf M=N:=subgroupOf_normalizer_eq hUM
    rw[←he,subgroupOf_map_subtype,inf_comm]
  let e:N≃*L:=(N.equivMapOfInjective M.subtype M.subtype_injective).trans (MulEquiv.subgroupCongr hmap)
  have he:∀n:N,(e n:G)=(n:M):=fun _=>rfl
  have hei:∀l:L,((e.symm l:M):G)=(l:G):=by
    intro l
    have hh:=he (e.symm l)
    simpa only[e.apply_symm_apply] using hh.symm
  obtain ⟨hN,hcore,⟨φ,hφ,hker⟩,horb⟩:=R.plane_cubic_normalizer_data h A hA U hU hUM hfixed
  have hUL:U≤L:=le_inf hUM le_normalizer
  have hUm:((U.subgroupOf M).subgroupOf N).map e.toMonoidHom=U.subgroupOf L:=by
    ext l
    constructor
    · rintro ⟨n,hn,rfl⟩
      exact hn
    · intro hl
      exact ⟨e.symm l,by change ((e.symm l:M):G)∈U;rw[hei];exact hl,e.apply_symm_apply l⟩
  refine ⟨(Nat.card_congr e.toEquiv).symm.trans hN,?_,?_,?_⟩
  · have hh:=pCore_map_iso 3 e
    rw[hcore,hUm] at hh
    rw[←hh,map_subgroupOf_eq_of_le hUL]
  · refine ⟨φ.comp e.symm.toMonoidHom,hφ.comp e.symm.surjective,?_⟩
    ext l
    change φ (e.symm l)=1 ↔ (l:G)∈U
    rw[←MonoidHom.mem_ker,hker]
    change ((e.symm l:M):G)∈U ↔ _
    rw[hei]
  · intro x y hx hy hx1 hy1
    let W:Sylow 3 N:=default
    obtain ⟨w,hw,heq⟩:=horb W x y hx hy hx1 hy1
    exact ⟨w,(show w∈L from hmap ▸ map_mono (map_subtype_le (W:Subgroup N)) hw),heq⟩
end Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair
