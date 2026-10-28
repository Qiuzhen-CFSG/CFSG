module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.PlaneCubicNormalizer
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicNormalizer.LineNormalizer.PlanePosition

/-!
# Original reflected-line S4 local structure

The earlier simultaneous placement constructs the marking and its plane. The local A6 calculation now gives the actual S4 quotient and the Sylow-nine action on its fixed four, without any remaining placement or module premise.
Source: Aschbacher, Sporadic Groups (1994), 45.7(3), printed p.245.
-/

public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair
variable {G:Type*} [Group G] [Finite G] {z:G}

/-- Original-source local S4 normalizer with the same reflected cubic, actors, and plane. -/
theorem exists_reflected_plane_cubic_normalizer (R:RootPair z) (h:IsType z)
    (P:Sylow 3 (centralizer z)) :
    let X:=(P:Subgroup (centralizer z)).map (centralizer z).subtype
    ∃m:CubicNormalizer.ReflectedMarking z X,∃A:Subgroup G,
      (A≤R.T ∧ IsElementaryAbelian 2 A ∧ Nat.card A=16) ∧
      m.t∈A ∧ m.t∈R.cubicSylow X ∧ m.s∈R.cubicSylow X ∧
      R.cubicSylow X≤normalizer (A:Set G) ∧
      let U:=X⊓Subgroup.centralizer ({m.t}:Set G)
      let M:=normalizer (A:Set G)
      let N:=normalizer (U.subgroupOf M:Set M)
      U≤M ∧ Nat.card (A⊓Subgroup.centralizer (U:Set G):Subgroup G)=4 ∧
      Nat.card N=72 ∧ pCore 3 N=(U.subgroupOf M).subgroupOf N ∧
      (∃φ:N→*Equiv.Perm (Fin 4),Function.Surjective φ ∧
        φ.ker=(U.subgroupOf M).subgroupOf N) ∧
      ∀W:Sylow 3 N,∀x y:G,x∈A⊓Subgroup.centralizer (U:Set G)→
        y∈A⊓Subgroup.centralizer (U:Set G)→x≠1→y≠1→
        ∃w∈((W:Subgroup N).map N.subtype).map M.subtype,w*x*w⁻¹=y := by
  obtain ⟨m,A,hA,htA,ht,hs,hTN,_,_,_,_,hUM,hfixed⟩:=
    R.exists_reflected_line_source_geometry h P
  exact ⟨m,A,hA,htA,ht,hs,hTN,hUM,hfixed,
    R.plane_cubic_normalizer_data h A hA _ m.common_fixed_card hUM hfixed⟩
end Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair
