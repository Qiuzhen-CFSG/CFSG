module

public import CFSG.Quasithin.Chapter3.Section02.Setup
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.Source.Transport
public import Theory.GroupTheory.CComponent.OrbitCorrespondence

/-!
# Identifying the original component with a selected alternating-five block

A C-component generating L₀T together with T has every other C-component
in its T-conjugacy orbit. In particular the original FSU component is a
conjugate of the block selected by E.2.3. Transport along that conjugation
preserves both shortness and the literal alternating-five module model.

The block's subnormality is retained in L₀T, its actual ambient group;
the intrinsic alternating-five statement also holds on the original L.
This discharges the identification step after E.2.3 in the A₅ branch of
10.2.1, without assuming normalization of L or identifying it by abstract
isomorphism alone.
Source: Aschbacher–Smith, 10.2.1, printed pp.742–743, using E.2.3 and
the C-component correspondence A.3.3, pp.216–217,42–43.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC
universe u
variable {G : Type u} [Group G] [Finite G] {C : GroupClass.{u}}
  {T : Sylow 2 G} {L : Subgroup G} (D : FundamentalSetup C T L)

include D

/-- The selected generating component has the original L in its actual
Sylow conjugacy orbit inside L₀T. -/
theorem source_original_component_conjugate_of_generating_component
    (K : Subgroup (localJoin T L)) (hK : K.IsCComponent)
    (hgen : K ⊔ ((T.subtype (show (T : Subgroup G) ≤ localJoin T L from
      le_sup_right)) : Subgroup (localJoin T L)) = ⊤) :
    ∃ s : (T.subtype (show (T : Subgroup G) ≤ localJoin T L from le_sup_right)),
      L.subgroupOf (localJoin T L) = K.map (MulAut.conj (s : localJoin T L)).toMonoidHom := by
  have hL : (L.subgroupOf (localJoin T L)).IsCComponent := by
    change (L.subgroupOf (componentOrbit L (T : Subgroup G) ⊔ (T : Subgroup G))).IsCComponent
    rw [componentOrbit_sup]
    exact D.maximal.1.1
  exact hK.conjugate_of_pGroup_generated hL (T.subtype le_sup_right).isPGroup' hgen

/-- The literal original component inherits the selected block and its
alternating-five action; no A₅-quotient or nonnormality premise is needed
once the generating block has been constructed. -/
theorem original_L_block_of_generating_block
    (K : Subgroup (localJoin T L)) (hK : K.IsCComponent)
    (hgen : K ⊔ ((T.subtype (show (T : Subgroup G) ≤ localJoin T L from
      le_sup_right)) : Subgroup (localJoin T L)) = ⊤)
    (hblock : IsBlock K) (hAlt : IsAlternatingBlock K 5) :
    IsBlock (L.subgroupOf (localJoin T L)) ∧
      IsAlternatingBlock (L.subgroupOf (localJoin T L)) 5 ∧
      IsAlternatingBlock L 5 := by
  obtain ⟨s, hs⟩ := source_original_component_conjugate_of_generating_component D K hK hgen
  let a := ((MulAut.conj (s : localJoin T L)).subgroupMap K).trans
    (MulEquiv.subgroupCongr hs.symm)
  have hshort := RankOne.Solvable.isShort_of_equiv a hblock.short
  have hsub : (L.subgroupOf (localJoin T L)).IsSubnormal := by
    rw [hs]
    exact hblock.subnormal.map (MulAut.conj (s : localJoin T L)).surjective
  have ha := RankOne.Solvable.isAlternatingBlock_of_equiv a hAlt
  have hLH : L ≤ localJoin T L := (le_componentOrbit L T).trans le_sup_left
  exact ⟨⟨inferInstance, hshort, hsub⟩, ha,
    RankOne.Solvable.isAlternatingBlock_of_equiv (subgroupOfEquivOfLe hLH) ha⟩

end CFSG.Quasithin.Chapter10
