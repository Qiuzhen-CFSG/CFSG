module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.ComponentSylowMark
public import Theory.GroupTheory.CentralProductProjection.Elementary
/-! # Original crossing preparation and marked quotients
The original Thompson product extends the actual component mark, with kernel exactly its centralizing factor.
Source: Aschbacher--Smith 2.5.7, printed pp.555--556.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement Stellmacher
variable {G:Type*} [Group G] [Finite G] {H L M:Subgroup G} {S:Sylow 2 H} {z:G}
theorem MathieuSourceSetup.linear_thompson_mark_of_cover
    (c:MathieuSourceSetup H L M S z)
    (hJ:elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)=
      (((S:Subgroup H).map H.subtype)⊓L)⊔
        (elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)⊓centralizer (L:Set G)))
    (F:Type*) [Field F] [Finite F] {n:ℕ} (hn:0<n) (hF:Nat.card F=2^n)
    (α:L→*PSL(3,F)) (hα:Function.Surjective α) (hk:α.ker=center L)
    (hlift:∀W:Subgroup PSL(3,F),IsElementaryAbelian 2 W→IsElementaryAbelian 2 (W.comap α)) :
    let R:=elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)
    let A:=(((S:Subgroup H).map H.subtype)⊓L).subgroupOf R
    ∃f:R→*Matrix.PSL3Even.UnipotentGeometry.U F, Function.Surjective (f.comp A.subtype) ∧
      f.ker=(R⊓centralizer (L:Set G)).subgroupOf R ∧ A≤centralizer (f.ker:Set R) ∧
      ∀W:Subgroup (Matrix.PSL3Even.UnipotentGeometry.U F),IsElementaryAbelian 2 W→
        IsElementaryAbelian 2 (W.comap (f.comp A.subtype)) := by
  let Y:=(S:Subgroup H).map H.subtype
  let R:=elementaryAbelianMaxJ Y
  let A:=Y⊓L
  let C:=R⊓centralizer (L:Set G)
  have hR:R=A⊔C:=hJ
  have hAR:A≤R:=hR.symm ▸ (show A≤A⊔C from le_sup_left)
  obtain ⟨q,hq,hker,hpre⟩:=MathieuSourceSetup.linear_component_sylow_mark c F hn hF α hα hk hlift
  have hqC:q.ker=C.subgroupOf A:=by
    ext a
    change q a=1 ↔ (a:G)∈C
    rw [hker]
    exact ⟨fun h=>⟨hAR a.property,h⟩,fun h=>h.2⟩
  have hc:A≤centralizer (C:Set G):=
    le_centralizer_iff.mp (inf_le_right.trans (centralizer_le (show A≤L from inf_le_right)))
  exact exists_elementary_relative_projection A C R hc hJ q hqC hq hpre
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
