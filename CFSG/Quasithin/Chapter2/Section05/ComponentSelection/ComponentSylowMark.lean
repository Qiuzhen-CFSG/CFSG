module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SylowCommutatorSource
public import Theory.SpecificGroups.PSL3Even.ThompsonCentralCover.SylowMark
public import Theory.GroupTheory.CentralProductProjection.Relative
/-! # Original crossing preparation and marked quotients
The original component Sylow subgroup carries its literal matrix quotient; the kernel is the component centralizer.
Source: Aschbacher--Smith 2.5.7, printed pp.555--556.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement Stellmacher
variable {G:Type*} [Group G] [Finite G] {H L M:Subgroup G} {S:Sylow 2 H} {z:G}
theorem MathieuSourceSetup.exists_relative_component_sylow
    (c:MathieuSourceSetup H L M S z) :
    ∃P:Sylow 2 L,(P:Subgroup L)=((S:Subgroup H).map H.subtype).subgroupOf L := by
  obtain ⟨Q,hQ⟩:=S.exists_subgroupOf_eq_of_subnormal (L.subgroupOf H) c.component.1
  let eL:L.subgroupOf H≃*L:=subgroupOfEquivOfLe c.component_le
  let P:=Q.mapSurjective (f:=eL.toMonoidHom) eL.surjective
  refine ⟨P,?_⟩
  ext l
  change l∈(Q:Subgroup (L.subgroupOf H)).map eL.toMonoidHom ↔ _
  rw [mem_map_equiv,hQ]
  change (⟨(l:G),c.component_le l.property⟩:H)∈S ↔ (l:G)∈(S:Subgroup H).map H.subtype
  constructor
  · exact fun h=>mem_map_of_mem H.subtype h
  · rintro ⟨a,ha,he⟩
    exact (show a=(⟨(l:G),c.component_le l.property⟩:H) from Subtype.ext he) ▸ ha

theorem MathieuSourceSetup.linear_component_sylow_mark
    (c:MathieuSourceSetup H L M S z)
    (F:Type*) [Field F] [Finite F] {n:ℕ} (hn:0<n) (hF:Nat.card F=2^n)
    (α:L→*PSL(3,F)) (hα:Function.Surjective α) (hk:α.ker=center L)
    (hlift:∀W:Subgroup PSL(3,F),IsElementaryAbelian 2 W→IsElementaryAbelian 2 (W.comap α)) :
    ∃f:(((S:Subgroup H).map H.subtype)⊓L:Subgroup G)→*Matrix.PSL3Even.UnipotentGeometry.U F,
      Function.Surjective f ∧
      (∀k,f k=1↔(k:G)∈centralizer (L:Set G)) ∧
      ∀W:Subgroup (Matrix.PSL3Even.UnipotentGeometry.U F),
        IsElementaryAbelian 2 W→IsElementaryAbelian 2 (W.comap f) := by
  obtain ⟨P,hP⟩:=MathieuSourceSetup.exists_relative_component_sylow c
  let Y:=(S:Subgroup H).map H.subtype
  let e:(Y⊓L:Subgroup G)≃*P:={
    toFun k:=⟨⟨k,k.property.2⟩,by rw [hP];exact k.property.1⟩
    invFun k:=⟨k.val.val,by
      have hy:(k:L)∈Y.subgroupOf L:=hP ▸ k.property
      exact ⟨hy,k.val.property⟩⟩
    left_inv _:=rfl
    right_inv _:=rfl
    map_mul' _ _:=rfl }
  obtain ⟨q,hq,hker,hpre⟩:=Matrix.PSL3Even.UnipotentGeometry.exists_sylow_cover_mark
    α hα hlift hn hF P
  let f:=q.comp e.toMonoidHom
  refine ⟨f,hq.comp e.surjective,?_,?_⟩
  · intro k
    change q (e k)=1 ↔ _
    rw [←MonoidHom.mem_ker,hker,hk]
    constructor
    · intro hz a ha
      exact congrArg Subtype.val (mem_center_iff.mp hz ⟨a,ha⟩)
    · intro hz
      apply mem_center_iff.mpr
      intro a
      exact Subtype.ext (hz a a.property)
  · intro W hW
    let :=hpre W hW
    change IsElementaryAbelian 2 ((W.comap q).comap e.toMonoidHom)
    exact IsElementaryAbelian.comap_of_injective e.toMonoidHom e.injective _
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
