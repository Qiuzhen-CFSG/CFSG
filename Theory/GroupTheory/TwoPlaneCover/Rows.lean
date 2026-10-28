module
public import Theory.GroupTheory.TwoPlaneCover
/-! # Plane centralizers and full commutator rows
A plane and its opposite involution centralizer generate the cover. Thus its
commutator row equals the full row, with the exact marked centralizer kept.
Source: Aschbacher--Smith 2.5.7, printed pp.555--556.
-/
public section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace Subgroup.ClassTwo
variable {G:Type*} [Group G]
theorem commutatorHom_map (hc:_root_.commutator G≤center G) (t:G) (V:Subgroup G) :
    V.map (commutatorHom hc t)=⁅zpowers t,V⁆ := by
  let f:=commutatorHom hc t
  have hcentral:V.map f≤center G:=by
    rintro _ ⟨x,_,rfl⟩
    exact hc (commutator_mem_commutator (mem_top t) (mem_top x))
  let : (V.map f).Normal:=⟨fun x hx g=>by
    rw [mem_center_iff.mp (hcentral hx) g,mul_inv_cancel_right]
    exact hx⟩
  let π:=QuotientGroup.mk' (V.map f)
  have ht (x:G) (hx:x∈V):Commute (π t) (π x):=by
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [←map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨x,hx,rfl⟩
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact commutator_mem_commutator (mem_zpowers t) hx
  · apply commutator_le.mpr
    intro y hy x hx
    obtain ⟨n,rfl⟩:=mem_zpowers_iff.mp hy
    apply (QuotientGroup.eq_one_iff _).mp
    change π ⁅t^n,x⁆=1
    rw [map_commutatorElement,map_zpow]
    exact commutatorElement_eq_one_iff_mul_comm.mpr ((ht x hx).zpow_left n).eq

theorem commutator_row_eq_of_sup_centralizer (hc:_root_.commutator G≤center G)
    (V:Subgroup G) (a:G) (hgen:V⊔centralizer ({a}:Set G)=⊤) :
    ⁅V,zpowers a⁆=⁅(⊤:Subgroup G),zpowers a⁆ := by
  rw [commutator_comm V,commutator_comm ⊤,←commutatorHom_map hc a V,
    ←commutatorHom_map hc a ⊤,←hgen,Subgroup.map_sup]
  have hz:(centralizer ({a}:Set G)).map (commutatorHom hc a)=⊥:=by
    apply bot_unique
    rintro _ ⟨x,hx,rfl⟩
    change (commutatorHom hc a) x=1
    exact (show x∈(commutatorHom hc a).ker from (commutatorHom_ker hc a).symm ▸ hx)
  rw [hz,sup_bot_eq]
end Subgroup.ClassTwo
namespace Subgroup.TwoPlaneCover
variable {G:Type*} [Group G]
theorem centralizer_inter_plane_le_center (V W:Subgroup G)
    (hZ:V⊓W≤center G) (t:G) (ht:t∉V)
    (hc:centralizer ({t}:Set G)=V∨centralizer ({t}:Set G)=W) :
    V⊓centralizer ({t}:Set G)≤center G := by
  rcases hc with h|h
  · exact False.elim (ht (h ▸ (show t∈centralizer ({t}:Set G) from mem_centralizer_singleton_iff.mpr rfl)))
  · rw [h]
    exact hZ
end Subgroup.TwoPlaneCover
namespace Subgroup.TwoPlaneCover
variable {E Q:Type*} [Group E] [Group Q]
theorem comap_sup_eq_top (f:E→*Q) (hf:Function.Surjective f) (V W:Subgroup Q) (hgen:V⊔W=⊤) :
    V.comap f⊔W.comap f=⊤ := by
  have hker:f.ker≤V.comap f⊔W.comap f:=by
    intro x hx
    apply mem_sup_left
    change f x∈V
    rw [show f x=1 from hx]
    exact V.one_mem
  have hm:((V.comap f)⊔(W.comap f)).map f=⊤:=by
    rw [Subgroup.map_sup,map_comap_eq_self_of_surjective hf,
      map_comap_eq_self_of_surjective hf,hgen]
  have he:=congrArg (Subgroup.comap f) hm
  simpa only [comap_map_eq_self hker,comap_top] using he

theorem plane_row_eq_full (f:E→*Q) (hf:Function.Surjective f)
    (V W:Subgroup Q) (hgen:V⊔W=⊤) (hZ:center Q≤V⊓W)
    [IsMulCommutative (V.comap f)] [IsMulCommutative (W.comap f)]
    (hc:_root_.commutator Q≤center Q) (a:E)
    (ha:centralizer ({f a}:Set Q)=W) :
    ⁅V.comap f,zpowers a⁆=⁅(⊤:Subgroup E),zpowers a⁆ := by
  have hclass:=class_two f hf V W hgen hZ hc
  have hi:IsMulCommutative ((centralizer ({f a}:Set Q)).comap f):=ha.symm ▸ inferInstance
  let :=hi
  have hcent:=centralizer_eq_comap f a
  apply ClassTwo.commutator_row_eq_of_sup_centralizer hclass
  rw [hcent,ha]
  exact comap_sup_eq_top f hf V W hgen

theorem self_centralizer_of_witness (V:Subgroup Q) [IsMulCommutative V]
    (a:Q) (ha:a∈V) (hcent:centralizer ({a}:Set Q)=V) : centralizer (V:Set Q)=V := by
  apply le_antisymm
  · intro x hx
    rw [←hcent]
    apply mem_centralizer_singleton_iff.mpr
    exact (hx a ha).symm
  · intro x hx y hy
    let : CommGroup V:=IsMulCommutative.instCommGroup
    exact congrArg Subtype.val (mul_comm (⟨y,hy⟩:V) ⟨x,hx⟩)
end Subgroup.TwoPlaneCover

