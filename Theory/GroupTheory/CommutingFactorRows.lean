module
public import Theory.GroupTheory.TwoPlaneCover.Rows
/-! # Commutator rows in commuting products
The row of an element of one factor is unchanged after adjoining its
centralizing factor. The literal subgroup maps retain the kernel marking
needed for the crossing-plane argument in Aschbacher--Smith 2.5.7.
-/
public section
open Subgroup
open scoped commutatorElement
namespace Subgroup.ClassTwo
variable {G:Type*} [Group G]
theorem commutator_row_map_subtype (K:Subgroup G) (a:K) :
    (⁅zpowers a,(⊤:Subgroup K)⁆:Subgroup K).map K.subtype=⁅zpowers (a:G),K⁆ := by
  have ht:(⊤:Subgroup K).map K.subtype=K:=by ext x;simp
  rw [map_commutator,MonoidHom.map_zpowers,ht]
  rfl

theorem row_eq_factor (hc:_root_.commutator G≤center G)
    (K C:Subgroup G) (hKC:K⊔C=⊤) (hcomm:K≤centralizer (C:Set G)) (a:K) :
    (⁅zpowers a,(⊤:Subgroup K)⁆:Subgroup K).map K.subtype=⁅zpowers (a:G),(⊤:Subgroup G)⁆ := by
  rw [commutator_row_map_subtype,commutator_comm (zpowers (a:G)) K,
    commutator_comm (zpowers (a:G)) ⊤]
  apply commutator_row_eq_of_sup_centralizer hc
  apply top_unique
  rw [←hKC]
  apply sup_le_sup_left
  intro c hc
  exact mem_centralizer_singleton_iff.mpr (hcomm a.property c hc)

theorem row_card_eq_factor [Finite G] (hc:_root_.commutator G≤center G)
    (K C:Subgroup G) (hKC:K⊔C=⊤) (hcomm:K≤centralizer (C:Set G)) (a:K) :
    Nat.card (⁅zpowers (a:G),(⊤:Subgroup G)⁆:Subgroup G)=
      Nat.card (⁅zpowers a,(⊤:Subgroup K)⁆:Subgroup K) := by
  rw [←row_eq_factor hc K C hKC hcomm a,card_map_of_injective K.subtype_injective]

theorem row_congr_on_plane (hc:_root_.commutator G≤center G)
    (V:Subgroup G) (a b:G) (hab:∀v∈V,⁅a,v⁆=⁅b,v⁆) :
    ⁅zpowers a,V⁆=⁅zpowers b,V⁆ := by
  rw [←commutatorHom_map hc a V,←commutatorHom_map hc b V]
  ext x
  constructor
  · rintro ⟨v,hv,h⟩
    exact ⟨v,hv,(hab v hv).symm.trans h⟩
  · rintro ⟨v,hv,h⟩
    exact ⟨v,hv,(hab v hv).trans h⟩

theorem row_mul_centralizer (hc:_root_.commutator G≤center G)
    (V:Subgroup G) (a c:G) (hcV:c∈centralizer (V:Set G)) :
    ⁅zpowers (a*c),V⁆=⁅zpowers a,V⁆ := by
  apply row_congr_on_plane hc V
  intro v hv
  have hz:c*v*c⁻¹=v:=by rw [←hcV v hv,mul_inv_cancel_right]
  calc
    ⁅a*c,v⁆=a*(c*v*c⁻¹)*a⁻¹*v⁻¹ := by simp only [commutatorElement_def,mul_inv_rev];group
    _=⁅a,v⁆ := by rw [hz];rfl
end Subgroup.ClassTwo

