module

public import Theory.GroupTheory.Recognition.AlternatingSixCubicTI.StronglyRegular
public import Theory.Combinatorics.DoilyRecognition.Action
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The cubic-TI recognition of the alternating group on six letters

An actual S₄ subgroup of index fifteen, together with an elementary Sylow
3-subgroup of order nine having TI and cyclic-four normalizer quotient,
produces the (15,6,1,3) coset graph.  Its six-letter action and the order
calculation identify the ambient group with A₆.

Source: Aschbacher, *Sporadic Groups* (1994), Exercise 2, printed p.249.
-/

@[expose] public section

open Subgroup
namespace Theory.GroupTheory.Recognition.AlternatingSixCubicTI
variable {G:Type*} [Group G] [Finite G]

/-- Aschbacher's original cubic-TI characterization of A6, with no simplicity premise. -/
theorem alternatingSix_of_symmetricFour_index_fifteen
    (H:Subgroup G) (eH:H≃*Equiv.Perm (Fin 4)) (hi:H.index=15)
    (P:Sylow 3 G) [IsElementaryAbelian 3 P] (hP:Nat.card (P:Subgroup G)=9)
    (hTI:∀g:G,(P:Subgroup G)⊓(P:Subgroup G).map (MulAut.conj g).toMonoidHom=⊥ ∨
      (P:Subgroup G).map (MulAut.conj g).toMonoidHom=P)
    (hC:centralizer (P:Set G)≤P)
    (eN:(normalizer ((P:Subgroup G):Set G)⧸(P:Subgroup G).subgroupOf
      (normalizer ((P:Subgroup G):Set G)))≃*Multiplicative (ZMod 4)):
    Nonempty (G≃*alternatingGroup (Fin 6)) := by
  classical
  let f:=H.subtype.comp eH.symm.toMonoidHom
  have hf:Function.Injective f:=H.subtype_injective.comp eH.symm.injective
  have hr:f.range=H := by
    ext x
    constructor
    · rintro ⟨a,rfl⟩
      exact (eH.symm a).property
    · intro hx
      exact ⟨eH ⟨x,hx⟩,by simp [f]⟩
  have hindex:f.range.index=15 := hr ▸ hi
  have hfour:Nat.card f.range=24 := by
    rw [←Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
    simp only [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
    decide
  obtain ⟨b,c,hb,h8,hcover,h6⟩:=exists_suborbits_of_ti f hf hindex P hP hTI hC eN
  let : Fintype (G⧸f.range):=Fintype.ofFinite _
  have hgraph:=cosetGraph_strongly_regular f.range hfour b c hb h8 hcover h6 hindex
  have hfaith:=symmetric_coset_action_injective f.range (MonoidHom.ofInjective hf).symm hindex
    (cubic_centralizer_card P hP hTI hC eN)
  obtain ⟨φ,hφ⟩:=Theory.Combinatorics.Doily.faithful_action_six hgraph
    (MulAction.toPermHom G (G⧸f.range)) hfaith (cosetGraph_invariant f.range hfour)
  have hG:Nat.card G=360:=card_eq_360_of_s4_index15 H eH hi
  have hφcard:Nat.card φ.range=360:=
    (Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv).symm.trans hG
  have hφindex:φ.range.index=2 := by
    have hh:=φ.range.index_mul_card
    rw [hφcard,Nat.card_perm,Nat.card_fin] at hh
    norm_num [Nat.factorial] at hh
    omega
  exact ⟨(MonoidHom.ofInjective hφ).trans
    (MulEquiv.subgroupCongr (Equiv.Perm.eq_alternatingGroup_of_index_eq_two hφindex))⟩
end Theory.GroupTheory.Recognition.AlternatingSixCubicTI
