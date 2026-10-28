module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.Reflections
public import Theory.GroupTheory.PGroup.HyperbolicFactors
public import Theory.ElementaryAbelian.Injective

/-!
# Marked hyperbolic factors of the actual root product

The two extraspecial involution centralizers inside R are subgroups of order
sixteen meeting in its center E. Their generating product is R. Ambient
centralizer control supplies the self-centralizing condition, and the two
original core transpositions furnish the precise quotient reflections.
Source: Aschbacher, *Sporadic Groups* (1994), 8.15(6) and45.3, pp.29–30,243.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement
namespace Theory.GroupTheory.Recognition.UnitaryFourThree
variable {G : Type*} [Group G] [Finite G] {z : G}
namespace RootPair
variable (P : RootPair z)

noncomputable def hyperbolicFactors (h : IsType z) :
    Theory.GroupTheory.HyperbolicFactors P.R := by
  let Z : P.R := ⟨z,P.E_le_R h P.z_mem_E⟩
  let U : P.R := ⟨P.u,P.E_le_R h P.u_mem_E⟩
  have hc : center P.R = P.E.subgroupOf P.R := by
    apply (map_injective P.R.subtype_injective)
    rw [map_subgroupOf_eq_of_le (P.E_le_R h),P.R_center h]
  have hcenterCard : Nat.card (center P.R)=4 := by
    rw [hc,Nat.card_congr (subgroupOfEquivOfLe (P.E_le_R h)).toEquiv,P.E_card h]
  have hcenterEA : IsElementaryAbelian 2 (center P.R) := by
    rw [hc]
    let : IsElementaryAbelian 2 P.E := P.E_elementary h
    exact IsElementaryAbelian.subgroupOf (P.E_le_R h)
  let zR : center P.R := ⟨Z,hc ▸ P.z_mem_E⟩
  let uR : center P.R := ⟨U,hc ▸ P.u_mem_E⟩
  let A := P.leftCore.subgroupOf P.R
  let B := P.rightCore.subgroupOf P.R
  refine {
    card := P.R_card h
    center_card := hcenterCard
    center_elementary := hcenterEA
    square_central := ?_
    A := A
    B := B
    A_card := ?_
    B_card := ?_
    inf_eq := ?_
    sup_eq := ?_
    z := zR
    u := uR
    z_ne_one := ?_
    u_ne_one := ?_
    distinct := ?_
    centralizer_A := ?_
  }
  · intro x
    rw [hc]
    exact P.R_square_mem_E h x x.property
  · exact (Nat.card_congr (subgroupOfEquivOfLe le_sup_left).toEquiv).trans (P.leftCore_card h)
  · exact (Nat.card_congr (subgroupOfEquivOfLe le_sup_right).toEquiv).trans (P.rightCore_card h)
  · change (P.leftCore ⊓ P.rightCore).subgroupOf P.R = center P.R
    rw [P.leftCore_inf_rightCore h,hc]
  · rw [← subgroupOf_sup (show P.leftCore ≤ P.R from le_sup_left)
        (show P.rightCore ≤ P.R from le_sup_right)]
    change P.R.subgroupOf P.R = ⊤
    exact subgroupOf_self _
  · intro he
    have hz1 : z=1 := congrArg (fun x : center P.R => (x:G)) he
    have hh := h.involution
    simp [hz1] at hh
  · intro he
    have hu1 : P.u=1 := congrArg (fun x : center P.R => (x:G)) he
    have hh := P.u_order h
    simp [hu1] at hh
  · intro he
    exact P.u_ne_z (congrArg (fun x : center P.R => (x:G)) he).symm
  · apply le_antisymm
    · intro x hx
      have hxG : (x:G) ∈ Subgroup.centralizer (P.leftCore : Set G) := by
        intro y hy
        exact congrArg Subtype.val (hx ⟨y,(le_sup_left : P.leftCore ≤ P.R) hy⟩ hy)
      rw [P.centralizer_leftCore_eq_E h] at hxG
      rw [hc]
      exact hxG
    · rw [hc]
      intro x hx y hy
      have hyC : (y:G) ∈ Subgroup.centralizer (P.E : Set G) :=
        P.R_eq_centralizer_E h ▸ y.property
      exact Subtype.ext (hyC (x:G) hx).symm

end RootPair
end Theory.GroupTheory.Recognition.UnitaryFourThree
