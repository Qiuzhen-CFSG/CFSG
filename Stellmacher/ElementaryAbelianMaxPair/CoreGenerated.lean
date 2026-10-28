module
public import Stellmacher.ElementaryAbelianMaxPair.FactorFamily
/-! # The Thompson factor of a commuting core
The exact maximum-family factorization implies that the centralizer
intersection of J(S) is J(C). To prove the reverse containment, combine an
arbitrary largest elementary subgroup of C with a fixed component factor;
the central-product order formula shows that the resulting join is again
largest in S. This retains a possibly nontrivial shared central kernel.
Source: Aschbacher--Smith 2.5.7, printed p.555, passage to the two core planes.
-/
public section
open Subgroup
open scoped Pointwise
namespace Stellmacher
variable {G:Type*} [Group G] [Finite G]
theorem maxFamily_central_intersection_le (S K C A:Subgroup G)
    (hc:K≤centralizer (C:Set G)) (hKS:K≤S)
    [IsElementaryAbelian 2 (K⊓C:Subgroup G)]
    (hA:A∈elementaryAbelianMaxSubgroups S) (hAKC:A≤K⊔C) : K⊓C≤A := by
  let : IsElementaryAbelian 2 A:=hA.2.1
  have hZK:K⊓C≤centralizer (K:Set G):=inf_le_right.trans (le_centralizer_iff.mp hc)
  have hZC:K⊓C≤centralizer (C:Set G):=inf_le_left.trans hc
  have hZA:K⊓C≤centralizer (A:Set G):=by
    apply le_centralizer_iff.mp
    exact hAKC.trans (sup_le (le_centralizer_iff.mp hZK) (le_centralizer_iff.mp hZC))
  have he:IsElementaryAbelian 2 (A⊔(K⊓C):Subgroup G):=
    IsElementaryAbelian.sup_of_le_centralizer hZA
  have hEq:A=A⊔(K⊓C):=eq_of_le_of_card_ge le_sup_left
    (hA.2.2 _ (sup_le hA.1 (inf_le_left.trans hKS)) he)
  rw [hEq]
  exact le_sup_right

theorem thompson_centralizer_factor (S K C:Subgroup G)
    (hKS:K≤S) (hCS:C≤S) (hc:K≤centralizer (C:Set G))
    (hsplit:∀A∈elementaryAbelianMaxSubgroups S,
      A=(A⊓K)⊔(A⊓C) ∧ A⊓C∈elementaryAbelianMaxSubgroups C)
    (hZ:∀A∈elementaryAbelianMaxSubgroups S,K⊓C≤A) :
    elementaryAbelianMaxJ S⊓C=elementaryAbelianMaxJ C := by
  let R:=elementaryAbelianMaxJ S
  let J:=elementaryAbelianMaxJ C
  obtain ⟨A,hA⟩:=elementaryAbelianMaxSubgroups_nonempty S
  obtain ⟨ha,hAC⟩:=hsplit A hA
  let : IsElementaryAbelian 2 A:=hA.2.1
  let : IsElementaryAbelian 2 (A⊓K:Subgroup G):=IsElementaryAbelian.of_le inf_le_left
  have hint:(A⊓K)⊓(A⊓C)=K⊓C:=by
    apply le_antisymm
    · exact le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
    · exact le_inf (le_inf (hZ A hA) inf_le_left) (le_inf (hZ A hA) inf_le_right)
  have hprodA:=card_mul_eq_card_inf_mul_card_sup_of_normalizes (A⊓K) (A⊓C)
    ((inf_le_right.trans ((le_centralizer_iff.mp hc).trans
      (centralizer_le inf_le_right))).trans (Subgroup.centralizer_le_normalizer _))
  rw [hint,←ha] at hprodA
  have hJRC:J≤R⊓C:=by
    apply le_inf ?_ (sSup_le fun _ h=>h.1)
    apply sSup_le
    intro B hB
    let : IsElementaryAbelian 2 B:=hB.2.1
    have hbc:A⊓K≤centralizer (B:Set G):=inf_le_right.trans (hc.trans (centralizer_le hB.1))
    have hbe:IsElementaryAbelian 2 ((A⊓K)⊔B:Subgroup G):=
      IsElementaryAbelian.sup_of_le_centralizer (le_centralizer_iff.mp hbc)
    have hBJ:((A⊓K)⊔B)≤S:=sup_le (inf_le_right.trans hKS) (hB.1.trans hCS)
    have hsize:Nat.card B=Nat.card (A⊓C:Subgroup G):=
      le_antisymm (hAC.2.2 B hB.1 hB.2.1) (hB.2.2 _ hAC.1 hAC.2.1)
    have hprodB:=card_mul_eq_card_inf_mul_card_sup_of_normalizes (A⊓K) B
      ((le_centralizer_iff.mp hbc).trans (Subgroup.centralizer_le_normalizer _))
    have hI:Nat.card ((A⊓K)⊓B:Subgroup G)≤Nat.card (K⊓C:Subgroup G):=
      card_le_of_le (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans hB.1))
    have hlarge:Nat.card A≤Nat.card ((A⊓K)⊔B:Subgroup G):=by
      apply Nat.le_of_mul_le_mul_left (c:=Nat.card (K⊓C:Subgroup G)) ?_ Nat.card_pos
      calc
        Nat.card (K⊓C:Subgroup G)*Nat.card A=
          Nat.card (A⊓K:Subgroup G)*Nat.card B:=by rw [←hprodA,hsize]
        _=Nat.card ((A⊓K)⊓B:Subgroup G)*Nat.card ((A⊓K)⊔B:Subgroup G):=hprodB
        _≤_:=Nat.mul_le_mul_right _ hI
    have hmax:((A⊓K)⊔B)∈elementaryAbelianMaxSubgroups S:=
      ⟨hBJ,hbe,fun E hES hE=>(hA.2.2 E hES hE).trans hlarge⟩
    exact le_sup_right.trans (le_sSup hmax)
  have hZJ:K⊓C≤J:=
    (le_inf (hZ A hA) inf_le_right).trans (le_sSup hAC)
  have hRJ:R≤K⊔J:=by
    apply sSup_le
    intro B hB
    obtain ⟨he,hC⟩:=hsplit B hB
    rw [he]
    exact sup_le_sup inf_le_right (le_sSup hC)
  have hJC:J≤C:=sSup_le fun _ h=>h.1
  have hKJ:K≤centralizer (J:Set G):=hc.trans (centralizer_le hJC)
  apply le_antisymm ?_ hJRC
  intro x hx
  have hp:x∈(K:Set G)*(J:Set G):=by
    rw [←coe_mul_of_left_le_normalizer_right K J (hKJ.trans (Subgroup.centralizer_le_normalizer _))]
    exact hRJ hx.1
  obtain ⟨k,hk,j,hj,hkj⟩:=hp
  have hkC:k∈C:=by
    have hh:=C.mul_mem hx.2 (C.inv_mem (hJC hj))
    rw [←hkj,mul_inv_cancel_right] at hh
    exact hh
  rw [←hkj]
  exact J.mul_mem (hZJ ⟨hk,hkC⟩) hj
end Stellmacher
