module
public import Theory.GroupTheory.C5C4TwoInvolutions
public import Theory.GroupTheory.CommutatorPreimage
public import Theory.ElementaryAbelian.Join

/-!
# Residual commutator control from two Frobenius reflections

Let a finite group P map to C₅ ⋊ C₄ with kernel Q. Suppose A is normal,
A≤Q and [Q,Q]≤A. A subgroup C contained in V1 Q centralizes V1 and
centralizes V2 modulo A. If the actual V1,V2 images are distinct of order
two, then C≤Q and C centralizes every subgroup E modulo A whose image
lies in the normal C₅. Neither the action nor the projection is assumed
faithful or surjective.

The image of C lies in the first reflection and centralizes the second.
A nontrivial image would make the two reflections generate an elementary
four-group, contradicting the elementary-subgroup bound in C₅ ⋊ C₄.
The two reflections generate the normal five-subgroup, so E lies in
Q V1 V2. The three commutator bounds then close in the preimage of the
centralizer of C modulo A.

This is the finite-group transfer behind the predecessor commutator step
in Stellmacher (10.1), Journal of Algebra190 (1997), printed p.65.
-/

namespace Subgroup
open scoped IsMulCommutative

public theorem commutator_residual_le_of_two_reflections
    {P:Type*} [Group P] [Finite P]
    (φ : Multiplicative (ZMod 4)→*MulAut (Multiplicative (ZMod 5)))
    (f:P→*SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ)
    (Q A C V1 V2 E:Subgroup P) [A.Normal]
    (hker:f.ker=Q) (hAQ:A≤Q) (hC:C≤V1⊔Q)
    (hC1:⁅C,V1⁆=⊥) (hC2:⁅C,V2⁆≤A) (hQQ:⁅Q,Q⁆≤A)
    (hE:E.map f≤(SemidirectProduct.inl : Multiplicative (ZMod 5)→*
      SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ).range)
    (h1:Nat.card (V1.map f)=2) (h2:Nat.card (V2.map f)=2)
    (hne:V1.map f≠V2.map f) : C≤Q ∧ ⁅C,E⁆≤A := by
  let _ : Finite (SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ) :=
    Finite.of_equiv (Multiplicative (ZMod 5) × Multiplicative (ZMod 4)) SemidirectProduct.equivProd.symm
  let T1:=V1.map f
  let T2:=V2.map f
  let D:=C.map f
  have hQzero:Q.map f=⊥:=by
    rw [←hker,map_eq_bot_iff]
  have hAzero:A.map f=⊥:=by
    rw [map_eq_bot_iff,hker]
    exact hAQ
  have hD1:D≤T1:=by
    have hh:=map_mono (f:=f) hC
    rw [map_sup,hQzero,sup_bot_eq] at hh
    exact hh
  have hD2:⁅D,T2⁆=⊥:=by
    change ⁅C.map f,V2.map f⁆=⊥
    rw [←map_commutator]
    exact bot_unique ((map_mono hC2).trans_eq hAzero)
  have hDzero:D=⊥:=by
    by_contra hnot
    have hDcard:2≤Nat.card D:=by
      have hh:1<Nat.card D:=(one_lt_card_iff_ne_bot D).mpr hnot
      omega
    have hDeq:D=T1:=eq_of_le_of_card_ge hD1 (by rw [h1];exact hDcard)
    have hcentral:T1≤centralizer (T2:Set _) := commutator_eq_bot_iff_le_centralizer.mp (hDeq ▸ hD2)
    let _ : Fact (Nat.Prime 2):=⟨Nat.prime_two⟩
    let _ : IsCyclic T1:=isCyclic_of_prime_card h1
    let _ : IsCyclic T2:=isCyclic_of_prime_card h2
    let _ : IsElementaryAbelian 2 T1:={
      toIsMulCommutative:=inferInstance
      exponent_dvd_p:=by rw [IsCyclic.exponent_eq_card,h1] }
    let _ : IsElementaryAbelian 2 T2:={
      toIsMulCommutative:=inferInstance
      exponent_dvd_p:=by rw [IsCyclic.exponent_eq_card,h2] }
    let _ : IsElementaryAbelian 2 ↥(T1⊔T2):=
      IsElementaryAbelian.sup_of_le_centralizer (le_centralizer_iff.mp hcentral)
    have hc:=SemidirectProduct.elementary_two_subgroup_card_le_two φ (T1⊔T2) inferInstance
    have he1:T1=T1⊔T2:=eq_of_le_of_card_ge le_sup_left (by rw [h1];exact hc)
    have he2:T2=T1⊔T2:=eq_of_le_of_card_ge le_sup_right (by rw [h2];exact hc)
    exact hne (he1.trans he2.symm)
  have hCQ:C≤Q:=by
    rw [←hker,←map_eq_bot_iff]
    exact hDzero
  have hnormalFive:=SemidirectProduct.normal_five_le_sup_of_distinct_two_subgroups φ T1 T2 h1 h2 hne
  have hEimage:E.map f≤(V1⊔V2).map f:=by
    rw [map_sup]
    exact hE.trans hnormalFive
  have hEjoin:E≤(V1⊔V2)⊔Q:=by
    have hpullback:=Subgroup.map_le_iff_le_comap.mp hEimage
    rw [Subgroup.comap_map_eq,hker] at hpullback
    simpa only [sup_assoc,sup_comm,sup_left_comm] using hpullback
  have hCQcomm:⁅C,Q⁆≤A:=(commutator_mono hCQ le_rfl).trans hQQ
  have hpre:E≤commutatorPreimage ⊤ C A:=hEjoin.trans (sup_le (sup_le
    (le_commutatorPreimage le_top (by rw [commutator_comm,hC1];exact bot_le))
    (le_commutatorPreimage le_top (by rw [commutator_comm];exact hC2)))
    (le_commutatorPreimage le_top (by rw [commutator_comm];exact hCQcomm)))
  refine ⟨hCQ,?_⟩
  rw [commutator_comm]
  exact (commutator_mono hpre le_rfl).trans
    (commutator_commutatorPreimage_le ⊤ C A le_normalizer_of_normal)
end Subgroup
