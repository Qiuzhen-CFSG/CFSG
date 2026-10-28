module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic

/-!
# A nonnormal point stabilizer on three points

If a point stabilizer does not interchange the other two points, it fixes all three and is normal. Thus a nonnormal stabilizer is transitive on the complementary pair, with the indicated intersection order.

Source: Aschbacher, *Sporadic Groups* (1994), Exercise 2(2), printed p.249.
-/

@[expose] public section

open Subgroup
namespace Theory.GroupTheory.Recognition.AlternatingSixCubicTI
variable {A X:Type*} [Group A] [MulAction A X] [Finite X]

theorem three_point_stabilizer_transitive (hX:Nat.card X=3) (a:X)
    (hn:¬(MulAction.stabilizer A a).Normal) (b c:X) (hb:b≠a) (hc:c≠a):
    ∃g∈MulAction.stabilizer A a,g • b=c := by
  classical
  by_cases hbc:b=c
  · exact ⟨1,one_mem _,by simpa using hbc⟩
  let : Fintype X:=Fintype.ofFinite X
  have hcard:Fintype.card X=3 := by simpa only [Nat.card_eq_fintype_card] using hX
  have huniv:({a,b,c}:Finset X)=Finset.univ := Finset.eq_univ_of_card {a,b,c} (by simp [hbc,hcard,Ne.symm hb,Ne.symm hc])
  have hcover (x:X):x=a ∨ x=b ∨ x=c := by
    have hh:x∈({a,b,c}:Finset X):=huniv ▸ Finset.mem_univ x
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hh
  by_contra hmove
  have hfix (g:A) (hg:g∈MulAction.stabilizer A a) (x:X):g • x=x := by
    have hga:g • a=a:=hg
    have hgb:g • b=b := by
      rcases hcover (g • b) with hh|hh|hh
      · exact (hb ((MulAction.injective g) (hh.trans hga.symm))).elim
      · exact hh
      · exact (hmove ⟨g,hg,hh⟩).elim
    have hgc:g • c=c := by
      rcases hcover (g • c) with hh|hh|hh
      · exact (hc ((MulAction.injective g) (hh.trans hga.symm))).elim
      · exact (hbc ((MulAction.injective g) (hgb.trans hh.symm))).elim
      · exact hh
    rcases hcover x with rfl|rfl|rfl
    · exact hga
    · exact hgb
    · exact hgc
  apply hn
  constructor
  intro g hg k
  change (k*g*k⁻¹) • a=a
  rw [mul_smul,mul_smul,hfix g hg,smul_inv_smul]

theorem three_point_stabilizer_orbit_card (hX:Nat.card X=3) (a:X)
    (hn:¬(MulAction.stabilizer A a).Normal) (b:X) (hb:b≠a):
    Nat.card (MulAction.orbit (MulAction.stabilizer A a) b)=2 := by
  classical
  have he:MulAction.orbit (MulAction.stabilizer A a) b={x:X | x≠a} := by
    ext x
    constructor
    · rintro ⟨g,rfl⟩ he
      have hg:g.val • a=a:=g.property
      exact hb ((MulAction.injective g.val) (he.trans hg.symm))
    · intro hx
      obtain ⟨g,hg,hgx⟩:=three_point_stabilizer_transitive hX a hn b x hb hx
      exact ⟨⟨g,hg⟩,hgx⟩
  rw [he]
  let : Fintype X:=Fintype.ofFinite X
  rw [Nat.card_eq_fintype_card]
  change Fintype.card {x:X // ¬x=a}=2
  rw [Fintype.card_subtype_compl]
  have hh:Fintype.card X=3 := by simpa only [Nat.card_eq_fintype_card] using hX
  simp [hh]

theorem three_point_stabilizer_intersection_card (hX:Nat.card X=3) (a:X)
    (hn:¬(MulAction.stabilizer A a).Normal) (hA:Nat.card (MulAction.stabilizer A a)=6)
    (b:X) (hb:b≠a):
    Nat.card (MulAction.stabilizer A a⊓MulAction.stabilizer A b:Subgroup A)=3 := by
  let S:=MulAction.stabilizer A a
  have he:MulAction.stabilizer S b=(S⊓MulAction.stabilizer A b).subgroupOf S := by
    ext g
    change g.val • b=b ↔ g.val∈S ∧ g.val • b=b
    simp only [g.property,true_and]
  have hh:=Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup S b)
  rw [Nat.card_prod,three_point_stabilizer_orbit_card hX a hn b hb,he,
    Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv,hA] at hh
  change 2*Nat.card (S⊓MulAction.stabilizer A b:Subgroup A)=6 at hh
  change Nat.card (S⊓MulAction.stabilizer A b:Subgroup A)=3
  omega
end Theory.GroupTheory.Recognition.AlternatingSixCubicTI
