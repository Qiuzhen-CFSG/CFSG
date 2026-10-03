module
public import Theory.GroupTheory.Commutator.CrossFixedFactors
public import Theory.GroupTheory.Commutator.CentralFourCoprimeDerived
public import Theory.GroupTheory.CoprimeCentralizerDecomposition
public import Theory.PGroup

/-!
# A central derived subgroup from two opposite coprime fixed factors

Let U be a finite two-group with V ≤ U and Z ≤ V. Two commuting
three-groups normalize U,V and centralize Z, while Z centralizes U.
Write Qi=C_U(Ai) and Wi=C_V(Ai). Suppose the two Qi generate U, the Wi
generate V and intersect in Z, the full actor fixes only points in Z,
[U,U] ≤ V, and [V,U] ≤ Z. If each literal Qi/Wi is elementary of order
four, then [U,U] ≤ Z. All quotient normality witnesses are retained.

Commuting actors normalize the opposite fixed groups. Coprime splitting
gives Qi=[Qi,Aj]Z. The relative three-subgroups argument bounds the cross
commutator by both W1 and W2. The central elementary-four quotient theorem
puts each individual derived subgroup in Z, since the opposite actor's
fixed subgroup lies in Z. The generating join then bounds the full derived
subgroup. Commutator preimages handle the joins using only relative
normalization, without global normality assumptions.

This is the algebraic ending of the nine-alternative contradiction in
Stellmacher (10.1), printed p.64, between (18) and (19). The campaign caller
must supply the actual fixed factors and their quotient cardinalities.
-/

namespace Subgroup
private theorem join_commutator_bound
    {G:Type*} [Group G] (U Q1 Q2 E Z:Subgroup G)
    (hgen:U=Q1⊔Q2) (hUZ:U≤normalizer (Z:Set G))
    (h1:⁅Q1,E⁆≤Z) (h2:⁅Q2,E⁆≤Z) : ⁅U,E⁆≤Z := by
  have h1' : Q1≤commutatorPreimage U E Z :=
    le_commutatorPreimage (le_sup_left.trans hgen.ge) h1
  have h2' : Q2≤commutatorPreimage U E Z :=
    le_commutatorPreimage (le_sup_right.trans hgen.ge) h2
  exact (commutator_mono (hgen.le.trans (sup_le h1' h2')) le_rfl).trans
    (commutator_commutatorPreimage_le U E Z hUZ)

public theorem commutator_le_of_two_coprime_fixed_factors
    {G:Type*} [Group G] [Finite G]
    (U V Z A1 A2 Q1 Q2 W1 W2:Subgroup G)
    (hU:IsPGroup 2 U) (hA1:IsPGroup 3 A1) (hA2:IsPGroup 3 A2)
    (hZV:Z≤V) (hVU:V≤U)
    (hZU:Z≤centralizer (U:Set G))
    (hZA1:Z≤centralizer (A1:Set G)) (hZA2:Z≤centralizer (A2:Set G))
    (hA1U:A1≤normalizer (U:Set G)) (hA2U:A2≤normalizer (U:Set G))
    (hA1V:A1≤normalizer (V:Set G)) (hA2V:A2≤normalizer (V:Set G))
    (hAA:A1≤centralizer (A2:Set G))
    (hQ1:Q1=U⊓centralizer (A1:Set G)) (hQ2:Q2=U⊓centralizer (A2:Set G))
    (hW1:W1=V⊓centralizer (A1:Set G)) (hW2:W2=V⊓centralizer (A2:Set G))
    (hUgen:U=Q1⊔Q2) (hVgen:V=W1⊔W2) (hinter:W1⊓W2=Z)
    (hfixed:U⊓centralizer ((A1⊔A2:Subgroup G):Set G)≤Z)
    (hUU:⁅U,U⁆≤V) (hVUcomm:⁅V,U⁆≤Z)
    (hN1:(W1.subgroupOf Q1).Normal) (hN2:(W2.subgroupOf Q2).Normal) :
    let _:=hN1
    let _:=hN2
    IsElementaryAbelian 2 (Q1⧸W1.subgroupOf Q1) → Nat.card (Q1⧸W1.subgroupOf Q1)=4 →
    IsElementaryAbelian 2 (Q2⧸W2.subgroupOf Q2) → Nat.card (Q2⧸W2.subgroupOf Q2)=4 →
    ⁅U,U⁆≤Z := by
  let _:=hN1
  let _:=hN2
  dsimp only
  intro hel1 hc1 hel2 hc2
  let _ : Fact (Nat.Prime 2):=⟨Nat.prime_two⟩
  let _ : Fact (Nat.Prime 3):=⟨Nat.prime_three⟩
  have hQ1U:Q1≤U:=hQ1.le.trans inf_le_left
  have hQ2U:Q2≤U:=hQ2.le.trans inf_le_left
  have hW1V:W1≤V:=hW1.le.trans inf_le_left
  have hW2V:W2≤V:=hW2.le.trans inf_le_left
  have hW1Q:W1≤Q1:=hW1.le.trans ((inf_le_inf hVU le_rfl).trans hQ1.ge)
  have hW2Q:W2≤Q2:=hW2.le.trans ((inf_le_inf hVU le_rfl).trans hQ2.ge)
  have hZ1:Z≤W1:=(le_inf hZV hZA1).trans hW1.ge
  have hZ2:Z≤W2:=(le_inf hZV hZA2).trans hW2.ge
  have hQ1c:Q1≤centralizer (A1:Set G):=hQ1.le.trans inf_le_right
  have hQ2c:Q2≤centralizer (A2:Set G):=hQ2.le.trans inf_le_right
  have hW1c:W1≤centralizer (A1:Set G):=hW1.le.trans inf_le_right
  have hW2c:W2≤centralizer (A2:Set G):=hW2.le.trans inf_le_right
  have hA2A1:A2≤centralizer (A1:Set G):=le_centralizer_iff.mp hAA
  have hA1Q2:A1≤normalizer (Q2:Set G):=by
    rw [hQ2]
    exact (le_inf hA1U (hAA.trans (centralizer (A2:Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hA2Q1:A2≤normalizer (Q1:Set G):=by
    rw [hQ1]
    exact (le_inf hA2U (hA2A1.trans (centralizer (A1:Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hA1W2:A1≤normalizer (W2:Set G):=by
    rw [hW2]
    exact (le_inf hA1V (hAA.trans (centralizer (A2:Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hA2W1:A2≤normalizer (W1:Set G):=by
    rw [hW1]
    exact (le_inf hA2V (hA2A1.trans (centralizer (A1:Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hUZ:U≤normalizer (Z:Set G):=
    (le_centralizer_iff.mp hZU).trans (centralizer_le_normalizer _)
  have hA1Z:A1≤normalizer (Z:Set G):=
    (le_centralizer_iff.mp hZA1).trans (centralizer_le_normalizer _)
  have hA2Z:A2≤normalizer (Z:Set G):=
    (le_centralizer_iff.mp hZA2).trans (centralizer_le_normalizer _)
  have hUW1:U≤normalizer (W1:Set G):=le_normalizer_iff_commutator_le_left.mpr
    (((commutator_mono hW1V le_rfl).trans hVUcomm).trans hZ1)
  have hUW2:U≤normalizer (W2:Set G):=le_normalizer_iff_commutator_le_left.mpr
    (((commutator_mono hW2V le_rfl).trans hVUcomm).trans hZ2)
  have hfix1:Q1⊓centralizer (A2:Set G)≤Z:=by
    apply le_trans (le_inf (inf_le_left.trans hQ1U) ?_) hfixed
    exact le_centralizer_iff.mp (sup_le
      (le_centralizer_iff.mp (inf_le_left.trans hQ1c))
      (le_centralizer_iff.mp inf_le_right))
  have hfix2:Q2⊓centralizer (A1:Set G)≤Z:=by
    apply le_trans (le_inf (inf_le_left.trans hQ2U) ?_) hfixed
    exact le_centralizer_iff.mp (sup_le
      (le_centralizer_iff.mp inf_le_right)
      (le_centralizer_iff.mp (inf_le_left.trans hQ2c)))
  have hQ1two:=hU.to_le hQ1U
  have hQ2two:=hU.to_le hQ2U
  let _ : Group.IsNilpotent Q1:=hQ1two.isNilpotent
  let _ : Group.IsNilpotent Q2:=hQ2two.isNilpotent
  have hfull1:Q1=⁅Q1,A2⁆⊔Z:=by
    have hsplit:=eq_commutator_sup_centralizer_of_solvable_coprime Q1 A2 hA2Q1 inferInstance
      (IsPGroup.coprime_card_of_ne 3 2 (by decide) A2 Q1 hA2 hQ1two)
    have hfixeq:Q1⊓centralizer (A2:Set G)=Z:=le_antisymm hfix1
      (le_inf (hZ1.trans hW1Q) hZA2)
    rwa [hfixeq] at hsplit
  have hfull2:Q2=⁅Q2,A1⁆⊔Z:=by
    have hsplit:=eq_commutator_sup_centralizer_of_solvable_coprime Q2 A1 hA1Q2 inferInstance
      (IsPGroup.coprime_card_of_ne 3 2 (by decide) A1 Q2 hA1 hQ2two)
    have hfixeq:Q2⊓centralizer (A1:Set G)=Z:=le_antisymm hfix2
      (le_inf (hZ2.trans hW2Q) hZA1)
    rwa [hfixeq] at hsplit
  have hVA1:⁅V,A1⁆≤W2:=join_commutator_bound V W1 W2 A1 W2 hVgen
    (hVU.trans hUW2) ((commutator_eq_bot_iff_le_centralizer.mpr hW1c).le.trans bot_le)
    (le_normalizer_iff_commutator_le_left.mp hA1W2)
  have hVA2:⁅V,A2⁆≤W1:=join_commutator_bound V W1 W2 A2 W1 hVgen
    (hVU.trans hUW1) (le_normalizer_iff_commutator_le_left.mp hA2W1)
    ((commutator_eq_bot_iff_le_centralizer.mpr hW2c).le.trans bot_le)
  have hcross:⁅Q1,Q2⁆≤V:=(commutator_mono hQ1U hQ2U).trans hUU
  have hcrossZ:⁅Q1,Q2⁆≤Z:=by
    rw [←hinter]
    apply le_inf
    · rw [commutator_comm Q1 Q2]
      exact commutator_le_of_opposite_full_factor Q2 Q1 A2 Z V W1
        (hQ2U.trans hUW1) (hQ1U.trans hUW1) hA2W1
        (by rwa [commutator_comm]) hVA2
        (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hQ2c)) hfull1
        ((commutator_eq_bot_iff_le_centralizer.mpr
          (hZU.trans (centralizer_le hQ2U))).le.trans bot_le)
    · exact commutator_le_of_opposite_full_factor Q1 Q2 A1 Z V W2
        (hQ1U.trans hUW2) (hQ2U.trans hUW2) hA1W2 hcross hVA1
        (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hQ1c)) hfull2
        ((commutator_eq_bot_iff_le_centralizer.mpr
          (hZU.trans (centralizer_le hQ1U))).le.trans bot_le)
  have hder1:⁅Q1,Q1⁆≤Z:=commutator_le_of_central_four_quotient_coprime_fixed Q1 W1 Z A2
    hZ1 hW1Q (hZU.trans (centralizer_le hQ1U))
    ((commutator_mono hW1V hQ1U).trans hVUcomm)
    hQ1two hA2 hA2Q1 hA2Z hfix1 hN1 hel1 hc1
  have hder2:⁅Q2,Q2⁆≤Z:=commutator_le_of_central_four_quotient_coprime_fixed Q2 W2 Z A1
    hZ2 hW2Q (hZU.trans (centralizer_le hQ2U))
    ((commutator_mono hW2V hQ2U).trans hVUcomm)
    hQ2two hA1 hA1Q2 hA1Z hfix2 hN2 hel2 hc2
  have hcross':⁅Q2,Q1⁆≤Z:=by rwa [commutator_comm]
  have hU1:⁅U,Q1⁆≤Z:=join_commutator_bound U Q1 Q2 Q1 Z hUgen hUZ hder1 hcross'
  have hU2:⁅U,Q2⁆≤Z:=join_commutator_bound U Q1 Q2 Q2 Z hUgen hUZ hcrossZ hder2
  apply join_commutator_bound U Q1 Q2 U Z hUgen hUZ
  · rwa [commutator_comm]
  · rwa [commutator_comm]
end Subgroup
