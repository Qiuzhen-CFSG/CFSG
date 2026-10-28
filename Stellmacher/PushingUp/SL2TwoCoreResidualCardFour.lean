module
public import Stellmacher.PushingUp.SL2TwoStructure
public import Stellmacher.SectionTwo.LemmaTwoOne

/-!
# The actual four-element core-residual module

A finite group satisfying Section Two's solvable characteristic-two
hypotheses, the exact characteristic-Sylow obstruction (P), and the nested
Frattini `SL₂(2)` condition (A) has canonical action quotient `SL₂(2)`.
Its actual core-residual commutator `W = [O₂(G),O²(G)]` has order four and
equals `[SectionTwo.vSubgroup S,G]` for the supplied Sylow subgroup.
The canonical module itself may retain a fixed central summand; this result
asserts order four only for its full-group commutator.

Even order makes the Sylow subgroup nontrivial. If it were elementary
abelian, it would centralize the two-core and characteristic-two type would
force it to equal that core. Its resulting normality contradicts (P) on the
nontrivial characteristic top subgroup. Thus critical distance zero is
excluded; the established distance-four contradiction leaves distance two.
The shared distance-two natural-data theorem supplies the exact quotient,
cardinality and subgroup equality, retaining the original module and action.

Source: Stellmacher, *Pushing up*, Arch. Math. 46 (1986), (3.2), journal
p.14, specialized to p=2 and n=1; used for the selected factor in (6.1) of
`refs/latex/stellmacher-n-group.tex`, Journal of Algebra 190 (1997), p.30.
-/

namespace Stellmacher.PushingUp

private theorem sylow_not_elementary_of_characteristic_two
    {G : Type*} [Group G] [Finite G]
    (h : SectionTwo.Hypotheses G) (S : Sylow 2 G)
    (hP : ∀ K : Subgroup S, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (S : Subgroup G).subtype).Normal) :
    ¬ IsElementaryAbelian 2 (S : Subgroup G) := by
  intro hEA
  let _ : IsElementaryAbelian 2 (S : Subgroup G) := hEA
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSne : (S : Subgroup G) ≠ ⊥ :=
    S.ne_bot_of_dvd_card (even_iff_two_dvd.mp h.even_order)
  have hQS : pCore 2 G ≤ (S : Subgroup G) :=
    (pCore_isPGroup (p := 2) (G := G)).le_sylow_of_normal S
  have hSQ : (S : Subgroup G) ≤ pCore 2 G := by
    apply le_trans _ h.centralizer_twoCore_le
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact setLike_mul_comm (hQS hq) hs
  have hSnormal : (S : Subgroup G).Normal := by
    rw [le_antisymm hSQ hQS]
    infer_instance
  have htopmap : (⊤ : Subgroup S).map (S : Subgroup G).subtype = (S : Subgroup G) := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have htopne : (⊤ : Subgroup S) ≠ ⊥ := by
    intro hbot
    apply hSne
    rw [← htopmap, hbot, Subgroup.map_bot]
  apply hP ⊤ inferInstance htopne
  rwa [htopmap]

/-- The characteristic-two pushing-up group has its canonical SL₂(2)
action and an actual four-element core-residual commutator. -/
public theorem sl2Two_coreResidual_card_four
    {G : Type*} [Group G] [Finite G]
    (h : SectionTwo.Hypotheses G) (S : Sylow 2 G)
    (hP : ∀ K : Subgroup S, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (S : Subgroup G).subtype).Normal)
    (hA : IsSL2Two ((G ⧸ pCore 2 G) ⧸ frattini (G ⧸ pCore 2 G)))
 :
    let _ : (SectionTwo.vSubgroup S).Normal := Subgroup.normalClosure_normal
    let _ : (SectionTwo.cSubgroup S).Normal := Subgroup.normal_centralizer
    IsSL2Two (G ⧸ SectionTwo.cSubgroup S) ∧
    Nat.card ↥(⁅pCore 2 G, twoResidualAmbient (⊤ : Subgroup G)⁆) = 4 ∧
    ⁅pCore 2 G, twoResidualAmbient (⊤ : Subgroup G)⁆ =
      ⁅SectionTwo.vSubgroup S, (⊤ : Subgroup G)⁆ := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSne : (S : Subgroup G) ≠ ⊥ :=
    S.ne_bot_of_dvd_card (even_iff_two_dvd.mp h.even_order)
  rcases criticalDistance_zero_two_or_four (S : Subgroup G) S rfl hP hSne hA with
    hzero | htwo | hfour
  · exact (sylow_not_elementary_of_characteristic_two h S hP
      (criticalDistance_zero_isElementaryAbelian (S : Subgroup G) S rfl hP hSne hA hzero)).elim
  · exact (criticalDistance_two_structure_and_natural
      (S : Subgroup G) S rfl hP hSne hA htwo).2
  · exact (criticalDistance_four_impossible (S : Subgroup G) S rfl hP hSne hA hfour).elim

end Stellmacher.PushingUp
