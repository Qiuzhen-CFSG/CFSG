module

public import Stellmacher.SectionOne.SL2ProductSylowCoordinates
public import Stellmacher.SectionOne.OneSevenFactorAction
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.OmegaIndependence

public import Theory.GroupAction.FourElementInvolutionLines

/-!
# The Sylow offender in the global SL2 product

The intersection of the ambient Sylow subgroup with a normal product of
one-seven factors is an elementary abelian offender. The group-theoretic
coordinate theorem supplies commuting order-two intersections, generation,
and cardinality two to the number of factors. Each coordinate has full
fixed-point index at most two: its factor fixes the coprime derived-fixed
complement, and a two-group acting on the four-element support fixes at
least two elements by orbit parity. The index of the intersection of these
fixed subgroups is at most the product of their indices, yielding m≤1.

This proves S∩E0 belongs to A(V,S) in Stellmacher (1.7), journal page 19,
following refs/latex/stellmacher-n-group.tex. The proof keeps the full
ambient module and does not require an additional global support split.

The fixed-index argument also exposes the order-two commutator line of each
faithful involution coordinate. Order-two rank-nullity identifies its order
with the fixed-point index, and faithfulness excludes a trivial action.
The factor fixes the coprime complement of its four-element support, so its
full fixed subgroup has index four. Comparing with the involution fixed
index two gives relative index two between these fixed subgroups.
-/

open scoped IsMulCommutative
open Stellmacher.SectionOne.RankOneThreeGroupAssembly
namespace Stellmacher.SectionOne
universe u

private theorem factor_fixed_index_le_two
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (D Q : Subgroup G) (hD : IsOneSevenFactor (V := V) D)
    (hQD : Q ≤ D) (hQcard : Nat.card Q = 2) :
    (FixedPoints.subgroup Q V).index ≤ 2 := by
  let U : Subgroup V := commutatorAction D V
  let C : Subgroup V := FixedPoints.subgroup ((commutator D).map D.subtype) V
  let _ : IsInvariant Q V U :=
    _root_.commutatorAction_isInvariant_of_normalizing_actor Q D
      (hQD.trans D.le_normalizer)
  have hUcard : Nat.card U = 4 := hD.2.2.1
  have hcop : Nat.Coprime (Nat.card ((commutator D).map D.subtype)) (Nat.card V) := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    rw [hD.2.1.2.1, hn]
    exact (show Nat.Coprime 3 2 by decide).pow_right n
  have hcompl : IsCompl C U := by
    dsimp only [C, U]
    rw [oneSevenFactor_full_commutator_eq_derived D hD]
    exact isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := V) (A := ((commutator D).map D.subtype))
      (Group.isSolvable_of_comm fun x y => (IsMulCommutative.is_comm (M := V)).comm x y)
      hcop (inferInstance : IsMulCommutative V)
  have hCfix : C ≤ FixedPoints.subgroup Q V := by
    intro v hv
    rw [FixedPoints.mem_subgroup]
    intro q
    exact oneSevenFactor_fixes_derived_fixedPoints D hD q (hQD q.property) v hv
  have hQp : IsPGroup 2 Q := IsPGroup.of_card (n := 1) (by simpa using hQcard)
  have hmod := hQp.card_modEq_card_fixedPoints U
  have hfixpos : 0 < Nat.card (FixedPoints.subgroup Q U) := Nat.card_pos
  have hfixge : 2 ≤ Nat.card (FixedPoints.subgroup Q U) := by
    change Nat.card U % 2 = Nat.card (FixedPoints.subgroup Q U) % 2 at hmod
    rw [hUcard] at hmod
    omega
  have hfixmap : Nat.card (↥(U ⊓ FixedPoints.subgroup Q V)) =
      Nat.card (FixedPoints.subgroup Q U) := by
    rw [← fixedPoints_subgroup_map_subtype_eq_inf U,
      Subgroup.card_map_of_injective U.subtype_injective]
  have hcomm (B : Subgroup V) : B ≤ Subgroup.centralizer (C : Set V) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact (IsMulCommutative.is_comm (M := V)).comm c b
  have hcardV : Nat.card V = Nat.card C * 4 := by
    have hc := natCard_sup_eq_mul_of_disjoint_of_le_centralizer C U
      hcompl.disjoint (hcomm U)
    simpa [hcompl.sup_eq_top, hUcard] using hc
  have hcardFix : Nat.card C * 2 ≤ Nat.card (FixedPoints.subgroup Q V) := by
    have hdisj : Disjoint C (U ⊓ FixedPoints.subgroup Q V) :=
      hcompl.disjoint.mono_right inf_le_left
    have hc := natCard_sup_eq_mul_of_disjoint_of_le_centralizer C
      (U ⊓ FixedPoints.subgroup Q V) hdisj (hcomm _)
    have hle := Nat.card_le_card_of_injective _
      (Subgroup.inclusion_injective
        (show C ⊔ (U ⊓ FixedPoints.subgroup Q V) ≤ FixedPoints.subgroup Q V from
          sup_le hCfix inf_le_right))
    rw [hc, hfixmap] at hle
    exact (Nat.mul_le_mul_left (Nat.card C) hfixge).trans hle
  have hindex := (FixedPoints.subgroup Q V).index_mul_card
  have hpos : 0 < Nat.card (FixedPoints.subgroup Q V) := Nat.card_pos
  rw [hcardV] at hindex
  nlinarith

/-- A faithful one-seven factor has an order-two commutator line for each involution coordinate. -/
public theorem oneSevenFactor_involution_commutator_card_two
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥)
    (D Q : Subgroup G) (hD : IsOneSevenFactor (V := V) D)
    (hQD : Q ≤ D) (hQcard : Nat.card Q = 2) :
    Nat.card (commutatorAction Q V) = 2 := by
  have hindex := factor_fixed_index_le_two D Q hD hQD hQcard
  have hVcard : 4 ≤ Nat.card V := by
    rw [← hD.2.2.1]
    exact Nat.card_le_card_of_injective _ (commutatorAction D V).subtype_injective
  let _ : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x,hxne,huniq⟩ := (Nat.card_eq_two_iff' (1 : Q)).mp hQcard
  have hxinv : x⁻¹ = x := (huniq x⁻¹ (by simpa using hxne)).trans (huniq x hxne).symm
  have hxx : x ^ 2 = 1 := by
    calc
      x ^ 2 = x * x := pow_two x
      _ = x⁻¹ * x := by rw [hxinv]
      _ = 1 := inv_mul_cancel x
  have hdata := card_two_action_fixed_commutator_card_data (U := V) x ⟨hxne,hxx⟩ hQcard
  have hcount := (FixedPoints.subgroup Q V).index_mul_card
  have hfixpos : 0 < Nat.card (FixedPoints.subgroup Q V) := Nat.card_pos
  have hcommle : Nat.card (commutatorAction Q V) ≤ 2 := by nlinarith [hdata.1]
  have hcommne : commutatorAction Q V ≠ ⊥ := by
    intro hbot
    have htriv := actsTrivially_of_commutatorAction_eq_bot hbot
    have hQfix : Q ≤ fixingSubgroup G (Set.univ : Set V) := by
      intro q hq
      rw [mem_fixingSubgroup_iff]
      intro v _hv
      exact htriv ⟨q,hq⟩ v
    have hQbot : Q = ⊥ := le_bot_iff.mp (hQfix.trans_eq hfaith)
    have hcardone := Subgroup.card_eq_one.mpr hQbot
    omega
  have hcommgt := (Subgroup.one_lt_card_iff_ne_bot _).mpr hcommne
  omega


/-- An involution coordinate fixes twice as many module elements as its full factor. -/
public theorem oneSevenFactor_involution_fixed_relIndex
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥)
    (D Q : Subgroup G) (hD : IsOneSevenFactor (V := V) D)
    (hQD : Q ≤ D) (hQcard : Nat.card Q = 2) :
    (FixedPoints.subgroup D V).relIndex (FixedPoints.subgroup Q V) = 2 := by
  let U : Subgroup V := commutatorAction D V
  let C : Subgroup V := FixedPoints.subgroup ((commutator D).map D.subtype) V
  have hC : C = FixedPoints.subgroup D V := by
    apply le_antisymm
    · intro v hv
      rw [FixedPoints.mem_subgroup]
      intro d
      exact oneSevenFactor_fixes_derived_fixedPoints D hD d d.property v hv
    · intro v hv
      rw [FixedPoints.mem_subgroup]
      intro d
      exact hv ⟨d, Subgroup.map_subtype_le _ d.property⟩
  have hcop : Nat.Coprime (Nat.card ((commutator D).map D.subtype)) (Nat.card V) := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    rw [hD.2.1.2.1, hn]
    exact (show Nat.Coprime 3 2 by decide).pow_right n
  have hcompl : IsCompl C U := by
    dsimp only [C, U]
    rw [oneSevenFactor_full_commutator_eq_derived D hD]
    exact isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := V) (A := ((commutator D).map D.subtype))
      (Group.isSolvable_of_comm fun x y => (IsMulCommutative.is_comm (M := V)).comm x y)
      hcop (inferInstance : IsMulCommutative V)
  have hcardV : Nat.card V = Nat.card (FixedPoints.subgroup D V) * 4 := by
    have hcomm : U ≤ Subgroup.centralizer (C : Set V) := by
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      exact (IsMulCommutative.is_comm (M := V)).comm c b
    have hc := natCard_sup_eq_mul_of_disjoint_of_le_centralizer C U
      hcompl.disjoint hcomm
    rw [hcompl.sup_eq_top, Subgroup.card_top, hC] at hc
    simpa only [U, hD.2.2.1] using hc
  have hindexD : (FixedPoints.subgroup D V).index = 4 := by
    have hcount := (FixedPoints.subgroup D V).index_mul_card
    have hpos : 0 < Nat.card (FixedPoints.subgroup D V) := Nat.card_pos
    nlinarith
  have hVcard : 4 ≤ Nat.card V := by
    rw [← hD.2.2.1]
    exact Nat.card_le_card_of_injective _ (commutatorAction D V).subtype_injective
  let _ : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x, hxne, huniq⟩ := (Nat.card_eq_two_iff' (1 : Q)).mp hQcard
  have hxinv : x⁻¹ = x := (huniq x⁻¹ (by simpa using hxne)).trans (huniq x hxne).symm
  have hxx : x ^ 2 = 1 := by
    calc
      x ^ 2 = x * x := pow_two x
      _ = x⁻¹ * x := by rw [hxinv]
      _ = 1 := inv_mul_cancel x
  have hdata := card_two_action_fixed_commutator_card_data (U := V) x ⟨hxne, hxx⟩ hQcard
  have hcommcard := oneSevenFactor_involution_commutator_card_two hfaith D Q hD hQD hQcard
  have hindexQ : (FixedPoints.subgroup Q V).index = 2 := by
    have hcount := (FixedPoints.subgroup Q V).index_mul_card
    have hfixpos : 0 < Nat.card (FixedPoints.subgroup Q V) := Nat.card_pos
    rw [hcommcard] at hdata
    nlinarith [hdata.1]
  have hle : FixedPoints.subgroup D V ≤ FixedPoints.subgroup Q V := by
    intro v hv q
    exact hv ⟨q, hQD q.property⟩
  have hindex := Subgroup.relIndex_mul_index hle
  rw [hindexD, hindexQ] at hindex
  omega

private theorem offender_of_coordinate_data
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (S : Sylow 2 G) (E : Subgroup G) (F : Finset (Subgroup G))
    (hF : ∀ D ∈ F, IsOneSevenFactor (V := V) D)
    (helem : IsElementaryAbelian 2 (↥((S : Subgroup G) ⊓ E)))
    (hgen : ((S : Subgroup G) ⊓ E) =
      ⨆ D : {D : Subgroup G // D ∈ F}, (S : Subgroup G) ⊓ D.val)
    (hcard : Nat.card (↥((S : Subgroup G) ⊓ E)) = 2 ^ F.card)
    (hcoord : ∀ D ∈ F, Nat.card (↥((S : Subgroup G) ⊓ D)) = 2) :
    oneA (G := G) (V := V) (S : Subgroup G) ((S : Subgroup G) ⊓ E) := by
  classical
  let I := {D : Subgroup G // D ∈ F}
  let Q (D : I) : Subgroup G := (S : Subgroup G) ⊓ D.val
  have hfix : FixedPoints.subgroup (↥((S : Subgroup G) ⊓ E)) V =
      ⨅ D : I, FixedPoints.subgroup (Q D) V := by
    rw [hgen]
    apply SetLike.coe_injective
    change MulAction.fixedPoints (↥(⨆ D : I, Q D)) V = _
    rw [fixedPoints_subgroup_iSup]
    simp only [Subgroup.coe_iInf]
    rfl
  have hindex : (FixedPoints.subgroup (↥((S : Subgroup G) ⊓ E)) V).index ≤
      Nat.card (↥((S : Subgroup G) ⊓ E)) := by
    rw [hfix, hcard]
    refine (Subgroup.index_iInf_le _).trans ?_
    have hle : ∏ D : I, (FixedPoints.subgroup (Q D) V).index ≤ ∏ _D : I, 2 := by
      apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
      intro D hD
      exact factor_fixed_index_le_two D.val (Q D) (hF D.val D.property)
        inf_le_right (hcoord D.val D.property)
    simpa [I] using hle
  refine ⟨inf_le_left, helem, ?_⟩
  have hm := (FixedPoints.subgroup (↥((S : Subgroup G) ⊓ E)) V).index_mul_card
  have hpos : 0 < (Nat.card (FixedPoints.subgroup (↥((S : Subgroup G) ⊓ E)) V) : ℚ) := by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card (FixedPoints.subgroup (↥((S : Subgroup G) ⊓ E)) V))
  have hTpos : 0 < (Nat.card (↥((S : Subgroup G) ⊓ E)) : ℚ) := by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card (↥((S : Subgroup G) ⊓ E)))
  unfold m
  apply (div_le_iff₀ (mul_pos hpos hTpos)).mpr
  have hbound : Nat.card V ≤ Nat.card (FixedPoints.subgroup (↥((S : Subgroup G) ⊓ E)) V) *
      Nat.card (↥((S : Subgroup G) ⊓ E)) := by nlinarith
  exact_mod_cast (by simpa using hbound)


public theorem oneSevenFactor_product_sylow_oneA
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (_h : Hypotheses G V) (S : Sylow 2 G) (E : Subgroup G)
    (hEnormal : E.Normal) (F : Finset (Subgroup G))
    (hprod : IsInternalDirectProduct E F)
    (hF : ∀ D ∈ F, IsOneSevenFactor (V := V) D) :
    oneA (G := G) (V := V) (S : Subgroup G) ((S : Subgroup G) ⊓ E) := by
  obtain ⟨helem, hgen, hcard, hcoord⟩ :=
    sl2_product_sylow_coordinates S E hEnormal F hprod (fun D hD => (hF D hD).1)
  exact offender_of_coordinate_data S E F hF helem hgen hcard hcoord

end Stellmacher.SectionOne

