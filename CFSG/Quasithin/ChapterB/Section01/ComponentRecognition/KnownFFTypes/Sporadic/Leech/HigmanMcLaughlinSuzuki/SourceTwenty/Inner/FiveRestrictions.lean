module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceTwenty.Inner.Inputs
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceTwenty.Inner.FiveRestrictions.Actors
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.AbsoluteWindow.FiveCenter
public import Theory.Representation.ExtraspecialQuinticDisplacement

/-!
# Universal order-five restrictions for the inner HS degree-twenty argument

The certified nonabelian subgroup P of order 125 is Sylow and extraspecial.
The existing five-center multiplicity calculation makes Z(P) fixed-point-free
in every faithful degree-twenty representation. A noncentral five-element fixes
one fifth of the module by the six-line hyperplane calculation. Thus every
five-element of P moves sixteen or twenty dimensions; Sylow conjugacy covers
all order-five elements of the actual HS carrier.

The checked inversion certificates use the literal e0 and ClassCoverage.t.
The latter inverts a conjugate of Z(P), which is therefore fixed-point-free on
the original representation. This proves every field of FiveRestrictions,
uniformly in the module. Faithfulness and dimension twenty suffice; neither
irreducibility nor inherited simplicity is required by this proof.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1,
HS paragraph, author preprint pp.16--17; Aschbacher--Smith K.4, printed p.457.
The theorem `fiveRestrictions` has exactly the interface consumed by the
parent `Inner.estimates_of_inputs`; no model-comparison premise remains.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.Twenty.Inner
open Subgroup Representation.BinaryOffender
open _root_.Sporadic.LeechRelated.HS
local notation "P₅" => _root_.Sporadic.LeechRelated.HS.FiveSubgroup.subgroup
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private instance : IsExtraspecial 5 P₅ :=
  IsExtraspecial.of_noncommutative_card_prime_cube
    FiveSubgroup.card_subgroup FiveSubgroup.subgroup_not_commutative

private theorem five_index : (P₅).index = 354816 := by
  have h := (P₅).card_mul_index
  rw [FiveSubgroup.card_subgroup, NormalizerIndex.card_carrier] at h
  omega

private def fiveSylow : Sylow 5 Carrier :=
  FiveSubgroup.subgroup_isPGroup.toSylow (by rw [five_index]; decide)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

private theorem center_fixed (σ : Representation (ZMod 2) Carrier V)
    (hf : Function.Injective σ) (hd : Module.finrank (ZMod 2) V = 20) :
    fixedSpace (σ.comp (P₅).subtype) (center P₅) = ⊥ := by
  rw [fixedSpace_comp_map]
  exact AbsoluteWindow.fiveCenter_fixed_eq_bot_of_finrank_twenty σ hf hd

private theorem subgroup_five_bound (σ : Representation (ZMod 2) Carrier V)
    (hf : Function.Injective σ) (hd : Module.finrank (ZMod 2) V = 20)
    (y : P₅) (hy : orderOf y = 5) :
    16 ≤ fixedCodim (σ.comp (P₅).subtype) (zpowers y) := by
  have hc := center_fixed σ hf hd
  have hr := fixedCodim_add_finrank (σ.comp (P₅).subtype) (zpowers y)
  by_cases hz : y ∈ center P₅
  · have hZ : zpowers y = center P₅ := by
      apply eq_of_le_of_card_ge (zpowers_le.mpr hz)
      rw [Nat.card_zpowers, hy, IsExtraspecial.center_order_p 5 P₅]
    have hc' : fixedSpace (σ.comp (P₅).subtype) (zpowers y) = ⊥ := by
      rw [hZ]
      exact hc
    rw [hc', finrank_bot, hd] at hr
    omega
  · have h := Representation.BinaryCoprimeDegree.extraspecial_quintic_fixed_finrank
      (σ.comp (P₅).subtype) hc hy hz
    rw [hd] at h hr
    omega

/-- Every five-element moves at least sixteen dimensions in every faithful
binary degree-twenty HS representation. Sylow conjugacy makes the local
extraspecial computation exhaustive. -/
theorem order_five_fixedCodim_ge_sixteen (σ : Representation (ZMod 2) Carrier V)
    (hf : Function.Injective σ) (hd : Module.finrank (ZMod 2) V = 20)
    (x : Carrier) (hx : orderOf x = 5) : 16 ≤ fixedCodim σ (zpowers x) := by
  obtain ⟨y, hxy⟩ := fiveSylow.exists_isConj_of_orderOf_eq_prime_pow
    (n := 1) (by simpa using hx)
  obtain ⟨g, hg⟩ := isConj_iff.mp hxy
  let yP : P₅ := ⟨y.val, y.property⟩
  have hyo : orderOf (y : Carrier) = 5 := by
    rw [← hg]
    exact ((MulAut.conj g).orderOf_eq x).trans hx
  have hy : orderOf yP = 5 :=
    (orderOf_injective (P₅).subtype (P₅).subtype_injective yP).symm.trans hyo
  have hb := subgroup_five_bound σ hf hd yP hy
  unfold fixedCodim at hb
  rw [fixedSpace_comp_map, MonoidHom.map_zpowers] at hb
  change 16 ≤ fixedCodim σ (zpowers (y : Carrier)) at hb
  rw [← hg, fixedCodim_zpowers_conj] at hb
  exact hb

/-- The marked product involution inverts a conjugate of the literal
five-center, hence a fixed-point-free five-element on the original module. -/
theorem productFive_fixedSpace_eq_bot (σ : Representation (ZMod 2) Carrier V)
    (hf : Function.Injective σ) (hd : Module.finrank (ZMod 2) V = 20) :
    fixedSpace σ (zpowers FiveActors.productFive) = ⊥ := by
  obtain ⟨g, hg⟩ := FiveActors.productFive_conjugate_center
  rw [hg]
  apply Submodule.finrank_eq_zero.mp
  have he := (fixedSpaceConjEquiv σ ((center P₅).map (P₅).subtype) g).finrank_eq
  have hz : fixedSpace σ ((center P₅).map (P₅).subtype) = ⊥ :=
    AbsoluteWindow.fiveCenter_fixed_eq_bot_of_finrank_twenty σ hf hd
  rw [hz, finrank_bot] at he
  exact he.symm

/-- The exact three order-five inputs used by the inner HS calculation.
The proof is uniform in the representation and needs only faithfulness and
degree twenty. -/
theorem fiveRestrictions_of_faithful (σ : Representation (ZMod 2) HS V)
    (hf : Function.Injective σ) (hd : Module.finrank (ZMod 2) V = 20) :
    FiveRestrictions σ where
  order_five := order_five_fixedCodim_ge_sixteen σ hf hd
  core_inverts := ⟨FiveActors.coreFive, FiveActors.coreFive_order, FiveActors.core_inverts⟩
  product_inverts_free := ⟨FiveActors.productFive, FiveActors.productFive_order,
    FiveActors.product_inverts, productFive_fixedSpace_eq_bot σ hf hd⟩

/-- Specialization with the exact faithful irreducible interface consumed by
`Inner.estimates_of_inputs`. No character-table or model-comparison premise
remains. -/
theorem fiveRestrictions (σ : Representation (ZMod 2) HS V)
    (hf : Function.Injective σ) (_hi : σ.IsIrreducible)
    (hd : Module.finrank (ZMod 2) V = 20) : FiveRestrictions σ :=
  fiveRestrictions_of_faithful σ hf hd

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.Twenty.Inner
