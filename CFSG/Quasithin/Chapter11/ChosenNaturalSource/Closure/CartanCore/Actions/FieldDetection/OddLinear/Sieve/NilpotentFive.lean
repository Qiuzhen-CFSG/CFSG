module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.OddLinear.Sieve.Nilpotent
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.Even
public import Theory.SpecificGroups.GL2.FiveConjugation
public import Theory.AtlasPort.LinearGroups.SL2Order

/-!
# The primary plane prevents squaring a five-element

Every full primary Frattini quotient in the nilpotent-Fitting A.3.6 row
is an elementary plane. Its automorphism group embeds faithfully in
GL₂(p). For p>5, the two-dimensional trace restriction prevents any
automorphism of the original group from squaring an order-five action
on that plane. The original moved-component consumer supplies such a
prime p, retaining both extraspecial and arbitrary-exponent homocyclic
primary factors.

This is a restriction on the actual primary action. To finish 11.5.6(3),
qt-d-1222-natural-closure-cartan must still connect it to the action of T
on the SL₂(5) Fitting quotient and exclude the ambient scalar actor.
The parent qt-d-1222-natural-closure retains the preceding geometry.
Source: Aschbacher--Smith A.3.6, pp.43--45, and 11.5.6(3), pp.780--781.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.Chapter1.Section02
open CFSG.Quasithin.Chapter1.RadicalActions
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.OddLinear

/-- No automorphism of the original nilpotent-Fitting group squares a
five-element in its actual primary Frattini action when p>5. -/
theorem nilpotent_primary_five_not_squared {Q : Type*} [Group Q] [Finite Q]
    (hn : A36Nilpotent Q) {p : ℕ} [Fact p.Prime] (hp5 : 5 < p)
    (hpF : p ∣ Nat.card (fittingSubgroup Q)) (a : MulAut Q) (g : Q)
    (ho : orderOf (FittingActions.coreFrattiniAction p Q g) = 5) :
    FittingActions.coreFrattiniAction p Q (a g) ≠
      (FittingActions.coreFrattiniAction p Q g) ^ 2 := by
  obtain ⟨hel,hcard⟩ := nilpotent_primary_frattini_shape hn hpF
  let := hel
  obtain ⟨f,hf⟩ := IsElementaryAbelian.exists_injective_mulAut_generalLinear_of_card_le
    (p := p) (n := 2) (pCore p Q ⧸ frattini (pCore p Q)) hcard.le
  have h5 : (5 : ZMod p) ≠ 0 := by
    intro hz
    exact (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 5) hp5)
      ((ZMod.natCast_eq_zero_iff 5 p).mp hz)
  intro he
  apply Matrix.GeneralLinearGroup.not_conjugate_square_of_order_five
    (f (FittingActions.coreFrattiniAction p Q g))
    (f (primaryFrattiniAut p Q a)) h5
    ((orderOf_injective f hf _).trans ho)
  rw [← map_inv, ← map_mul, ← map_mul, primaryFrattiniAut_conjugation, he, map_pow]

/-- The Fitting quotient supplies an actual five-element on the same plane. -/
theorem nilpotent_primary_exists_five_not_squared {Q : Type*} [Group Q] [Finite Q]
    [Group.IsPerfect Q] (hn : A36Nilpotent Q) (hc : A36Common Q)
    {p : ℕ} [Fact p.Prime] (hp5 : 5 < p)
    (hpF : p ∣ Nat.card (fittingSubgroup Q)) :
    ∃ g : Q, orderOf (FittingActions.coreFrattiniAction p Q g) = 5 ∧
      ∀ a : MulAut Q, FittingActions.coreFrattiniAction p Q (a g) ≠
        (FittingActions.coreFrattiniAction p Q g) ^ 2 := by
  let r := FittingActions.coreFrattiniAction p Q
  have hk : r.ker = fittingSubgroup Q :=
    ((FittingActions.nilpotent_frattini_actions hn hc).2.2 p hpF).2.1
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hn.2.2.1
  have hcard : Nat.card r.range = 120 := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange r).toEquiv, hk,
      ← hn.1, Nat.card_congr e.toEquiv, Atlas.card_sl_two, hF]
    norm_num
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := r.range) 5
    (by rw [hcard]; norm_num)
  obtain ⟨g,hg⟩ := z.property
  have ho : orderOf (r g) = 5 := by
    rw [hg, Subgroup.orderOf_coe, hz]
  exact ⟨g,ho,fun a => nilpotent_primary_five_not_squared hn hp5 hpF a g ho⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.OddLinear

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
open CartanActions.FieldDetection.OddLinear
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
    {L V : Subgroup G} {D : ChosenModule T L V} (E : Geometry D)

/-- The remaining original moved component has a primary plane on which
no automorphism of its literal quotient can square a five-element. -/
theorem moved_component_primary_five_not_squared (hp : E.point ≠ ⊥)
    (hT : (T : Subgroup G) ≤ E.G₁) (hX : E.X ≤ E.G₁)
    (c : LocalGeometry.Coordinates D E.input.field)
    (hcart : LocalGeometry.IsCartan T L E.X)
    (hXR : E.X ≤ normalizer (E.R₁ : Set G))
    (hCX : E.X ⊓ centralizer (E.V₁ : Set G) ≤ E.L₁)
    (hz : center (E.L₁ ⧸ pCore 2 E.L₁) = ⊥)
    (hNG : normalizer (T : Set G) ≤ E.M)
    (hthree : 1 ≤ primeRank 3 E.L₁)
    (hexception : E.L₁ < E.K → Even E.input.field.degree)
    {I : Subgroup G} (hI : Source.ComponentIn E.Y I)
    (hmoved : ¬ ⁅I,E.X⁆ ≤ E.Y.pCoreIn 2) :
    let B := (I.subgroupOf E.G₁).map (QuotientGroup.mk' (pCore 2 E.G₁))
    A36Nilpotent B ∧ A36Common B ∧ primeRank 3 B ≤ 1 ∧
      ∃ p : ℕ, p.Prime ∧ 5 < p ∧ p ∣ Nat.card (fittingSubgroup B) ∧
        ∃ g : B, orderOf (FittingActions.coreFrattiniAction p B g) = 5 ∧
          ∀ a : MulAut B, FittingActions.coreFrattiniAction p B (a g) ≠
            (FittingActions.coreFrattiniAction p B g) ^ 2 := by
  have hc := E.cartan_coprime_of_local_action hp hX hcart.odd
    (fun _ hprime hdiv => (c.cartan_primeRank hcart hprime hdiv).ge) hCX hz
  have hr := E.three_rank_Y_le_one hp hc hexception hz hthree
  have ho : Odd E.input.field.degree := by
    apply Nat.not_even_iff_odd.mp
    intro he
    exact hmoved ((E.cartan_actions_of_even_marked hp hT hX c hcart hXR hCX hz hNG he).1 I hI)
  obtain ⟨hn,hcommon,hrB,_,_,_,_,p,hpp,hp5,hpF,_⟩ :=
    E.moved_component_primary_scalar_case hp hT hX c hcart hXR hCX hz hNG hr ho hI hmoved
  let : Fact p.Prime := ⟨hpp⟩
  let B := (I.subgroupOf E.G₁).map (QuotientGroup.mk' (pCore 2 E.G₁))
  let := pCore_isNilpotent (p := 2) (G := E.G₁)
  let : Group.IsPerfect B := ((E.component_in_point_normalizer hI).map_quotient _).perfect
  exact ⟨hn,hcommon,hrB,p,hpp,hp5,hpF,
    nilpotent_primary_exists_five_not_squared hn hcommon hp5 hpF⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
