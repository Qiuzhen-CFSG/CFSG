module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Witness.SupercriticalNineSource.UpperXi
public import Theory.SpecificGroups.GL2.PrimeThreeFiveResidual.Coordinates
public import Theory.Frattini.PGroup
public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms

/-!
# Source applications of the small prime-plane action calculation

Once a normal supercritical subgroup has one of the two noncyclic source
shapes, its original nontrivial two-core action supplies Sylow irreducibility
and uppercase membership of its residual lift. At five an actual cubic
actor makes the lift positive, contradicting the genuine preceding
15.4.2(3) exclusion. At three the original action on P has order 24.

The supercritical selection and the extraspecial-three exclusion are
separate steps of the source argument; the hypotheses here state exactly
which outputs of that selection are consumed.

Source: Aschbacher--Smith 15.4.10, printed p.1159.
-/

public section
open Subgroup Matrix
namespace CFSG.Quasithin.Chapter15.Section04.CentralizerWitness.SupercriticalNineSource
open FamilySource Matrix.GeneralLinearGroup.PrimeThreeFiveResidual
variable {G : Type*} [Group G] [Finite G]

private theorem shape_perfect {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {P : Type*} [Group P] (hs : Chapter1.XiOddQuotient p P) : IsPPerfect 2 P := by
  apply (pResidual_eq_top_iff 2 P).mp
  apply top_unique
  intro x _
  exact mem_pResidual_of_orderOf_coprime
    ((hs.isPGroup.orderOf_coprime
      ((Nat.coprime_primes (Fact.out : p.Prime) Nat.prime_two).mpr hp) x).symm)

private theorem shape_frattini_card {p : ℕ} [Fact p.Prime]
    {P : Type*} [Group P] [Finite P] (hs : Chapter1.XiOddQuotient p P) :
    Nat.card (P ⧸ frattini P) = p ^ 2 := by
  let : Fact (IsPGroup p P) := ⟨hs.isPGroup⟩
  rcases hs with ⟨he, hc⟩ | ⟨he, hc, _⟩
  · let : IsElementaryAbelian p P := he
    exact (Nat.card_congr (frattiniQuotientEquivOfIsElementaryAbelian (p := p)).toEquiv).trans hc
  · let : IsExtraspecial p P := he
    have hf : Nat.card (frattini P) = p := by
      rw [IsExtraspecial.frattini_eq_center (p := p), IsExtraspecial.center_order_p p P]
    have hh := (frattini P).index_mul_card
    change Nat.card (P ⧸ frattini P) * Nat.card (frattini P) = Nat.card P at hh
    rw [hf, hc, show 3 = 2 + 1 from rfl, pow_succ] at hh
    exact mul_right_cancel₀ (Fact.out : p.Prime).ne_zero hh

omit [Finite G] in
private theorem member_core_le_sylow (T : Sylow 2 G) (X Z : Subgroup G)
    (hX : X ∈ NormalCentralizerXi (T : Subgroup G) Z) : X.pCoreIn 2 ≤ (T : Subgroup G) := by
  have hn : (T : Subgroup G) ≤ normalizer (X.pCoreIn 2 : Set G) :=
    hX.1.1.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  exact sup_eq_right.mp (T.is_maximal'
    ((isPGroup_pCoreIn 2 X).to_sup_of_normal_left' T.isPGroup' hn) le_sup_right)

/-- Nontrivial original core action makes the actual Sylow action on the
Frattini quotient irreducible in each of the two source characteristics. -/
theorem sylow_frattini_irreducible {p : ℕ} [Fact p.Prime] (hp : p = 3 ∨ p = 5)
    (T : Sylow 2 G) (M X Z : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hXM : X ≤ M)
    (hX : X ∈ NormalCentralizerXi (T : Subgroup G) Z)
    (hX3 : Nat.card (X ⧸ pCore 2 X) = 3)
    (P : Subgroup (CoreQuotient M)) [P.Normal] (hs : Chapter1.XiOddQuotient p P)
    (hne : (pCore 2 X).map ((MulAut.conjNormal : CoreQuotient M →* MulAut P).comp
      ((quotientMap M).comp (inclusion hXM))) ≠ ⊥) :
    ∀ B : Subgroup (P ⧸ frattini P),
      (∀ t : T, ∀ b ∈ B, quotientAut (frattini P)
        (MulAut.conjNormal (quotientMap M (inclusion hTM t))) b ∈ B) → B = ⊥ ∨ B = ⊤ := by
  let a := (MulAut.conjNormal : CoreQuotient M →* MulAut P).comp
    ((quotientMap M).comp (inclusion hXM))
  let b := (quotientAut (frattini P)).comp a
  let : Fact (IsPGroup p P) := ⟨hs.isPGroup⟩
  let : IsElementaryAbelian p (P ⧸ frattini P) := isElementaryAbelian_quotient_frattini
  have hp2 : p ≠ 2 := by rcases hp with rfl | rfl <;> decide
  have hb := twoCore_frattini_image_ne_bot hp2 hs.isPGroup a hne
  intro B hB
  apply core_irreducible_on_plane hp (shape_frattini_card hs) hX.1.2.1 hX3 b hb B
  intro x hx v hv
  let t : T := ⟨(x : G), member_core_le_sylow T X Z hX ⟨x, hx, rfl⟩⟩
  exact hB t v hv

/-- The actual normal prime-five source subgroup yields a positive lift
from nontrivial original two-core action, with all action witnesses derived. -/
theorem five_positive_of_core_action
    (T : Sylow 2 G) (M X Z : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hXM : X ≤ M) (hM : HasCharacteristicTwo M)
    (hX : X ∈ NormalCentralizerXi (T : Subgroup G) Z)
    (hX3 : Nat.card (X ⧸ pCore 2 X) = 3)
    (P : Subgroup (CoreQuotient M)) [P.Normal] (hs : Chapter1.XiOddQuotient 5 P)
    (hne : (pCore 2 X).map ((MulAut.conjNormal : CoreQuotient M →* MulAut P).comp
      ((quotientMap M).comp (inclusion hXM))) ≠ ⊥) :
    lift M P ∈ Chapter3.XiPlus G (T : Subgroup G) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let a := (MulAut.conjNormal : CoreQuotient M →* MulAut P).comp
    ((quotientMap M).comp (inclusion hXM))
  let b := (quotientAut (frattini P)).comp a
  have hb : (pCore 2 X).map b ≠ ⊥ := twoCore_frattini_image_ne_bot (by decide) hs.isPGroup a hne
  have hk : b.ker ≠ ⊤ := fun h => hb ((Subgroup.map_eq_bot_iff _).mpr (h ▸ le_top))
  obtain ⟨x, _, hx, _⟩ := exists_cubic_actor hX.1.2.1 hX3 a hk
  exact five_lift_positive T M X hTM hXM hM hX3 P (shape_perfect (by decide) hs) hs
    (sylow_frattini_irreducible (Or.inr rfl) T M X Z hTM hXM hX hX3 P hs hne)
    (inclusion hXM x) hx

/-- The universal source Ξ-plus exclusion kills the original two-core action
on every normal prime-five subgroup of the source noncyclic shapes. -/
theorem five_core_action_trivial_of_source_exclusion
    (T : Sylow 2 G) (M X Z : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hXM : X ≤ M) (hM : HasCharacteristicTwo M)
    (hX : X ∈ NormalCentralizerXi (T : Subgroup G) Z)
    (hX3 : Nat.card (X ⧸ pCore 2 X) = 3)
    (hex : ∀ Y ∈ Chapter1.Xi G (T : Subgroup G), Y ∉ Chapter3.XiPlus G (T : Subgroup G))
    (P : Subgroup (CoreQuotient M)) [P.Normal] (hs : Chapter1.XiOddQuotient 5 P) :
    (pCore 2 X).map ((MulAut.conjNormal : CoreQuotient M →* MulAut P).comp
      ((quotientMap M).comp (inclusion hXM))) = ⊥ := by
  by_contra hne
  have hpos := five_positive_of_core_action T M X Z hTM hXM hM hX hX3 P hs hne
  exact hex (lift M P) hpos.1 hpos

/-- The ternary noncyclic source shape gives order 24 on the original P. -/
theorem ternary_action_card
    (M X : Subgroup G) (hXM : X ≤ M) (hX : IsPPerfect 2 X)
    (hX3 : Nat.card (X ⧸ pCore 2 X) = 3)
    (P : Subgroup (CoreQuotient M)) [P.Normal] (hs : Chapter1.XiOddQuotient 3 P)
    (hne : (pCore 2 X).map ((MulAut.conjNormal : CoreQuotient M →* MulAut P).comp
      ((quotientMap M).comp (inclusion hXM))) ≠ ⊥) :
    Nat.card (((MulAut.conjNormal : CoreQuotient M →* MulAut P).comp
      ((quotientMap M).comp (inclusion hXM))).range) = 24 := by
  let : Fact (IsPGroup 3 P) := ⟨hs.isPGroup⟩
  let : IsElementaryAbelian 3 (P ⧸ frattini P) := isElementaryAbelian_quotient_frattini
  obtain ⟨_, e, _⟩ := exists_plane_coordinates (shape_frattini_card hs)
  exact ternary_original_action_card hs.isPGroup hX hX3 _ e hne

end CFSG.Quasithin.Chapter15.Section04.CentralizerWitness.SupercriticalNineSource
