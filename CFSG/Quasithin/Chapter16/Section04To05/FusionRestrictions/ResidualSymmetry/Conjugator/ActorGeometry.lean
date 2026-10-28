module

public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Conjugator
public import Theory.GroupTheory.CentralPChiefCore

/-!
# The actual action left by unequal selected residuals

The inputs are the selected Sylow transport from 16.4.2(4), the equality
R = T_C^g from 16.4.11(3), the cross-containments from 16.4.8, and the
exceptional two-perfectness calculation. No common-residual equality is
an input. The existing common-residual theorem constructs it.

Inverse transport makes the two residuals isomorphic, so they have equal
order. Two-perfectness, together with the exceptional three-perfectness,
then turns pointwise fixation into containment and hence equality. Therefore
unequal residuals supply a moved odd-order element and an automorphism of
L of order two. Odd-order generation of a finite two-perfect group supplies
the order restriction. This retains the A4 row, which is not ordinarily perfect.

The model-dependent construction of an odd-rank-three witness from this
moving action is still required. `OddRankThreeWitness` specifies its actual
subgroups and element as output data; no existence theorem is asserted here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.4.2(4), 16.4.8, 16.4.11(3), and 16.5.5–6(3), printed
pp.1183, 1187–1188, 1193–1194, and 1197. Conjugation is left conjugation.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter16

namespace CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Conjugator

variable {G : Type*} [Group G] [Finite G]

/-- Earlier source inputs, before constructing any common residual. -/
structure ResidualInputs (T : Sylow 2 G) (z : G) (L : Subgroup G)
    (g : G) (R : Subgroup G) : Prop where
  setup : IntersectionSetup T z L g R
  selected : (T : Subgroup G) ⊓
      normalizer ((centralizer (L : Set G)).conjBy g : Set G) ≤
    (T : Subgroup G).conjBy g
  transport : R = (commutingSylow T L).conjBy g
  forward_le : ∀ u ∈ R, orderOf u = 2 →
    modifiedCentralizerResidual L u ≤ L.conjBy g
  backward_le : ∀ i ∈ commutingSylow T L, orderOf i = 2 →
    modifiedCentralizerResidual (L.conjBy g) i ≤ L
  forward_twoPerfect : HasEvenLinearThreeType L → ∀ u ∈ R, orderOf u = 2 →
    IsPPerfect 2 (modifiedCentralizerResidual L u)
  backward_twoPerfect : HasEvenLinearThreeType (L.conjBy g) →
    ∀ i ∈ commutingSylow T L, orderOf i = 2 →
      IsPPerfect 2 (modifiedCentralizerResidual (L.conjBy g) i)

variable {T : Sylow 2 G} {z g : G} {L R : Subgroup G}

/-- Construct both families of common-residual identities from the earlier inputs. -/
theorem ResidualInputs.common (d : ResidualInputs T z L g R) :
    (∀ u ∈ R, orderOf u = 2 → modifiedCentralizerResidual L u =
      modifiedCentralizerResidual L (MulAut.conj g z)) ∧
    (∀ i ∈ commutingSylow T L, orderOf i = 2 →
      modifiedCentralizerResidual (L.conjBy g) i =
        modifiedCentralizerResidual L (MulAut.conj g z)) := by
  obtain ⟨X, _, _, hf, hb⟩ := exists_common_residual_conjugate d.setup d.transport
    d.forward_le d.backward_le d.forward_twoPerfect d.backward_twoPerfect
  obtain ⟨hu, hu2⟩ := forward_actor d.setup d.transport
  rw [hf _ hu hu2]
  exact ⟨hf, hb⟩

/-- Inverse conjugation gives the inverse actor residual on the original component. -/
theorem ResidualInputs.inverse_transport (d : ResidualInputs T z L g R) :
    (modifiedCentralizerResidual L (MulAut.conj g z)).conjBy g⁻¹ =
      modifiedCentralizerResidual L (MulAut.conj g⁻¹ z) := by
  have hz : z ∈ commutingSylow T L := by
    refine ⟨d.setup.mem_sylow, ?_⟩
    exact mem_centralizer_iff.mpr fun x hx =>
      mem_centralizer_singleton_iff.mp (d.setup.component.1 hx)
  exact inverse_residual_transport (d.common.2 z hz d.setup.involution)

/-- The two embedded residuals have equal order even before their equality is proved. -/
theorem ResidualInputs.residual_card_eq (d : ResidualInputs T z L g R) :
    Nat.card (modifiedCentralizerResidual L (MulAut.conj g⁻¹ z)) =
      Nat.card (modifiedCentralizerResidual L (MulAut.conj g z)) := by
  rw [← d.inverse_transport]
  exact card_map_of_injective (MulAut.conj g⁻¹).injective

/-- The common residual is two-perfect, including the exceptional modification. -/
theorem ResidualInputs.forward_perfect (d : ResidualInputs T z L g R) :
    IsPPerfect 2 (modifiedCentralizerResidual L (MulAut.conj g z)) := by
  obtain ⟨hu, hu2⟩ := forward_actor d.setup d.transport
  by_cases he : HasEvenLinearThreeType L
  · exact d.forward_twoPerfect he _ hu hu2
  · exact modifiedCentralizerResidual_twoPerfect_of_nonexceptional _ he

/-- Transport supplies two-perfectness for the inverse actor as well. -/
theorem ResidualInputs.inverse_perfect (d : ResidualInputs T z L g R) :
    IsPPerfect 2 (modifiedCentralizerResidual L (MulAut.conj g⁻¹ z)) := by
  rw [← d.inverse_transport]
  let e := (MulAut.conj g⁻¹).subgroupMap
    (modifiedCentralizerResidual L (MulAut.conj g z))
  exact d.forward_perfect.of_surjective e.toMonoidHom e.surjective

/-- Fixation of the forward residual by the inverse actor is the exact missing action fact. -/
theorem ResidualInputs.eq_iff_centralizes (d : ResidualInputs T z L g R) :
    modifiedCentralizerResidual L (MulAut.conj g⁻¹ z) =
        modifiedCentralizerResidual L (MulAut.conj g z) ↔
      modifiedCentralizerResidual L (MulAut.conj g z) ≤
        centralizer ({MulAut.conj g⁻¹ z} : Set G) := by
  constructor
  · intro he
    rw [← he]
    exact (modifiedCentralizerResidual_le _ _).trans
      ((involutionTwoResidual_le _ _).trans inf_le_right)
  · intro hc
    apply Eq.symm
    apply eq_of_le_of_card_ge
    · exact le_modifiedCentralizerResidual
        ((modifiedCentralizerResidual_le _ _).trans
          ((involutionTwoResidual_le _ _).trans inf_le_left)) hc d.forward_perfect
        (fun he => modifiedCentralizerResidual_threePerfect _ he)
    · exact le_of_eq d.residual_card_eq

/-- Two-perfectness forces some odd-order generator of the common residual to
be moved by the inverse actor. This does not assume that the actor normalizes
that residual, and does not yet supply an independent commuting prime-order actor. -/
theorem ResidualInputs.exists_moved_odd_order_element
    (d : ResidualInputs T z L g R)
    (hne : modifiedCentralizerResidual L (MulAut.conj g⁻¹ z) ≠
      modifiedCentralizerResidual L (MulAut.conj g z)) :
    ∃ x ∈ modifiedCentralizerResidual L (MulAut.conj g z), Odd (orderOf x) ∧
      MulAut.conj (MulAut.conj g⁻¹ z) x ≠ x := by
  classical
  by_contra! hfixed
  apply hne
  apply d.eq_iff_centralizes.mpr
  let X := modifiedCentralizerResidual L (MulAut.conj g z)
  let C := (centralizer ({MulAut.conj g⁻¹ z} : Set G)).subgroupOf X
  have hgen := closure_coprime_order_eq_top_of_pResidual_eq_top 2
    ((pResidual_eq_top_iff 2 X).mpr d.forward_perfect)
  have hle : closure {x : X | Nat.Coprime 2 (orderOf x)} ≤ C := by
    apply (closure_le C).mpr
    intro x hx
    change (x : G) ∈ centralizer ({MulAut.conj g⁻¹ z} : Set G)
    have ho : Odd (orderOf (x : G)) := by
      rw [orderOf_coe]
      exact Nat.coprime_two_left.mp hx
    have he := hfixed x x.property ho
    exact mem_centralizer_singleton_iff.mpr
      (mul_inv_eq_iff_eq_mul.mp he).symm
  rw [hgen] at hle
  intro x hx
  exact hle (show (⟨x, hx⟩ : X) ∈ (⊤ : Subgroup X) from mem_top _)


/-- Unequal residuals give an actual element moved by the inverse actor in L. -/
theorem ResidualInputs.exists_moved_element (d : ResidualInputs T z L g R)
    (hne : modifiedCentralizerResidual L (MulAut.conj g⁻¹ z) ≠
      modifiedCentralizerResidual L (MulAut.conj g z)) :
    ∃ x ∈ modifiedCentralizerResidual L (MulAut.conj g z),
      MulAut.conj (MulAut.conj g⁻¹ z) x ≠ x := by
  obtain ⟨x, hx, _, hmove⟩ := d.exists_moved_odd_order_element hne
  exact ⟨x, hx, hmove⟩

/-- The selected transport puts the inverse actor in the normalizer of L. -/
theorem ResidualInputs.inverse_mem_normalizer (d : ResidualInputs T z L g R) :
    MulAut.conj g⁻¹ z ∈ normalizer (L : Set G) :=
  d.setup.sylow_normalizes (inverse_actor_mem_sylow d.setup d.selected d.transport).1

/-- In the unequal case, the actual induced automorphism has order two. -/
theorem ResidualInputs.inverse_action_order (d : ResidualInputs T z L g R)
    (hne : modifiedCentralizerResidual L (MulAut.conj g⁻¹ z) ≠
      modifiedCentralizerResidual L (MulAut.conj g z)) :
    orderOf (L.normalizerMonoidHom ⟨MulAut.conj g⁻¹ z, d.inverse_mem_normalizer⟩) = 2 := by
  let a : normalizer (L : Set G) := ⟨MulAut.conj g⁻¹ z, d.inverse_mem_normalizer⟩
  have ha2 : a ^ 2 = 1 := Subtype.ext
    ((inverse_actor_mem_sylow d.setup d.selected d.transport).2 ▸ pow_orderOf_eq_one a.val)
  have hp : L.normalizerMonoidHom a ^ 2 = 1 := by
    rw [← map_pow, ha2, map_one]
  apply orderOf_eq_prime hp
  intro he
  obtain ⟨x, hx, hmove⟩ := d.exists_moved_element hne
  have hxL : x ∈ L := ((modifiedCentralizerResidual_le _ _).trans
    ((involutionTwoResidual_le _ _).trans inf_le_left)) hx
  have hfix := congrArg (fun b : MulAut L => (b ⟨x, hxL⟩ : G)) he
  exact hmove hfix

/-- The selected conjugator normalizes the residual exactly when the inverse
actor fixes it pointwise. -/
theorem ResidualInputs.normalizes_iff_fixes (d : ResidualInputs T z L g R) :
    g ∈ normalizer (modifiedCentralizerResidual L (MulAut.conj g z) : Set G) ↔
      modifiedCentralizerResidual L (MulAut.conj g z) ≤
        centralizer ({MulAut.conj g⁻¹ z} : Set G) :=
  (normalizes_iff_inverse_actor_residual d.setup d.transport d.common.1 d.common.2).trans
    d.eq_iff_centralizes

/-- The trivial-residual branch needs no rank witness or model comparison. -/
theorem ResidualInputs.normalizes_of_trivial (d : ResidualInputs T z L g R)
    (hbot : modifiedCentralizerResidual L (MulAut.conj g z) = ⊥) :
    g ∈ normalizer (modifiedCentralizerResidual L (MulAut.conj g z) : Set G) := by
  apply d.normalizes_iff_fixes.mpr
  rw [hbot]
  exact bot_le

/-- This is output data, never a standing source hypothesis. -/
structure OddRankThreeWitness (G : Type*) [Group G] where
  p : ℕ
  prime : p.Prime
  odd : Odd p
  Q : Subgroup G
  Q_ne : Q ≠ ⊥
  Q_two : IsPGroup 2 Q
  E : Subgroup G
  E_normalizes : E ≤ normalizer (Q : Set G)
  E_elementary : IsElementaryAbelian p E
  E_card : Nat.card E = p ^ 2
  x : G
  x_normalizes : x ∈ normalizer (Q : Set G)
  x_order : orderOf x = p
  x_independent : x ∉ E
  x_centralizes : E ≤ centralizer ({x} : Set G)
end CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Conjugator
