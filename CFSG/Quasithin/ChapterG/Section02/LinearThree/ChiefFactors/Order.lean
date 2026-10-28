module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.Coordinates
public import Theory.GroupTheory.NormalizedSupCard
import Mathlib.Tactic.Ring

/-!
# The order formula in G.2.5(8)

The two marked lower images have order 2^(ns). Their preimages meet in S₂,
so their product has order |S₂|2^(2ns). This product is exactly W∩S₃.
The marked upper image contributes 2^(nr), and the original starred
unipotent radical contributes 2^(2n). Finally |V|=2^(3n).

The hypotheses retain the actual earlier coordinate identifications and
the comparison of the intrinsic core with the original star kernel. No
numerical factor in the conclusion is assumed. The chief-factor assertion
of (8) is a separate obligation, not asserted by this order calculation.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
G.2.5(1–8), printed pp.335–336, PDF pp.346–347.
-/

@[expose] public section
open Subgroup

namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors
open Setup
variable {G : Type*} [Group G] {D : Setup G} {g h : G}

/-- The lower image is measured with its literal quotient map. -/
theorem card_lowerImage [((S₂ D g h).subgroupOf (S₃ D g h)).Normal]
    (A : Subgroup G) (hA : A ≤ S₃ D g h) :
    Nat.card (lowerImage D g h A) = (S₂ D g h).relIndex A := by
  change Nat.card ((A.subgroupOf (S₃ D g h)).map
    (QuotientGroup.mk' ((S₂ D g h).subgroupOf (S₃ D g h)))) = _
  rw [← relIndex_ker, QuotientGroup.ker_mk']
  exact relIndex_subgroupOf hA

/-- The star image uses the original core of LT, embedded in G. -/
theorem card_star_U (hULT : D.U ≤ D.LT) :
    Nat.card (D.star D.U) = (D.LT.pCoreIn 2).relIndex D.U := by
  unfold Setup.star
  rw [← relIndex_ker, QuotientGroup.ker_mk']
  have hi := relIndex_map_map_of_injective (pCore 2 D.LT) (D.U.subgroupOf D.LT)
    D.LT.subtype_injective
  rw [map_subgroupOf_eq_of_le hULT] at hi
  exact hi.symm

private theorem card_eq_mul_relIndex {A B : Subgroup G} (hAB : A ≤ B) :
    Nat.card B = Nat.card A * A.relIndex B := by
  simpa only [relIndex_bot_left] using
    (relIndex_mul_relIndex (⊥ : Subgroup G) A B bot_le hAB).symm

variable [Finite G] {F : Type*} [Field F] [Finite F] {n : ℕ}
  (d : Hypothesis D F n g h)

include d

/-- The two pair subgroups inside W meet in the actual triple intersection. -/
theorem pair_inf (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) (hLI : D.L ≤ I D g h) :
    (W D g h ⊓ conjugate (W D g h) g) ⊓
      (W D g h ⊓ conjugate (W D g h) h) = S₂ D g h := by
  rw [d.S₂_eq_triple_W hUT hf hLI]
  ext x
  constructor
  · rintro ⟨⟨hx, hg⟩, _, hh⟩
    exact ⟨⟨hx, hg⟩, hh⟩
  · rintro ⟨⟨hx, hg⟩, hh⟩
    exact ⟨⟨hx, hg⟩, hx, hh⟩

/-- The product count needs only relative normalization inside U. -/
theorem pair_normalizes (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) (hLI : D.L ≤ I D g h) :
    W D g h ⊓ conjugate (W D g h) h ≤
      normalizer ((W D g h ⊓ conjugate (W D g h) g : Subgroup G) : Set G) := by
  apply le_normalizer_iff_commutator_le_right.mpr
  have hder : ⁅D.U, D.U⁆ ≤ D.V :=
    (derived_le_of_frattini_image_le (d.U_isPGroup hUT) hf).trans d.setup.point_le
  have hVA : D.V ≤ W D g h ⊓ conjugate (W D g h) g := by
    have he := (d.intersection hUT hf).1
    rw [d.S₂_eq_triple_W hUT hf hLI] at he
    exact he.trans inf_le_left
  exact (commutator_mono (inf_le_left.trans inf_le_left)
    (inf_le_left.trans inf_le_left)).trans (hder.trans hVA)

variable [((S₂ D g h).subgroupOf (S₃ D g h)).Normal]
  [((S₃ D g h).subgroupOf (S D g h)).Normal]
  {r s : ℕ} {hLI : D.L ≤ I D g h}

/-- The lower marked summands determine the order of the actual upper kernel. -/
theorem card_W_inf_S₃ (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (c : MarkedLayers d hLI r s) :
    Nat.card (W D g h ⊓ S₃ D g h : Subgroup G) =
      Nat.card (S₂ D g h) * 2 ^ (2 * (n * s)) := by
  let A := W D g h ⊓ conjugate (W D g h) g
  let B := W D g h ⊓ conjugate (W D g h) h
  have hEA : S₂ D g h ≤ A := by
    rw [d.S₂_eq_triple_W hUT hf hLI]
    exact inf_le_left
  have hEB : S₂ D g h ≤ B := by
    rw [d.S₂_eq_triple_W hUT hf hLI]
    exact le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hA : Nat.card A = Nat.card (S₂ D g h) * 2 ^ (n * s) := by
    rw [card_eq_mul_relIndex hEA, ← card_lowerImage A (le_sup_left.trans le_sup_left)]
    exact congrArg (Nat.card (S₂ D g h) * ·) c.card_lowerImage_g
  have hB : Nat.card B = Nat.card (S₂ D g h) * 2 ^ (n * s) := by
    rw [card_eq_mul_relIndex hEB, ← card_lowerImage B (le_sup_right.trans le_sup_left)]
    exact congrArg (Nat.card (S₂ D g h) * ·) c.card_lowerImage_h
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes A B
    (pair_normalizes d hUT hf hLI)
  have hi : A ⊓ B = S₂ D g h := pair_inf d hUT hf hLI
  have hj : W D g h ⊓ S₃ D g h = A ⊔ B := d.W_inf_S₃ hUT hf hLI
  rw [hA, hB, hi, ← hj] at hprod
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := S₂ D g h))
  calc
    _ = (Nat.card (S₂ D g h) * 2 ^ (n * s)) *
        (Nat.card (S₂ D g h) * 2 ^ (n * s)) := hprod.symm
    _ = _ := by rw [two_mul, pow_add]; ac_rfl

/-- W is counted through its actual upper image and its actual kernel. -/
theorem card_W (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (c : MarkedLayers d hLI r s) :
    Nat.card (W D g h) = Nat.card (S₂ D g h) * 2 ^ (n * (2 * s + r)) := by
  rw [card_eq_mul_relIndex (show W D g h ⊓ S₃ D g h ≤ W D g h from inf_le_left),
    inf_relIndex_left, ← card_upperImage_W, c.card_upperImage,
    card_W_inf_S₃ d hUT hf c, mul_assoc, ← pow_add]
  congr 2
  ring

/-- G.2.5's order formula from the marked natural/dual layers and the actual
unipotent radical coordinates. `hcore` is the earlier comparison of the
intrinsic core with the original star kernel. -/
theorem order_formula (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (hcore : S D g h = I D g h ⊓ D.LT.pCoreIn 2)
    (radical : D.star D.U ≃* Multiplicative (Fin 2 → F))
    (c : MarkedLayers d hLI r s) :
    Nat.card D.U = 2 ^ (n * (2 * s + r + 5)) * D.V.relIndex (S₂ D g h) := by
  have hUW : D.U ⊓ D.LT.pCoreIn 2 = W D g h := by
    unfold W
    rw [hcore]
    apply le_antisymm
    · intro x hx
      exact ⟨hx.1, (show D.U ≤ I D g h from le_sup_left.trans le_sup_left) hx.1, hx.2⟩
    · exact fun _ hx => ⟨hx.1, hx.2.2⟩
  have hU : Nat.card D.U = Nat.card (W D g h) * Nat.card (D.star D.U) := by
    rw [card_eq_mul_relIndex (show W D g h ≤ D.U from inf_le_left),
      card_star_U (hUT.trans le_sup_right)]
    congr 1
    rw [← hUW, inf_relIndex_left]
  have hr : Nat.card (D.star D.U) = 2 ^ (n * 2) := by
    rw [Nat.card_congr radical.toEquiv]
    change Nat.card (Fin 2 → F) = _
    rw [Nat.card_fun, Nat.card_fin, d.field_card, ← pow_mul]
  have hV : Nat.card D.V = 2 ^ (n * 3) := by
    rw [Nat.card_congr d.coordinates.toEquiv]
    change Nat.card (Fin 3 → F) = _
    rw [Nat.card_fun, Nat.card_fin, d.field_card, ← pow_mul]
  rw [hU, hr, card_W d hUT hf c,
    card_eq_mul_relIndex (d.intersection hUT hf).1, hV]
  calc
    _ = (2 ^ (n * 3) * 2 ^ (n * (2 * s + r)) * 2 ^ (n * 2)) *
        D.V.relIndex (S₂ D g h) := by ac_rfl
    _ = _ := by
      rw [← pow_add, ← pow_add]
      congr 2
      ring

end CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors
