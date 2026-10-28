module

public import Theory.SpecificGroups.Triality.StandardTwoRank.Perfectness
public import Theory.SpecificGroups.Triality.ConcreteBruhat.FixedDescent
public import Theory.GroupTheory.PerfectCentralCoverExistence
public import Theory.GroupTheory.FilteredCollection
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.TwoPrimary.Transfer

/-!
# Folded-root collection in central extensions of binary triality

The positive unipotent subgroup of the genuine carrier has unique coordinates
in three copies of GF(q³) and three copies of GF(q). We compare its literal
inclusion with the product of the six published folded roots, retaining the
central quotient in `StandardModel` through the faithful split-matrix map.

Suppose these six root groups have additive sections in a central extension,
and exchanging two distinct lifted factors introduces only factors of strictly
higher root height. The finite filtered collector gives a six-factor normal
form in the extension. Projection and uniqueness of the original matrix
coordinates then make this normal form a homomorphic section of the actual
positive subgroup. Its odd index and central transfer exclude two from the
kernel of any finite perfect central cover, including the canonical one.

`RootSections` and `HigherCommutators` are explicit local proof obligations.
Their existence is not asserted here. They require one common system of lifts;
independently chosen additive lifts need not satisfy the inter-root relations.
All definitions and deductions include q = 2.

Sources: GLS3 §2.4 for the folded roots and their heights, and §6.1,
Theorem 6.1.4 and Tables 6.1.2–3 for the finite multiplier calculation used in
Aschbacher–Smith I.1.3, printed p.407 (PDF p.418).
-/

@[expose] public section

open Triality.Standard
open Triality.Standard.Parabolics Triality.Standard.ConcreteBruhat
open Triality.Standard.PositiveCoordinates
open Triality.Standard.RadicalCoordinates.LeviCommutators

namespace Triality.Standard.CentralCovers.TwoPrimary
noncomputable section
variable (n : ℕ) (hn : 0 < n)
local notation "P" => binaryParameters n hn

/-- The actual three cubic-field and three fixed-field coordinates. -/
abbrev PositiveParameters := OrbitParameters P

/-- The six positive folded roots in the existing matrix normal-form order. -/
def baseProduct (v : PositiveParameters n hn) : BinaryCarrier n hn :=
  short P rfl 0 (v.1 0) * long P rfl 0 (v.2 0) *
    short P rfl 1 (v.1 1) * short P rfl 2 (v.1 2) *
    long P rfl 1 (v.2 1) * long P rfl 2 (v.2 2)

/-- The six parameters identify with the original descended positive subgroup. -/
def positiveEquiv : PositiveParameters n hn ≃ unipotent P :=
  (orbitPositiveEquiv_binary n hn).trans
    ((FixedDescent.carrierFixedEquiv P rfl).toEquiv.subtypeEquiv
      (fun g => FixedDescent.mem_descend_iff P rfl (positiveSubgroup P) g)).symm

private lemma map_six_of_eq {G H : Type*} [Group G] [Group H] (f : G →* H)
    {a b c d e g : G} {a' b' c' d' e' g' : H}
    (ha : f a = a') (hb : f b = b') (hc : f c = c')
    (hd : f d = d') (he : f e = e') (hg : f g = g') :
    f (a * b * c * d * e * g) = a' * b' * c' * d' * e' * g' := by
  simp only [map_mul, ha, hb, hc, hd, he, hg]

/-- The folded product is the original twelve-root matrix product. -/
theorem baseProduct_toSplit (v : PositiveParameters n hn) :
    FixedDescent.carrierToSplit P rfl (baseProduct n hn v) =
      orderedProduct P (expand P v) := by
  have hs (i : Fin 3) (t : ExtensionField P) :
      FixedDescent.carrierToSplit P rfl (short P rfl i t) = shortSplit P i t :=
    (FixedDescent.carrierToSplit_toCarrier P rfl (shortElementary P rfl i t)).trans
      (shortElementary_val P rfl i t)
  have hl (i : Fin 3) (t : fixedField P) :
      FixedDescent.carrierToSplit P rfl (long P rfl i t) = longSplit P i t :=
    (FixedDescent.carrierToSplit_toCarrier P rfl (longElementary P rfl i t)).trans
      (longElementary_val P rfl i t)
  exact (map_six_of_eq (FixedDescent.carrierToSplit P rfl)
    (hs 0 (v.1 0)) (hl 0 (v.2 0)) (hs 1 (v.1 1)) (hs 2 (v.1 2))
    (hl 1 (v.2 1)) (hl 2 (v.2 2))).trans (orderedProduct_expand P v).symm

/-- The coordinate equivalence commutes with the literal subgroup inclusion. -/
theorem positiveEquiv_val (v : PositiveParameters n hn) :
    (positiveEquiv n hn v).val = baseProduct n hn v := by
  apply FixedDescent.carrierToSplit_injective P rfl
  rw [baseProduct_toSplit]
  have h := (FixedDescent.carrierFixedEquiv P rfl).apply_symm_apply
    (orbitPositiveEquiv_binary n hn v).val
  exact congrArg Subtype.val h

/-- Uniqueness persists after the actual central quotient. -/
theorem baseProduct_injective : Function.Injective (baseProduct n hn) := by
  intro v w h
  apply (positiveEquiv n hn).injective
  apply Subtype.ext
  simpa only [positiveEquiv_val] using h

variable {E : Type*} [Group E]

/-- Six additive sections with their prescribed genuine root projections.
No inter-root compatibility is assumed in this structure. -/
structure RootSections (f : E →* BinaryCarrier n hn) where
  shortRoot : Fin 3 → Multiplicative (ExtensionField P) →* E
  longRoot : Fin 3 → Multiplicative (fixedField P) →* E
  project_short : ∀ i t, f (shortRoot i (.ofAdd t)) = short P rfl i t
  project_long : ∀ i t, f (longRoot i (.ofAdd t)) = long P rfl i t

namespace RootSections
variable {n hn} {f : E →* BinaryCarrier n hn}

/-- A common parameter space for the collector; each factor uses only its
own one of the six coordinates. -/
def factor (L : RootSections n hn f) (i : Fin 6) (v : PositiveParameters n hn) : E :=
  ![L.shortRoot 0 (.ofAdd (v.1 0)), L.longRoot 0 (.ofAdd (v.2 0)),
    L.shortRoot 1 (.ofAdd (v.1 1)), L.shortRoot 2 (.ofAdd (v.1 2)),
    L.longRoot 1 (.ofAdd (v.2 1)), L.longRoot 2 (.ofAdd (v.2 2))] i

/-- The ordered product of the six lifted folded roots. -/
def product (L : RootSections n hn f) (v : PositiveParameters n hn) : E :=
  (List.ofFn fun i : Fin 6 => L.factor i v).prod

theorem factor_add (L : RootSections n hn f) (i : Fin 6) (v w : PositiveParameters n hn) :
    L.factor i (v + w) = L.factor i v * L.factor i w := by
  fin_cases i <;> simp [factor, ← map_mul, ← ofAdd_add]

theorem product_zero (L : RootSections n hn f) : L.product 0 = 1 := by
  simp [product, factor, List.ofFn_succ]

/-- Projection preserves the original folded-root marking. -/
theorem project_product (L : RootSections n hn f) (v : PositiveParameters n hn) :
    f (L.product v) = baseProduct n hn v := by
  simp [product, factor, List.ofFn_succ, L.project_short, L.project_long,
    baseProduct, mul_assoc]

end RootSections

/-- D₄ heights of a, b, a+b, 2a+b, 3a+b and 3a+2b. -/
def height : Fin 6 → ℕ := ![1, 1, 2, 3, 4, 5]

namespace RootSections
variable {n hn} {E : Type*} [Group E] {f : E →* BinaryCarrier n hn}

/-- Each exchange has a correction word strictly above both root heights.
These are relations in the extension itself, not just in its image. -/
def HigherCommutators (L : RootSections n hn f) : Prop :=
  ∀ (i j : Fin 6) (a b : PositiveParameters n hn), i ≠ j →
    ∃ correction : List (Fin 6 × PositiveParameters n hn),
      (∀ z ∈ correction, max (height i) (height j) < height z.1) ∧
      L.factor i a * L.factor j b =
        L.factor j b * L.factor i a * FilteredCollection.wordProduct L.factor correction

private def diagonal (a : Fin 6 → PositiveParameters n hn) : PositiveParameters n hn :=
  (![ (a 0).1 0, (a 2).1 1, (a 3).1 2],
    ![ (a 1).2 0, (a 4).2 1, (a 5).2 2])

private lemma diagonal_product (L : RootSections n hn f) (a : Fin 6 → PositiveParameters n hn) :
    ((List.finRange 6).map fun i => L.factor i (a i)).prod = L.product (diagonal a) := by
  rw [← List.ofFn_eq_map]
  simp [product, factor, diagonal, List.ofFn_succ]

/-- Local higher-root corrections suffice to collect every lifted positive word. -/
theorem exists_collected_product (L : RootSections n hn f) (hL : L.HigherCommutators)
    (word : List (Fin 6 × PositiveParameters n hn)) :
    ∃ v : PositiveParameters n hn, FilteredCollection.wordProduct L.factor word = L.product v := by
  obtain ⟨a, ha⟩ := FilteredCollection.filteredCollection_exists_params height L.factor
    (List.finRange 6) (List.nodup_finRange 6) 6
    (by intro i _; fin_cases i <;> decide)
    (fun i a b => (L.factor_add i a b).symm)
    (by
      intro i j a b _ _ hij
      obtain ⟨c, hc, he⟩ := hL i j a b hij
      exact ⟨c, fun z hz => ⟨List.mem_finRange _, hc z hz⟩, he⟩)
    word (fun z _ => List.mem_finRange _)
  exact ⟨diagonal a, ha.trans (L.diagonal_product a)⟩

/-- The collected products are closed under multiplication. -/
theorem product_mul_exists (L : RootSections n hn f) (hL : L.HigherCommutators)
    (a b : PositiveParameters n hn) : ∃ v, L.product a * L.product b = L.product v := by
  obtain ⟨v, hv⟩ := L.exists_collected_product hL
    ((List.ofFn fun i : Fin 6 => (i, a)) ++ (List.ofFn fun i : Fin 6 => (i, b)))
  refine ⟨v, ?_⟩
  simpa only [FilteredCollection.wordProduct, List.map_append, List.prod_append,
    List.map_ofFn, Function.comp_def, product] using hv

/-- Uniqueness of the genuine coordinates makes collection a section of the
literal inclusion of the positive subgroup. -/
theorem exists_unipotent_section (L : RootSections n hn f) (hL : L.HigherCommutators) :
    ∃ s : unipotent (binaryParameters n hn) →* E,
      f.comp s = (unipotent (binaryParameters n hn)).subtype := by
  let e := positiveEquiv n hn
  let j : unipotent (binaryParameters n hn) → E := fun g => L.product (e.symm g)
  have hj (a : unipotent (binaryParameters n hn)) : f (j a) = a.val := by
    rw [show f (j a) = f (L.product (e.symm a)) from rfl, L.project_product,
      ← positiveEquiv_val]
    exact congrArg Subtype.val (e.apply_symm_apply a)
  have hz : e 0 = 1 := by
    apply Subtype.ext
    change (e 0).val = (1 : BinaryCarrier n hn)
    rw [positiveEquiv_val, ← L.project_product, L.product_zero, map_one]
  have hj0 : j 1 = 1 := by
    dsimp [j]
    rw [← hz, e.symm_apply_apply, L.product_zero]
  have hjmul (a b : unipotent (binaryParameters n hn)) : j (a * b) = j a * j b := by
    obtain ⟨v, hv⟩ := L.product_mul_exists hL (e.symm a) (e.symm b)
    have hev : e v = a * b := by
      apply Subtype.ext
      rw [positiveEquiv_val, ← L.project_product, ← hv, map_mul]
      exact congrArg₂ (· * ·) (hj a) (hj b)
    change L.product (e.symm (a * b)) = _
    rw [← hev, e.symm_apply_apply]
    exact hv.symm
  refine ⟨{ toFun := j, map_one' := hj0, map_mul' := hjmul }, ?_⟩
  exact MonoidHom.ext hj

end RootSections

open PerfectCentralCovering

/-- Transfer excludes two from a finite perfect central kernel once the
local folded-root relations have been established. -/
theorem not_two_dvd_kernel_of_higherCommutators {E : Type*} [Group E] [Finite E]
    (c : Cover E (BinaryCarrier n hn)) (L : RootSections n hn c.toMonoidHom)
    (hL : L.HigherCommutators) : ¬ 2 ∣ Nat.card c.toMonoidHom.ker := by
  obtain ⟨s, hs⟩ := L.exists_unipotent_section hL
  exact not_dvd_card_kernel_of_section c (unipotent P)
    (odd_unipotent_index P rfl).not_two_dvd_nat s hs

/-- Application to the canonical free-central-extension projection. Its
finiteness, centrality and perfectness are discharged by existing theorems. -/
theorem universal_not_two_dvd_kernel_of_higherCommutators
    (L : RootSections n hn (universalProjection (BinaryCarrier n hn)))
    (hL : L.HigherCommutators) :
    ¬ 2 ∣ Nat.card (universalProjection (BinaryCarrier n hn)).ker :=
  not_two_dvd_kernel_of_higherCommutators n hn (universalCover (BinaryCarrier n hn)) L hL

end
end Triality.Standard.CentralCovers.TwoPrimary
