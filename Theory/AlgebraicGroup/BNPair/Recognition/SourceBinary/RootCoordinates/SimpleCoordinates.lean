module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.OppositeBorel

/-!
# The two actual simple root groups and their unique coordinates

For each original simple class sᵢ, set Xᵢ = U ∩ U^(w₀sᵢ) and
Vᵢ = U ∩ U^sᵢ. Increasing Bruhat multiplication factors B into its two
corresponding Borel intersections. Removing the common odd torus gives
U = Vᵢ Xᵢ = Xᵢ Vᵢ; the opposite-Borel theorem makes these factors disjoint.
Multiplication is a bijection of types, without any commutation assertion.
The normalizer axiom excludes a trivial Xᵢ. Counting the unique coordinates
then gives the literal index [Pᵢ:B] = 1 + |Xᵢ| and transports this to the
original endpoint and full original overlap through the same quotient map.

Source: Carter Propositions 2.5.6, 2.5.9 and 2.5.11 in
`refs/KGroup/GLS3/Chapter2Ca2.tex`, with finite Sylow/odd-order separation
in place of algebraic unipotence. Right conjugation is used throughout.
Neither perfectness nor a prescribed value of the dihedral parameter is
required, and the original ambient carrier may be infinite.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
variable {X : Type*} [Group X] {T : TitsSystem (X := X)}

private theorem ascent_conjugate_mem_borel
    {s w : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N} (hs : s ∈ T.S)
    (hlen : T.wordLength w ≤ T.wordLength (s*w))
    (ns nw : T.N)
    (hns : QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N) ns = s)
    (hnw : QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N) nw = w)
    {x : X} (hx : x ∈ rightConjugate T.B (ns : X))
    (hcell : x * (nw : X) ∈ T.bruhatCell w) : x ∈ T.B := by
  have hnsP : (ns : X) ∈ T.standardParabolic {s} :=
    T.bruhatCell_subset_standardParabolic_of_mem (Set.mem_singleton s)
      (T.representative_mem_bruhatCell s ns hns)
  have hxP : x ∈ T.standardParabolic {s} := by
    have h := (T.standardParabolic {s}).mul_mem
      ((T.standardParabolic {s}).mul_mem ((T.standardParabolic {s}).inv_mem hnsP)
        (T.B_le_standardParabolic {s} hx)) hnsP
    change (ns : X)⁻¹ * ((ns : X) * x * (ns : X)⁻¹) * (ns : X) ∈
      T.standardParabolic {s} at h
    simpa only [inv_mul_cancel_left, mul_assoc, inv_mul_cancel, mul_one] using h
  have hxcell : x ∈ (T.B : Set X) ∪ T.bruhatCell s :=
    singleton_parabolic_cells hs ▸ hxP
  rcases hxcell with hxB | hxS
  · exact hxB
  · have hprod : x * (nw : X) ∈ T.bruhatCell (s*w) :=
      T.bruhatCell_mul_bruhatCell_subset_of_wordLength_le hs w hlen
        ⟨x, hxS, nw, T.representative_mem_bruhatCell w nw hnw, rfl⟩
    have he := T.doubleCoset_index_unique hprod hcell
    exact False.elim ((T.involutions s hs).1 (mul_right_cancel (he.trans (one_mul w).symm)))

/-- Carter 2.5.6's Borel product argument at any right ascent. -/
theorem ascent_borel_factorization
    {s w : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N} (hs : s ∈ T.S)
    (hlen : T.wordLength w⁻¹ ≤ T.wordLength (s*w⁻¹))
    (ns nw : T.N)
    (hns : QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N) ns = s)
    (hnw : QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N) nw = w) :
    (T.B : Set X) =
      ((T.B ⊓ rightConjugate T.B (ns : X) : Subgroup X) : Set X) *
        ((T.B ⊓ rightConjugate T.B (nw : X) : Subgroup X) : Set X) := by
  apply Set.Subset.antisymm
  · intro b hb
    have hni : QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N) nw⁻¹ = w⁻¹ := by
      rw [map_inv, hnw]
    have hprod : (ns : X) * b * (nw : X)⁻¹ ∈ T.bruhatCell (s*w⁻¹) := by
      apply T.bruhatCell_mul_bruhatCell_subset_of_wordLength_le hs w⁻¹ hlen
      refine ⟨(ns : X)*b, ?_, (nw : X)⁻¹, T.representative_mem_bruhatCell _ nw⁻¹ hni, rfl⟩
      simpa only [bruhatCell, one_mul] using mul_mem_doubleCoset T.B T.N s T.B.one_mem hb
        (T.representative_mem_bruhatCell s ns hns)
    rw [bruhatCell, B_mul_representativeSet_mul_B T.B T.N (s*w⁻¹) (ns*nw⁻¹)
      (by rw [map_mul, hns, hni])] at hprod
    obtain ⟨a, ha, c, hc, he⟩ := DoubleCoset.mem_doubleCoset.mp hprod
    change (ns : X) * b * (nw : X)⁻¹ = a * ((ns : X) * (nw : X)⁻¹) * c at he
    let x := (ns : X)⁻¹ * a * (ns : X)
    let y := (nw : X)⁻¹ * c * (nw : X)
    have hxy : b = x*y := by
      have h := congrArg (fun z : X => (ns : X)⁻¹ * z * (nw : X)) he
      simpa only [x, y, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using h
    have hx : x ∈ rightConjugate T.B (ns : X) := by
      change (ns : X) * ((ns : X)⁻¹ * a * (ns : X)) * (ns : X)⁻¹ ∈ T.B
      simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using (show a ∈ T.B from ha)
    have hxB : x ∈ T.B := by
      apply ascent_conjugate_mem_borel hs hlen ns nw⁻¹ hns hni hx
      have h := mul_mem_doubleCoset T.B T.N w⁻¹ hb (T.B.inv_mem hc)
        (T.representative_mem_bruhatCell w⁻¹ nw⁻¹ hni)
      have hident : x * (nw : X)⁻¹ = b * (nw : X)⁻¹ * c⁻¹ := by
        rw [hxy]
        simp only [y, mul_assoc, mul_inv_cancel, mul_one]
      change x * (nw : X)⁻¹ ∈ T.bruhatCell w⁻¹
      rw [hident]
      exact h
    have hyB : y ∈ T.B := by
      have h := T.B.mul_mem (T.B.inv_mem hxB) hb
      rwa [hxy, inv_mul_cancel_left] at h
    have hy : y ∈ rightConjugate T.B (nw : X) := by
      change (nw : X) * ((nw : X)⁻¹ * c * (nw : X)) * (nw : X)⁻¹ ∈ T.B
      simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using (show c ∈ T.B from hc)
    exact ⟨x, ⟨hxB, hx⟩, y, ⟨hyB, hy⟩, hxy.symm⟩
  · rintro b ⟨x, hx, y, hy, rfl⟩
    exact T.B.mul_mem hx.1 hy.1

variable {P : Fin 2 → Subgroup X} (d : MarkedQuotient P) (split : SplitData d.tits)

/-- The actual simple root intersection, with the constructed longest class. -/
@[expose] def simpleRoot (i : Fin 2) : Subgroup (X ⧸ d.D) :=
  rootIntersection split (longest d) (d.simple i)

/-- The complementary subgroup in the original U. -/
@[expose] def simpleRemainder (i : Fin 2) : Subgroup (X ⧸ d.D) :=
  split.U ⊓ unipotentConjugate split (d.simple i)

theorem simpleRoot_le (i : Fin 2) : simpleRoot d split i ≤ split.U := inf_le_left

theorem torus_normalizes_simpleRoot (i : Fin 2) :
    d.tits.B ⊓ d.tits.N ≤ normalizer (simpleRoot d split i : Set (X ⧸ d.D)) :=
  torus_normalizes_rootIntersection split (longest d) (d.simple i)

/-- The two Borel intersections factor the entire B, including its odd torus. -/
theorem simple_borel_factorization (i : Fin 2) :
    (d.tits.B : Set (X ⧸ d.D)) =
      ((d.tits.B ⊓ borelConjugate (d.simple i) : Subgroup (X ⧸ d.D)) : Set (X ⧸ d.D)) *
        ((d.tits.B ⊓ borelConjugate (longest d*d.simple i) : Subgroup (X ⧸ d.D)) : Set (X ⧸ d.D)) := by
  let ns := representative (d.simple i)
  let nw := representative (longest d*d.simple i)
  have hs : d.simple i * d.simple i = 1 := by
    simpa only [pow_two] using (d.tits.involutions _ (d.simple_mem i)).2
  have hlen : d.tits.wordLength (longest d*d.simple i)⁻¹ ≤
      d.tits.wordLength (d.simple i*(longest d*d.simple i)⁻¹) := by
    have hsi : (d.simple i)⁻¹ = d.simple i := inv_eq_of_mul_eq_one_right hs
    rw [wordLength_inv, wordLength_longest_mul_simple, mul_inv_rev, longest_inv, hsi,
      ← mul_assoc, hs, one_mul, wordLength_longest]
    exact Nat.sub_le _ _
  exact ascent_borel_factorization (d.simple_mem i) hlen ns nw
    (representative_spec _) (representative_spec _)

/-- The simple root and its complementary intersection are disjoint. -/
theorem simpleRoot_disjoint_remainder (i : Fin 2) :
    Disjoint (simpleRoot d split i) (simpleRemainder d split i) := by
  apply disjoint_iff.mpr
  apply eq_bot_iff.mpr
  intro x hx
  let n₀ := representative (longest d)
  let ns := representative (d.simple i)
  have hxR := hx.1.2
  rw [unipotentConjugate_eq split _ (n₀*ns)
    (by rw [map_mul, representative_spec, representative_spec])] at hxR
  have hxV := hx.2.2
  change (ns : X ⧸ d.D) * x * (ns : X ⧸ d.D)⁻¹ ∈ split.U at hxV
  have hzero : (ns : X ⧸ d.D) * x * (ns : X ⧸ d.D)⁻¹ ∈
      d.tits.B ⊓ unipotentConjugate split (longest d) := by
    refine ⟨split.U_le hxV, ?_⟩
    change (n₀ : X ⧸ d.D) * ((ns : X ⧸ d.D) * x * (ns : X ⧸ d.D)⁻¹) *
      (n₀ : X ⧸ d.D)⁻¹ ∈ split.U
    change ((n₀ : X ⧸ d.D) * (ns : X ⧸ d.D)) * x *
      ((n₀ : X ⧸ d.D) * (ns : X ⧸ d.D))⁻¹ ∈ split.U at hxR
    simpa only [mul_inv_rev, mul_assoc] using hxR
  rw [borel_inf_opposite_unipotent d split, mem_bot] at hzero
  apply (MulAut.conj (ns : X ⧸ d.D)).injective
  simpa only [MulAut.conj_apply, map_one] using hzero

/-- The ordered simple-root factorization is a set product; commutation is not asserted. -/
theorem remainder_mul_simpleRoot (i : Fin 2) :
    (simpleRemainder d split i : Set (X ⧸ d.D)) * (simpleRoot d split i : Set (X ⧸ d.D)) = split.U := by
  apply Set.Subset.antisymm
  · rintro x ⟨v, hv, r, hr, rfl⟩
    exact split.U.mul_mem hv.1 hr.1
  · intro u hu
    have hB : u ∈ d.tits.B := split.U_le hu
    rw [show u ∈ d.tits.B ↔ u ∈ (d.tits.B : Set (X ⧸ d.D)) from Iff.rfl,
      simple_borel_factorization d i] at hB
    obtain ⟨a, ha, b, hb, he⟩ := hB
    have hA := (borel_intersection_factorization split (representative (d.simple i))) ▸ ha
    have hB' := (borel_intersection_factorization split (representative (longest d*d.simple i))) ▸ hb
    obtain ⟨v, hv, h, hh, hav⟩ := hA
    obtain ⟨r, hr, k, hk, hbr⟩ := hB'
    have hr' : h*r*h⁻¹ ∈ simpleRoot d split i :=
      (mem_normalizer_iff.mp (torus_normalizes_simpleRoot d split i hh) r).mp hr
    have hvr : v*(h*r*h⁻¹) ∈ split.U := split.U.mul_mem hv.1 hr'.1
    have he' : v*(h*r*h⁻¹)*(h*k) = u := by
      rw [← he, ← hav, ← hbr]
      simp only [mul_assoc, inv_mul_cancel_left]
    have hhU : h*k ∈ split.U := by
      have hmem := split.U.mul_mem (split.U.inv_mem hvr) hu
      rwa [← he', inv_mul_cancel_left] at hmem
    have hhk : h*k = 1 := (mem_bot.mp ((disjoint_iff.mp (unipotent_disjoint_torus split)) ▸
      (show h*k ∈ split.U ⊓ (d.tits.B ⊓ d.tits.N) from ⟨hhU, mul_mem hh hk⟩)))
    exact ⟨v, hv, h*r*h⁻¹, hr', by simpa only [hhk, mul_one] using he'⟩

/-- Reversing the factors follows by inversion, without a commutation claim. -/
theorem simpleRoot_mul_remainder (i : Fin 2) :
    (simpleRoot d split i : Set (X ⧸ d.D)) * (simpleRemainder d split i : Set (X ⧸ d.D)) = split.U := by
  apply Set.Subset.antisymm
  · rintro x ⟨r, hr, v, hv, rfl⟩
    exact split.U.mul_mem hr.1 hv.1
  · intro x hx
    have hxi : x⁻¹ ∈ (simpleRemainder d split i : Set (X ⧸ d.D)) *
        (simpleRoot d split i : Set (X ⧸ d.D)) := by
      rw [remainder_mul_simpleRoot]
      exact split.U.inv_mem hx
    obtain ⟨v, hv, r, hr, he⟩ := hxi
    refine ⟨r⁻¹, inv_mem hr, v⁻¹, inv_mem hv, ?_⟩
    simpa only [mul_inv_rev, inv_inv] using congrArg Inv.inv he

private def simpleMul (i : Fin 2) : simpleRoot d split i × simpleRemainder d split i → split.U :=
  fun p => ⟨(p.1 : X ⧸ d.D) * p.2, split.U.mul_mem p.1.property.1 p.2.property.1⟩

private theorem simpleMul_bijective (i : Fin 2) : Function.Bijective (simpleMul d split i) := by
  constructor
  · intro p q hpq
    exact mul_injective_of_disjoint (simpleRoot_disjoint_remainder d split i)
      (congrArg Subtype.val hpq)
  · intro x
    have hx : (x : X ⧸ d.D) ∈ (simpleRoot d split i : Set (X ⧸ d.D)) *
        (simpleRemainder d split i : Set (X ⧸ d.D)) :=
      (simpleRoot_mul_remainder d split i).symm ▸ x.property
    obtain ⟨r, hr, v, hv, he⟩ := hx
    exact ⟨(⟨r, hr⟩, ⟨v, hv⟩), Subtype.ext he⟩

/-- Unique root and remainder multiplication coordinates as types. -/
def simpleCoordinates (i : Fin 2) : simpleRoot d split i × simpleRemainder d split i ≃ split.U :=
  Equiv.ofBijective (simpleMul d split i) (simpleMul_bijective d split i)

@[simp] theorem simpleCoordinates_apply (i : Fin 2)
    (r : simpleRoot d split i) (v : simpleRemainder d split i) :
    (simpleCoordinates d split i (r,v) : X ⧸ d.D) = (r : X ⧸ d.D) * v := by rfl

theorem unipotent_card_simple (i : Fin 2) :
    Nat.card split.U = Nat.card (simpleRoot d split i) * Nat.card (simpleRemainder d split i) := by
  rw [← Nat.card_congr (simpleCoordinates d split i), Nat.card_prod]

theorem simpleRemainder_index (i : Fin 2) :
    ((simpleRemainder d split i).subgroupOf split.U).index = Nat.card (simpleRoot d split i) := by
  have hV : Nat.card (simpleRemainder d split i) *
      ((simpleRemainder d split i).subgroupOf split.U).index = Nat.card split.U := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe
      (show simpleRemainder d split i ≤ split.U from inf_le_left)).toEquiv]
    exact ((simpleRemainder d split i).subgroupOf split.U).card_mul_index
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := simpleRemainder d split i))
  rw [hV, unipotent_card_simple, Nat.mul_comm]

/-- The literal standard-parabolic index is one plus this simple root order. -/
theorem singleton_parabolic_root_index (i : Fin 2) :
    (d.tits.B.subgroupOf (d.tits.standardParabolic {d.simple i})).index =
      1 + Nat.card (simpleRoot d split i) := by
  rw [singleton_parabolic_index split (d.simple_mem i) (representative (d.simple i))
    (representative_spec _)]
  exact congrArg (1 + ·) (simpleRemainder_index d split i)

/-- Transport to the original endpoint and its entire original overlap. -/
theorem original_endpoint_root_index (i : Fin 2) :
    ((P 0 ⊓ P 1).subgroupOf (P i)).index = 1 + Nat.card (simpleRoot d split i) := by
  rw [original_endpoint_index d, singleton_parabolic_root_index]

theorem simpleRoot_ne_bot (i : Fin 2) : simpleRoot d split i ≠ ⊥ := by
  intro hz
  have hV : simpleRemainder d split i = split.U := by
    apply SetLike.coe_injective
    have h := remainder_mul_simpleRoot d split i
    simpa [hz] using h
  let ns := representative (d.simple i)
  have hle : split.U ≤ rightConjugate split.U (ns : X ⧸ d.D) := by
    calc
      split.U = simpleRemainder d split i := hV.symm
      _ ≤ rightConjugate split.U (ns : X ⧸ d.D) := inf_le_right
  have hcard : Nat.card (rightConjugate split.U (ns : X ⧸ d.D)) = Nat.card split.U := by
    rw [rightConjugate, comap_equiv_eq_map_symm']
    exact card_map_of_injective (MulAut.conj (ns : X ⧸ d.D)).symm.injective
  have heq := eq_of_le_of_card_ge hle (le_of_eq hcard)
  have hn : (ns : X ⧸ d.D) ∈ normalizer (split.U : Set (X ⧸ d.D)) := by
    rw [mem_normalizer_iff]
    intro x
    change x ∈ split.U ↔ x ∈ rightConjugate split.U (ns : X ⧸ d.D)
    rw [← heq]
  rw [split.normalizer_eq] at hn
  have hq : QuotientGroup.mk' ((d.tits.B ⊓ d.tits.N).subgroupOf d.tits.N) ns = 1 :=
    (QuotientGroup.eq_one_iff ns).mpr ⟨hn, ns.property⟩
  rw [representative_spec] at hq
  exact (d.tits.involutions _ (d.simple_mem i)).1 hq

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
