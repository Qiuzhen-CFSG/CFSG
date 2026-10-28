module

public import CFSG.Quasithin.Chapter16.Section04To05.RankTwo.LongRoot.Construction.Normalizer

/-!
# Constructing the O'Nan input on the actual parabolic image

The displacement span of the literal normalizer representation is the binary
subspace of the group commutator. Fixed spaces use the existing centralizer
comparison. Tight embedding gives TI, and the intrinsic definition of the
root normalizer makes its image normal in the fixed-space stabilizer.

These deductions take the cyclic scalar action from the model calculation;
they do not assume Goldschmidt--O'Nan Input or its stabilizer-normality clause.
Source: Aschbacher--Smith, combined manuscript (1 March 2004), proof of
Lemma 16.5.13, printed pp.1201--1202; GLS96 C.14.1.
-/

@[expose] public section

open Subgroup
open Representation Representation.BinaryOffender Representation.RegularCyclicNormalClosure
open Representation.GoldschmidtONan
open CFSG.Quasithin.Chapter16.Intersections.RankTwo.LongRoot
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter16.Intersections.RankTwo.LongRoot.Construction
variable {G : Type*} [Group G]

@[simp] theorem linearSpace_bot (V : Subgroup G) [IsElementaryAbelian 2 V] :
    linearSpace V ⊥ = ⊥ := by
  ext v
  change (v.toMul : G) = 1 ↔ v = 0
  exact ⟨fun h => congrArg Additive.ofMul (Subtype.ext h), fun h => by simp [h]⟩

theorem linearSpace_disjoint {V C D : Subgroup G} [IsElementaryAbelian 2 V]
    (hd : Disjoint C D) : Disjoint (linearSpace V C) (linearSpace V D) := by
  apply disjoint_iff.mpr
  apply le_antisymm _ bot_le
  intro v hv
  exact congrArg Additive.ofMul (Subtype.ext (disjoint_def.mp hd hv.1 hv.2))

/-- Every linear displacement is a group commutator. -/
theorem displacementSpan_le_commutator {V X P : Subgroup G} [IsElementaryAbelian 2 V] :
    displacementSpan (representation V X) (inducedActor V X P) ⊤ ≤
      linearSpace V ⁅V, P⁆ := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a, ⟨p, hp, rfl⟩, v, _, rfl⟩
  change ((p : G) * (v.toMul : G) * (p : G)⁻¹) / (v.toMul : G) ∈ ⁅V, P⁆
  rw [div_eq_mul_inv, commutator_comm V P]
  exact commutator_mem_commutator hp v.toMul.property

/-- Conversely, all group commutators lie in the linear displacement span. -/
theorem displacementSpan_eq_commutator {V X P : Subgroup G} [IsElementaryAbelian 2 V]
    (hP : P ≤ actingGroup V X) :
    displacementSpan (representation V X) (inducedActor V X P) ⊤ =
      linearSpace V ⁅V, P⁆ := by
  apply le_antisymm displacementSpan_le_commutator
  let W := displacementSpan (representation V X) (inducedActor V X P) ⊤
  let D : Subgroup V := {
    carrier := {v | Additive.ofMul v ∈ W}
    one_mem' := W.zero_mem
    mul_mem' := fun ha hb => W.add_mem ha hb
    inv_mem' := fun ha => W.neg_mem ha }
  have hcomm : ⁅V, P⁆ ≤ D.map V.subtype := by
    rw [commutator_comm V P]
    apply commutator_le.mpr
    intro p hp v hv
    let a : actingGroup V X := ⟨p, hP hp⟩
    let w : Additive V := Additive.ofMul ⟨v, hv⟩
    let d := representation V X ((action V X).rangeRestrict a) w - w
    refine ⟨d.toMul, ?_, ?_⟩
    · change d ∈ W
      exact Submodule.subset_span ⟨_, ⟨a, hp, rfl⟩, w, Submodule.mem_top, rfl⟩
    · change p * v * p⁻¹ / v = ⁅p, v⁆
      simp only [div_eq_mul_inv, commutatorElement_def]
  intro v hv
  obtain ⟨w, hw, he⟩ := hcomm hv
  change Additive.ofMul w ∈ W at hw
  have he' : Additive.ofMul w = v := congrArg Additive.ofMul (Subtype.ext he)
  exact he' ▸ hw

/-- Normalization of the actual subgroup passes to its image in the literal
normalizer action. No ambient normality of P is asserted. -/
theorem inducedActor_normalized {V X P : Subgroup G}
    (m : actingGroup V X) (hm : (m : G) ∈ normalizer (P : Set G)) :
    (inducedActor V X P).conjBy ((action V X).rangeRestrict m) =
      inducedActor V X P := by
  apply mem_normalizer_iff_map_conj_eq.mp
  apply le_normalizer_map (action V X).rangeRestrict
  refine ⟨m, ?_, rfl⟩
  exact le_normalizer_comap (actingGroup V X).subtype hm

/-- Build Definition C.14.1 from the actual root action. Tight embedding and
the intrinsic root normalizer supply the two ambient geometry clauses. -/
theorem onanInput_of_root_action [Finite G]
    {T : Sylow 2 G} {z : G} {L X : Subgroup G} {n : ℕ}
    [IsElementaryAbelian 2 (space T X)]
    (h : StandardSetup T z L) (hn : 1 < n) (hXL : X ≤ L)
    (hP : relativeNormalizer L (residualRoot L X) ≤ actingGroup (space T X) X)
    (hcyclic : IsCyclic (inducedActor (space T X) X
      (relativeNormalizer L (residualRoot L X))))
    (hcard : Nat.card (inducedActor (space T X) X
      (relativeNormalizer L (residualRoot L X))) = 2 ^ n - 1)
    (hfixed : space T X ⊓ centralizer
      (relativeNormalizer L (residualRoot L X) : Set G) = commutingSylow T L)
    (htrans : ∀ v ∈ ⁅space T X, relativeNormalizer L (residualRoot L X)⁆, v ≠ 1 →
      ∀ w ∈ ⁅space T X, relativeNormalizer L (residualRoot L X)⁆, w ≠ 1 →
      ∃ p ∈ relativeNormalizer L (residualRoot L X), MulAut.conj p v = w) :
    GoldschmidtONan.Input (representation (space T X) X)
      (inducedActor (space T X) X (relativeNormalizer L (residualRoot L X))) := by
  let V := space (T : Subgroup G) X
  let C := commutingSylow T L
  let P := relativeNormalizer L (residualRoot L X)
  let S := inducedActor V X P
  let ρ := representation V X
  have hC : C ≤ V := le_inf inf_le_left (inf_le_right.trans (centralizer_le hXL))
  have hf : fixedSpace ρ S = linearSpace V C := by
    rw [fixedSpace_inducedActor hP, hfixed]
  refine {
    faithful := representation_faithful V X
    nontrivial := ?_
    cyclic := hcyclic
    odd := ?_
    transitive := ?_
    fixed_nontrivial := ?_
    ti := ?_
    normal_in_stabilizer := ?_ }
  · apply (one_lt_card_iff_ne_bot _).mp
    rw [hcard]
    have hp := Nat.lt_two_pow_self (n := n)
    omega
  · rw [hcard]
    apply (Nat.odd_sub' (by have := Nat.lt_two_pow_self (n := n); omega)).mpr
    simp only [odd_one, true_iff]
    exact even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))
  · intro v hv hv0 w hw hw0
    have hvM := displacementSpan_le_commutator hv
    have hwM := displacementSpan_le_commutator hw
    have hv1 : (v.toMul : G) ≠ 1 := fun he => hv0 (congrArg Additive.ofMul (Subtype.ext he))
    have hw1 : (w.toMul : G) ≠ 1 := fun he => hw0 (congrArg Additive.ofMul (Subtype.ext he))
    obtain ⟨p, hp, he⟩ := htrans v.toMul hvM hv1 w.toMul hwM hw1
    refine ⟨⟨(action V X).rangeRestrict ⟨p, hP hp⟩,
      ⟨⟨p, hP hp⟩, hp, rfl⟩⟩, ?_⟩
    exact congrArg Additive.ofMul (Subtype.ext he)
  · rw [hf]
    intro he
    have hz : z ∈ C := ⟨h.mem_sylow, mem_centralizer_iff.mpr fun x hx =>
      mem_centralizer_singleton_iff.mp (h.component.1 hx)⟩
    have hc : C = ⊥ := linearSpace_injective hC bot_le (he.trans (linearSpace_bot V).symm)
    have hz1 : z = 1 := by simpa only [hc, mem_bot] using hz
    have ho := h.involution
    simp [hz1] at ho
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hne
    obtain ⟨a, rfl⟩ := (action V X).rangeRestrict_surjective a
    obtain ⟨b, rfl⟩ := (action V X).rangeRestrict_surjective b
    rw [hf] at hne ⊢
    dsimp only at hne ⊢
    rw [linearSpace_map hC, linearSpace_map hC] at hne ⊢
    apply linearSpace_disjoint
    apply ti_commutingSylow h.tight hXL a.property b.property
    intro he
    exact hne (congrArg (fun D => linearSpace V D) he)
  · intro a ha
    obtain ⟨m, rfl⟩ := (action V X).rangeRestrict_surjective a
    rw [hf] at ha
    have hmC : (m : G) ∈ normalizer (C : Set G) :=
      mem_normalizer_iff_map_conj_eq.mpr ((linearSpace_map_eq_iff hC hC m).mp ha)
    exact inducedActor_normalized m (stabilizer_normalizes_parabolic h ⟨m.property, hmC⟩)

end CFSG.Quasithin.Chapter16.Intersections.RankTwo.LongRoot.Construction
