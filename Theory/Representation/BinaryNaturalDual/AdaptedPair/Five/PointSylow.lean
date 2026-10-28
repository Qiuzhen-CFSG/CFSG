module

public import Theory.Representation.BinaryNaturalDual.AdaptedPair.Five.PointSylow.Coordinates

/-!
# The point-stabilizer Sylow for the five-dimensional adapted pair

The inner upper stabilizer of (e₃,e₃*) restricts to the full U₄(2) action on
ker(e₃*) and has order 64. The reversal-twisted graph involution τ fixes this
pair and is outer. Under the explicitly supplied normal form for the standard
ambient subgroup, its intersection with the point stabilizer consists of two
disjoint cosets of that inner subgroup. It therefore has order 128 and is
exactly the subgroup obtained by adjoining τ.

If the point stabilizer has order 40320, this subgroup has odd index 315 and
hence is Sylow. The final witness preserves its actual embedding in the ambient
automorphism group and contains the marked outer involution `outerFive`.

This is a conditional helper for corrected Aschbacher–Smith H.9.1(4), printed
p.390, following the adapted-pair source audit of 6 October 2026. Its only
additional inputs beyond the coordinate action are the stated point-stabilizer
order and the ambient upper/τ normal form. Discharging these inputs and
assembling the full adapted-pair theorem belong to the parent development.
-/

public section

open BinaryLinear.OuterCyclic
open BinaryNaturalDual.VectorStabilizers
namespace BinaryNaturalDual.AdaptedPair.Five

variable (d : CoordinateAction 5)
include d

/-- The coordinate pair fixer is the actual inner-action point stabilizer. -/
theorem inner_fixes_vectorFive_iff (g : LinearGroup 5) :
    linearAction d (MulAut.conj g) vectorFive = vectorFive ↔ g ∈ pairFive := by
  rw [linearAction_inner]
  exact (mem_pairStabilizer_iff_action (axis 2) (coordinateForm 2) g).symm

/-- The U₄ comparison intertwines the given automorphism representation itself. -/
theorem upperPointEquiv_linearAction (g : upperPointGroup)
    (w : (coordinateForm (2 : Fin 5)).ker) :
    (linearAction d (MulAut.conj g.val) ((w : BinaryLinear.OuterCyclic.Space 5), 0)).1 =
      (complementCoordinates.symm ((upperPointEquiv g).val (complementCoordinates w)) :
        BinaryLinear.OuterCyclic.Space 5) := by
  rw [linearAction_inner, BinaryLinear.NaturalDualFlag.action_fst,
    upperPointEquiv_intertwines, LinearEquiv.symm_apply_apply]
  rfl

/-- The inner upper fixer as a subgroup of the actual automorphism group. -/
def innerUpperPointGroup : Subgroup (MulAut (LinearGroup 5)) := upperPointGroup.map MulAut.conj

/-- The actual inner automorphism subgroup is equivalent to the full U₄(2). -/
noncomputable def innerUpperPointEquiv : innerUpperPointGroup ≃* upperGroup 4 :=
  (upperPointGroup.equivMapOfInjective MulAut.conj (inner_injective d)).symm.trans upperPointEquiv

/-- This equivalence gives the restriction of the actual automorphism action. -/
theorem innerUpperPointEquiv_intertwines (a : innerUpperPointGroup)
    (w : (coordinateForm (2 : Fin 5)).ker) :
    (linearAction d a.val ((w : BinaryLinear.OuterCyclic.Space 5), 0)).1 =
      (complementCoordinates.symm ((innerUpperPointEquiv d a).val (complementCoordinates w)) :
        BinaryLinear.OuterCyclic.Space 5) := by
  obtain ⟨g, rfl⟩ :=
    (upperPointGroup.equivMapOfInjective MulAut.conj (inner_injective d)).surjective a
  change _ = (complementCoordinates.symm ((upperPointEquiv
    ((upperPointGroup.equivMapOfInjective MulAut.conj (inner_injective d)).symm
      ((upperPointGroup.equivMapOfInjective MulAut.conj (inner_injective d)) g))).val
        (complementCoordinates w)) : BinaryLinear.OuterCyclic.Space 5)
  rw [MulEquiv.symm_apply_apply]
  exact upperPointEquiv_linearAction d g w

theorem innerUpperPointGroup_card : Nat.card innerUpperPointGroup = 64 := by
  rw [Nat.card_congr (innerUpperPointEquiv d).toEquiv, upperFour_card]

theorem innerUpperPointGroup_le :
    innerUpperPointGroup ≤ standardGroup 5 ⊓ pointStabilizer (linearAction d) vectorFive := by
  rintro a ⟨g, hg, rfl⟩
  refine ⟨?_, (inner_fixes_vectorFive_iff d g).mpr hg.2⟩
  exact (show (upperGroup 5).map MulAut.conj ≤ standardGroup 5 from le_sup_left)
    (Subgroup.mem_map_of_mem _ hg.1)

private theorem inner_ne_inner_tau (g h : LinearGroup 5) :
    MulAut.conj g ≠ MulAut.conj h * tau 5 := by
  intro he
  apply tau_not_inner d
  have hm : (MulAut.conj h)⁻¹ * MulAut.conj g ∈ innerGroup 5 :=
    (innerGroup 5).mul_mem ((innerGroup 5).inv_mem ⟨h, rfl⟩) ⟨g, rfl⟩
  simpa only [he, inv_mul_cancel_left] using hm

variable (hnormalForm : ∀ a : MulAut (LinearGroup 5), a ∈ standardGroup 5 ↔
  ∃ u ∈ upperGroup 5, a = MulAut.conj u ∨ a = MulAut.conj u * tau 5)
include hnormalForm

/-- The ambient normal form restricts exactly to the upper pair stabilizer. -/
theorem point_normalForm (a : MulAut (LinearGroup 5)) :
    a ∈ standardGroup 5 ⊓ pointStabilizer (linearAction d) vectorFive ↔
      ∃ u ∈ upperPointGroup, a = MulAut.conj u ∨ a = MulAut.conj u * tau 5 := by
  constructor
  · rintro ⟨ha, hv⟩
    obtain ⟨u, hu, h | h⟩ := (hnormalForm a).mp ha
    · refine ⟨u, ⟨hu, ?_⟩, Or.inl h⟩
      exact (inner_fixes_vectorFive_iff d u).mp (h ▸ hv)
    · refine ⟨u, ⟨hu, ?_⟩, Or.inr h⟩
      apply (inner_fixes_vectorFive_iff d u).mp
      change linearAction d a vectorFive = vectorFive at hv
      simpa only [h, map_mul, LinearEquiv.mul_apply, tau_fixes_vectorFive] using hv
  · rintro ⟨u, hu, rfl | rfl⟩
    · exact innerUpperPointGroup_le d (Subgroup.mem_map_of_mem _ hu)
    · exact (standardGroup 5 ⊓ pointStabilizer (linearAction d) vectorFive).mul_mem
        (innerUpperPointGroup_le d (Subgroup.mem_map_of_mem _ hu))
        ⟨tau_mem_standard, tau_fixes_vectorFive d⟩

/-- The inner part of the standard point stabilizer is precisely the computed group. -/
theorem pointGroup_inf_inner :
    (standardGroup 5 ⊓ pointStabilizer (linearAction d) vectorFive) ⊓ innerGroup 5 =
      innerUpperPointGroup := by
  ext a
  constructor
  · rintro ⟨ha, hi⟩
    obtain ⟨u, hu, rfl | rfl⟩ := (point_normalForm d hnormalForm a).mp ha
    · exact Subgroup.mem_map_of_mem _ hu
    · exfalso
      apply tau_not_inner d
      have hm := (innerGroup 5).mul_mem ((innerGroup 5).inv_mem
        (show MulAut.conj u ∈ innerGroup 5 from ⟨u, rfl⟩)) hi
      simpa only [inv_mul_cancel_left] using hm
  · intro ha
    refine ⟨innerUpperPointGroup_le d ha, ?_⟩
    obtain ⟨u, _, rfl⟩ := ha
    exact ⟨u, rfl⟩

/-- Adjoining the marked outer involution gives the entire standard point stabilizer. -/
theorem pointGroup_eq_adjoin_tau :
    standardGroup 5 ⊓ pointStabilizer (linearAction d) vectorFive =
      innerUpperPointGroup ⊔ Subgroup.zpowers (tau 5) := by
  apply le_antisymm
  · intro a ha
    obtain ⟨u, hu, rfl | rfl⟩ := (point_normalForm d hnormalForm a).mp ha
    · exact (show innerUpperPointGroup ≤ innerUpperPointGroup ⊔ Subgroup.zpowers (tau 5)
        from le_sup_left) (Subgroup.mem_map_of_mem _ hu)
    · apply Subgroup.mul_mem
      · exact (show innerUpperPointGroup ≤ innerUpperPointGroup ⊔ Subgroup.zpowers (tau 5)
          from le_sup_left) (Subgroup.mem_map_of_mem _ hu)
      · exact (show Subgroup.zpowers (tau 5) ≤ innerUpperPointGroup ⊔ Subgroup.zpowers (tau 5)
          from le_sup_right) (Subgroup.mem_zpowers _)
  · apply sup_le (innerUpperPointGroup_le d)
    exact Subgroup.zpowers_le.mpr ⟨tau_mem_standard, tau_fixes_vectorFive d⟩

private noncomputable def pointParameterMap : upperPointGroup × Bool →
    ↥(standardGroup 5 ⊓ pointStabilizer (linearAction d) vectorFive) := fun p =>
  if p.2 then ⟨MulAut.conj p.1.val * tau 5,
    (standardGroup 5 ⊓ pointStabilizer (linearAction d) vectorFive).mul_mem
      (innerUpperPointGroup_le d (Subgroup.mem_map_of_mem _ p.1.property))
      ⟨tau_mem_standard, tau_fixes_vectorFive d⟩⟩
  else ⟨MulAut.conj p.1.val,
    innerUpperPointGroup_le d (Subgroup.mem_map_of_mem _ p.1.property)⟩

private theorem pointParameterMap_bijective : Function.Bijective (pointParameterMap d) := by
  constructor
  · rintro ⟨g, b⟩ ⟨h, c⟩ he
    have he' := congrArg Subtype.val he
    cases b <;> cases c
    · have hgh : g = h := Subtype.ext (inner_injective d he')
      simp [hgh]
    · exact False.elim (inner_ne_inner_tau d g.val h.val he')
    · exact False.elim (inner_ne_inner_tau d h.val g.val he'.symm)
    · have he'' : MulAut.conj g.val = MulAut.conj h.val := mul_right_cancel he'
      have hgh : g = h := Subtype.ext (inner_injective d he'')
      simp [hgh]
  · intro a
    obtain ⟨u, hu, he | he⟩ := (point_normalForm d hnormalForm a.val).mp a.property
    · exact ⟨(⟨u, hu⟩, false), Subtype.ext he.symm⟩
    · exact ⟨(⟨u, hu⟩, true), Subtype.ext he.symm⟩

/-- Two disjoint cosets of the actual order-64 inner subgroup. -/
theorem pointGroup_card :
    Nat.card ↥(standardGroup 5 ⊓ pointStabilizer (linearAction d) vectorFive) = 128 := by
  rw [← Nat.card_congr (Equiv.ofBijective (pointParameterMap d)
    (pointParameterMap_bijective d hnormalForm)), Nat.card_prod, upperPointGroup_card]
  simp

/-- The standard point stabilizer, viewed as a Sylow subgroup of the full fixer. -/
noncomputable def pointSylow
    (hcard : Nat.card (pointStabilizer (linearAction d) vectorFive) = 40320) :
    Sylow 2 (pointStabilizer (linearAction d) vectorFive) := by
  let H := standardGroup 5 ⊓ pointStabilizer (linearAction d) vectorFive
  let K := H.subgroupOf (pointStabilizer (linearAction d) vectorFive)
  have hK : Nat.card K = 128 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show H ≤
      pointStabilizer (linearAction d) vectorFive from inf_le_right)).toEquiv).trans
        (pointGroup_card d hnormalForm)
  have hi : K.index = 315 := by
    have hh := K.index_mul_card
    rw [hK, hcard] at hh
    omega
  exact (IsPGroup.of_card (p := 2) (n := 7) hK).toSylow (by rw [hi]; decide)

/-- The Sylow witness has exactly the required ambient image. -/
theorem pointSylow_map
    (hcard : Nat.card (pointStabilizer (linearAction d) vectorFive) = 40320) :
    (pointSylow d hnormalForm hcard : Subgroup _).map
      (pointStabilizer (linearAction d) vectorFive).subtype =
        standardGroup 5 ⊓ pointStabilizer (linearAction d) vectorFive := by
  exact Subgroup.map_subgroupOf_eq_of_le inf_le_right

/-- The specified outer involution belongs to the constructed Sylow subgroup. -/
theorem outerFive_mem_pointSylow
    (hcard : Nat.card (pointStabilizer (linearAction d) vectorFive) = 40320) :
    (⟨outerFive, tau_fixes_vectorFive d⟩ : pointStabilizer (linearAction d) vectorFive) ∈
      pointSylow d hnormalForm hcard := by
  exact ⟨tau_mem_standard, tau_fixes_vectorFive d⟩

omit hnormalForm in
theorem outerFive_not_inner : outerFive ∉ innerGroup 5 := tau_not_inner d

omit hnormalForm in
theorem outerFive_sq : outerFive ^ 2 = 1 := tau_sq d

/-- The concrete conditional Sylow witness, retaining the marked outer involution. -/
theorem exists_pointSylow
    (hcard : Nat.card (pointStabilizer (linearAction d) vectorFive) = 40320) :
    ∃ P : Sylow 2 (pointStabilizer (linearAction d) vectorFive),
      (P : Subgroup _).map (pointStabilizer (linearAction d) vectorFive).subtype =
        standardGroup 5 ⊓ pointStabilizer (linearAction d) vectorFive ∧
      (⟨outerFive, tau_fixes_vectorFive d⟩ : pointStabilizer (linearAction d) vectorFive) ∈ P ∧
      outerFive ∉ innerGroup 5 ∧ outerFive ^ 2 = 1 :=
  ⟨pointSylow d hnormalForm hcard, pointSylow_map d hnormalForm hcard,
    outerFive_mem_pointSylow d hnormalForm hcard, outerFive_not_inner d, outerFive_sq d⟩

end BinaryNaturalDual.AdaptedPair.Five
