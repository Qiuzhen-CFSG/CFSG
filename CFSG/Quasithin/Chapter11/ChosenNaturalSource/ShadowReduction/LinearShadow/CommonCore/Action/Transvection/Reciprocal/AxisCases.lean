module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Transvection.Reciprocal

/-!
# The common axis of the literal reciprocal action

Every noncentral actor has the same centralizer in the selected conjugate A.
The forward unipotent coordinates prove this directly. The entire reciprocal
commutator lies in that axis. Comparing its order q^m with the axis of index q
bounds m by the original module dimension minus one; in SL₃ this gives m=1 or 2.
These conclusions retain the actual original coordinates and selected g.
Source: Aschbacher--Smith 11.3.7(4), printed p.773 of refs/quasithin.pdf.
-/

@[expose] public noncomputable section
open Subgroup Matrix
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
open CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] {T : Sylow 2 G} {H A : Subgroup G} {F : BinaryField}
namespace NaturalSylowCoordinates
variable {m : ℕ} (n : NaturalSylowCoordinates T H A F m)
include n

/-- Every noncentral reciprocal actor has exactly the same original axis. -/
theorem centralizer_cyclic_eq_common (hm : 0 < m) (w : omegaClosure T H)
    (hw : (w : G) ∉ centralizer (A : Set G)) :
    A ⊓ centralizer (zpowers (w : G) : Set G) =
      A ⊓ centralizer (omegaClosure T H : Set G) := by
  apply le_antisymm
  · rintro a ⟨ha,hc⟩
    refine ⟨ha,?_⟩
    apply (n.parameter_eq_one_iff hm ⟨a,ha⟩).mp
    obtain ⟨i,hi⟩ : ∃ i, (n.coordinates w).toAdd i 1 ≠ 0 := by
      by_contra! hz
      exact hw ((n.mem_fixed_iff w).mpr hz)
    have hd : n.displacement ⟨a,ha⟩ w = 1 := by
      apply Subtype.ext
      change a * (w : G) * a⁻¹ * (w : G)⁻¹ = 1
      have hcomm := hc (w : G) (mem_zpowers (w : G))
      rw [← hcomm]
      group
    have he := congrFun (n.displacement_coordinates ⟨a,ha⟩ w i) 0
    rw [hd,map_one] at he
    have hz : (n.parameter ⟨a,ha⟩).toAdd * (n.coordinates w).toAdd i 1 = 0 := he.symm
    apply Multiplicative.toAdd.injective
    exact (mul_eq_zero.mp hz).resolve_right hi
  · exact inf_le_inf_left A (centralizer_le (zpowers_le.mpr w.property))

/-- The reciprocal commutator is contained in the literal common axis. -/
theorem commutator_le_common_axis
    (hN : omegaClosure T H ≤ normalizer (A : Set G)) :
    ⁅A,omegaClosure T H⁆ ≤ A ⊓ centralizer (omegaClosure T H : Set G) := by
  apply le_inf (le_normalizer_iff_commutator_le_left.mp hN)
  rw [n.commutator_eq_fixed]
  intro w hw u hu
  have he : (⟨u,hu⟩ : omegaClosure T H) * ⟨w,hw.1⟩ = ⟨w,hw.1⟩ * ⟨u,hu⟩ := by
    apply n.coordinates.injective
    rw [map_mul,map_mul,mul_comm]
  exact congrArg Subtype.val he

/-- The forward multiplicity is at most one less than the field dimension
of the actual reciprocal module. This is an order comparison of the literal
commutator and common centralizer, with no assumed transvection model. -/
theorem multiplicity_lt_dimension [Finite G] (hm : 0 < m)
    (hN : omegaClosure T H ≤ normalizer (A : Set G)) {d : ℕ}
    (hcard : Nat.card A = Nat.card F.Carrier ^ d) : m < d := by
  let C := A ⊓ centralizer (omegaClosure T H : Set G)
  have hCcard : Nat.card (C.subgroupOf A) = Nat.card C :=
    Nat.card_congr (subgroupOfEquivOfLe (show C ≤ A from inf_le_left)).toEquiv
  have hCsub : C.subgroupOf A = (centralizer (omegaClosure T H : Set G)).comap A.subtype :=
    inf_subgroupOf_left _ _
  have he := (C.subgroupOf A).card_mul_index
  rw [hCcard,hCsub,n.centralizer_index hm,hcard] at he
  have hle : Nat.card F.Carrier ^ m ≤ Nat.card C := by
    rw [← n.card_fixed,← n.commutator_eq_fixed]
    exact Nat.card_le_card_of_injective _
      (Subgroup.inclusion_injective (n.commutator_le_common_axis hN))
  have hp : Nat.card F.Carrier ^ (m+1) ≤ Nat.card F.Carrier ^ d := by
    rw [pow_succ,← he]
    exact Nat.mul_le_mul_right _ hle
  have hb : 1 < Nat.card F.Carrier := Finite.one_lt_card
  exact (Nat.pow_le_pow_iff_right hb).mp hp

/-- When the commutator has the full axis order, it is the literal common axis. -/
theorem commutator_eq_common_axis_of_card [Finite G] (hm : 0 < m)
    (hN : omegaClosure T H ≤ normalizer (A : Set G))
    (hcard : Nat.card A = Nat.card F.Carrier ^ (m+1)) :
    ⁅A,omegaClosure T H⁆ = A ⊓ centralizer (omegaClosure T H : Set G) := by
  let C := A ⊓ centralizer (omegaClosure T H : Set G)
  have hCcard : Nat.card (C.subgroupOf A) = Nat.card C :=
    Nat.card_congr (subgroupOfEquivOfLe (show C ≤ A from inf_le_left)).toEquiv
  have hCsub : C.subgroupOf A = (centralizer (omegaClosure T H : Set G)).comap A.subtype :=
    inf_subgroupOf_left _ _
  have he := (C.subgroupOf A).card_mul_index
  rw [hCcard,hCsub,n.centralizer_index hm,hcard,pow_succ] at he
  have hc : Nat.card C = Nat.card F.Carrier ^ m := by
    exact Nat.mul_right_cancel Nat.card_pos he
  apply eq_of_le_of_card_ge (n.commutator_le_common_axis hN)
  rw [n.commutator_eq_fixed,n.card_fixed]
  exact hc.le

end NaturalSylowCoordinates

open LocalGeometry Representation
variable [Finite G] {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}

private theorem sl3_conjugate_card
    (a : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) (g : G) :
    Nat.card (V.map (MulAut.conj g).toMonoidHom) = Nat.card S.field.Carrier ^ 3 := by
  rw [card_map_of_injective (MulAut.conj g).injective]
  calc
    Nat.card V = Nat.card ((Coordinates.sl3 a).preimage ⊤) :=
      congrArg (fun B : Subgroup G => Nat.card B) (Coordinates.sl3 a).preimage_top.symm
    _ = _ := by
      rw [Closure.Nonabelian.card_preimage (.sl3 a) hfixed ⊤]
      rw [← S.field.card_eq]
      change Nat.card S.field.Carrier ^ Module.finrank S.field.Carrier
        (⊤ : Submodule S.field.Carrier (Fin 3 → S.field.Carrier)) = _
      rw [finrank_top,Module.finrank_fin_fun]

/-- The literal original SL₃ reciprocal action has one or two forward summands. -/
theorem source_sl3_multiplicity_cases
    (a : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) (g : G) {m : ℕ}
    (n : NaturalSylowCoordinates T H (V.map (MulAut.conj g).toMonoidHom) S.field m)
    (hm : 0 < m)
    (hN : omegaClosure T H ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) :
    m = 1 ∨ m = 2 := by
  have h := n.multiplicity_lt_dimension hm hN (sl3_conjugate_card a hfixed g)
  omega

/-- In the doubled SL₃ case the entire actual commutator is the common axis. -/
theorem source_sl3_doubled_commutator_eq_axis
    (a : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) (g : G)
    (n : NaturalSylowCoordinates T H (V.map (MulAut.conj g).toMonoidHom) S.field 2)
    (hN : omegaClosure T H ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) :
    ⁅V.map (MulAut.conj g).toMonoidHom,omegaClosure T H⁆ =
      V.map (MulAut.conj g).toMonoidHom ⊓ centralizer (omegaClosure T H : Set G) :=
  n.commutator_eq_common_axis_of_card (by decide) hN (sl3_conjugate_card a hfixed g)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
