module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.Nonsolvable.Remaining
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.Nonsolvable.ModelBounds
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTransfer
public import Theory.Mathieu.M12.Properties.Simplicity

/-!
# Exceptional component orders in the F.6 comparison

The alternating group A₇ and its perfect central triple cover are
quasisimple, hence equal their generalized Fitting groups. The normal
alternating subgroup of S₇ and the specified derived subgroups of the
hatted symmetric models are components. Their orders, computed from the
actual center quotients for the covers, exceed 168. In M₁₂, simplicity
makes the nontrivial generalized Fitting subgroup the whole group.

The retained small subnormal image bounds the same component order by
168, excluding all six exceptional models. The final application uses
the original projection I/O₂(I) → I/O₃′(I) and its actual subgroup image.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 14.7.70, printed p.1075, and F.6.18(7)–(9),(12), printed pp.309–310.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.Nonsolvable
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition

private theorem exceptional_alternating_quasisimple {n : ℕ} (hn : 5 ≤ n) :
    IsQuasisimple (alternatingGroup (Fin n)) where
  toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simpa using hn)⟩
  simple := by
    let : IsSimpleGroup (alternatingGroup (Fin n)) :=
      alternatingGroup.isSimpleGroup (by simpa using hn)
    exact ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simpa using (show 4 ≤ n by omega)))).trans
        QuotientGroup.quotientBot).isSimpleGroup

private theorem exceptional_cover_quasisimple {D : Type*} [Group D] {n : ℕ}
    (h : FSource.TripleAlternating D n) (hn : 5 ≤ n) : IsQuasisimple D := by
  let : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by simpa using hn)
  obtain ⟨e⟩ := h.quotient
  exact { toIsPerfect := h.perfect, simple := e.isSimpleGroup }

private theorem exceptional_cover_card {D : Type*} [Group D] {n : ℕ}
    [Nontrivial (Fin n)] (h : FSource.TripleAlternating D n) :
    Nat.card D = (n.factorial / 2) * 3 := by
  obtain ⟨ec⟩ := h.center
  obtain ⟨eq⟩ := h.quotient
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center D),
    Nat.card_congr ec.toEquiv, Nat.card_congr eq.toEquiv, nat_card_alternatingGroup]
  simp

private theorem exceptional_fitting_card {D : Type*} [Group D] [IsQuasisimple D] :
    Nat.card (generalizedFitting D) = Nat.card D := by
  rw [generalizedFitting_eq_top_of_quasisimple]
  exact Nat.card_congr topEquiv.toEquiv

private theorem exceptional_symmetric_cover_bound {D : Type*} [Group D] [Finite D]
    {n : ℕ} (h : FSource.TripleSymmetric D n) (hn : n = 6 ∨ n = 7) :
    168 < Nat.card (generalizedFitting D) := by
  let : IsQuasisimple (commutator D) := exceptional_cover_quasisimple h.derived (by omega)
  have hl := card_le_of_le (component_le_generalizedFitting D (commutator D)
    ⟨(inferInstance : (commutator D).Normal).isSubnormal, inferInstance⟩)
  rcases hn with rfl | rfl <;>
    rw [exceptional_cover_card h.derived] at hl <;>
    norm_num [Nat.factorial] at hl ⊢ <;> omega

variable {D : Type*} [Group D] [Finite D]

private theorem exceptional_symmetric_bound (e : D ≃* Equiv.Perm (Fin 7)) :
    168 < Nat.card (generalizedFitting D) := by
  let : IsQuasisimple (alternatingGroup (Fin 7)) := exceptional_alternating_quasisimple (by decide)
  have hc : IsComponent (Equiv.Perm (Fin 7)) (alternatingGroup (Fin 7)) :=
    ⟨(inferInstance : (alternatingGroup (Fin 7)).Normal).isSubnormal, inferInstance⟩
  have hl := card_le_of_le (component_le_generalizedFitting D _ (hc.map_equiv e.symm))
  rw [card_map_of_injective e.symm.injective, nat_card_alternatingGroup] at hl
  norm_num [Nat.factorial] at hl
  omega

private theorem exceptional_mathieu_bound
    (hq : IsQuasisimple (generalizedFitting D)) (e : D ≃* Sporadic.Mathieu.M12) :
    168 < Nat.card (generalizedFitting D) := by
  let : IsSimpleGroup Sporadic.Mathieu.M12 := Sporadic.Mathieu.m12_isSimpleGroup
  let : IsSimpleGroup D := e.isSimpleGroup
  let : IsSimpleGroup ((generalizedFitting D) ⧸ center (generalizedFitting D)) := hq.simple
  let : Nontrivial (generalizedFitting D) :=
    (QuotientGroup.mk'_surjective (center (generalizedFitting D))).nontrivial
  have hn : generalizedFitting D ≠ ⊥ := (nontrivial_iff_ne_bot _).mp inferInstance
  have ht : generalizedFitting D = ⊤ :=
    (inferInstance : (generalizedFitting D).Normal).eq_bot_or_eq_top.resolve_left hn
  rw [ht, Nat.card_congr topEquiv.toEquiv, Nat.card_congr e.toEquiv,
    Sporadic.Mathieu.m12_order]
  decide

/-- Every exceptional F.6 ambient model has component order greater than 168. -/
theorem fitting_card_gt_of_exceptional (hq : IsQuasisimple (generalizedFitting D))
    (h : ExceptionalModel D) : 168 < Nat.card (generalizedFitting D) := by
  rcases h with he | h | hs | he | hs | he
  · obtain ⟨e⟩ := he
    let : IsQuasisimple (alternatingGroup (Fin 7)) := exceptional_alternating_quasisimple (by decide)
    let : IsQuasisimple D := IsQuasisimple.of_mulEquiv e.symm
    rw [exceptional_fitting_card, Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  · let : IsQuasisimple D := exceptional_cover_quasisimple h (by decide)
    rw [exceptional_fitting_card, exceptional_cover_card h]
    norm_num [Nat.factorial]
  · obtain ⟨h⟩ := hs
    exact exceptional_symmetric_cover_bound h (Or.inl rfl)
  · obtain ⟨e⟩ := he
    exact exceptional_symmetric_bound e
  · obtain ⟨h⟩ := hs
    exact exceptional_symmetric_cover_bound h (Or.inr rfl)
  · obtain ⟨e⟩ := he
    exact exceptional_mathieu_bound hq e

/-- A small subnormal subgroup excludes every exceptional ambient model. -/
theorem not_exceptional_model (K : Subgroup D) (hK : K.IsSubnormal) (hm : SmallModel K)
    (hq : IsQuasisimple (generalizedFitting D)) : ¬ ExceptionalModel D := by
  intro h
  exact (Nat.not_lt_of_ge (fitting_card_le K hK hm hq))
    (fitting_card_gt_of_exceptional hq h)

open Representation Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (c : CriticalPath (L := L) F)

/-- The faithful image of the original small subgroup excludes exceptional
models for the literal bang quotient I/O₃′(I). -/
theorem exceptional_bang_obstruction (small : SmallSubnormal c)
    (hq : IsQuasisimple (generalizedFitting ((I c) ⧸ pPrimeCore 3 (I c)))) :
    ¬ ExceptionalModel ((I c) ⧸ pPrimeCore 3 (I c)) := by
  obtain ⟨K, _, _, hN, hmN⟩ := retained_small_image c small
  exact not_exceptional_model (K.map (plusToBang c)) hN hmN hq

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.Nonsolvable
