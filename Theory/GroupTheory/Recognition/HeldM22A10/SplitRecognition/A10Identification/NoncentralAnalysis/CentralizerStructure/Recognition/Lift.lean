module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Core
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Section
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Coordinates
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.SourceChecks
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.IsPerfect

/-!
# The inverse image of Held's quotient core

For the supplied normal index-four subgroup M of Q = C/<mu>, `lift` is
its actual inverse image in C. The restricted quotient map has central
kernel of order two and identifies lift/kernel with M. The image of the
intrinsic derived subgroup of lift is a canonical normal candidate for A.

If M is perfect, this candidate maps onto M. Injectivity is a separate
splitting obligation. It implies that the candidate avoids <mu>; together
with surjectivity this gives the internal product and index eight in C.
No group identification or splitting is assumed by the definitions.

Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, proof of Lemma 4.2, p.234.
-/

open Subgroup
noncomputable section
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure
universe u
variable {G : Type u} [Group G] {D : LocalData G}
  {e : D.centralizer ≃* CentralizerModels.a10Centralizer}

namespace QuotientCore
variable (c : QuotientCore D e)

/-- The inverse image of M under C → C/<mu>. -/
@[expose] public def lift : Subgroup (C D e) := c.subgroup.comap (q D e)

public instance lift_normal : c.lift.Normal := c.normal.comap (q D e)

public theorem lift_index : c.lift.index = 4 :=
  (c.subgroup.index_comap_of_surjective (QuotientGroup.mk'_surjective (Z D e))).trans c.index

public theorem Z_le_lift : Z D e ≤ c.lift := by
  intro x hx
  change q D e x ∈ c.subgroup
  have hxq : q D e x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
  rw [hxq]
  exact c.subgroup.one_mem

public theorem pi_mem_lift : pi D e ∈ c.lift := c.p_mem

@[expose] public def liftMap : c.lift →* c.subgroup := (q D e).subgroupComap c.subgroup

public theorem liftMap_surjective : Function.Surjective c.liftMap := by
  intro x
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (Z D e) x.1
  refine ⟨⟨y, ?_⟩, ?_⟩
  · change q D e y ∈ c.subgroup
    exact hy ▸ x.property
  · exact Subtype.ext hy

@[expose] public def liftKernel : Subgroup c.lift := (Z D e).subgroupOf c.lift

public instance liftKernel_normal : c.liftKernel.Normal := inferInstanceAs
  ((Z D e).subgroupOf c.lift).Normal

public theorem ker_liftMap : c.liftMap.ker = c.liftKernel := by
  ext x
  change c.liftMap x = 1 ↔ x.1 ∈ Z D e
  rw [Subtype.ext_iff]
  exact QuotientGroup.eq_one_iff x.1

public theorem liftKernel_le_center : c.liftKernel ≤ center c.lift := by
  intro x hx
  apply mem_center_iff.mpr
  intro y
  exact Subtype.ext (mem_center_iff.mp (Z_le_center D e hx) y.1)

public theorem liftKernel_card : Nat.card c.liftKernel = 2 :=
  (Nat.card_congr (subgroupOfEquivOfLe c.Z_le_lift).toEquiv).trans (Z_card D e)

public def liftQuotientEquiv : (c.lift ⧸ c.liftKernel) ≃* c.subgroup :=
  (QuotientGroup.quotientMulEquivOfEq c.ker_liftMap.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective c.liftMap c.liftMap_surjective)

public theorem lift_card : Nat.card c.lift = 2 * Nat.card c.subgroup := by
  rw [card_eq_card_quotient_mul_card_subgroup c.liftKernel,
    Nat.card_congr c.liftQuotientEquiv.toEquiv, c.liftKernel_card, mul_comm]

/-- The intrinsic derived subgroup of the inverse image, mapped into C. -/
@[expose] public def derivedLift : Subgroup (C D e) :=
  (_root_.commutator c.lift).map c.lift.subtype

public theorem derivedLift_le_lift : c.derivedLift ≤ c.lift := map_subtype_le _

public instance derivedLift_normal : c.derivedLift.Normal := by
  unfold derivedLift
  rw [map_subtype_commutator]
  infer_instance

@[expose] public def derivedMap : c.derivedLift →* c.subgroup :=
  c.liftMap.comp (inclusion c.derivedLift_le_lift)

/-- Perfectness of M supplies surjectivity, independently of splitting. -/
public theorem derivedMap_surjective [Group.IsPerfect c.subgroup] :
    Function.Surjective c.derivedMap := by
  have hmap : (_root_.commutator c.lift).map c.liftMap = ⊤ := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr c.liftMap_surjective]
    exact Group.IsPerfect.commutator_eq_top
  intro x
  obtain ⟨y, hy, hyx⟩ := (show x ∈ (_root_.commutator c.lift).map c.liftMap by
    rw [hmap]; trivial)
  exact ⟨⟨y.1, mem_map_of_mem c.lift.subtype hy⟩, hyx⟩

public theorem Z_inf_derivedLift_eq_bot_of_injective
    (hinj : Function.Injective c.derivedMap) : Z D e ⊓ c.derivedLift = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  have hq : q D e x = 1 := (QuotientGroup.eq_one_iff x).mpr hx.1
  have hmap : c.derivedMap ⟨x, hx.2⟩ = c.derivedMap 1 := by
    rw [map_one]
    exact Subtype.ext hq
  exact congrArg Subtype.val (hinj hmap)

public theorem Z_sup_derivedLift_eq_lift_of_surjective
    (hsurj : Function.Surjective c.derivedMap) : Z D e ⊔ c.derivedLift = c.lift := by
  apply le_antisymm (sup_le c.Z_le_lift c.derivedLift_le_lift)
  intro x hx
  obtain ⟨y, hy⟩ := hsurj (c.liftMap ⟨x, hx⟩)
  have hyq : q D e y.1 = q D e x := congrArg Subtype.val hy
  have hxy : q D e (x * y.1⁻¹) = 1 := by
    rw [map_mul, map_inv, hyq, mul_inv_cancel]
  have hz : x * y.1⁻¹ ∈ Z D e := (QuotientGroup.eq_one_iff _).mp hxy
  have hprod := (Z D e ⊔ c.derivedLift).mul_mem
    ((le_sup_left : Z D e ≤ Z D e ⊔ c.derivedLift) hz)
    ((le_sup_right : c.derivedLift ≤ Z D e ⊔ c.derivedLift) y.property)
  simpa only [inv_mul_cancel_right] using hprod

public theorem derivedLift_index [Finite G]
    (hbij : Function.Bijective c.derivedMap) : c.derivedLift.index = 8 := by
  have hcard : Nat.card c.derivedLift = Nat.card c.subgroup :=
    Nat.card_congr (Equiv.ofBijective c.derivedMap hbij)
  have hJ := c.lift.index_mul_card
  rw [c.lift_index, c.lift_card] at hJ
  have hA := c.derivedLift.index_mul_card
  rw [hcard, ← hJ] at hA
  have hpos : 0 < Nat.card c.subgroup := Nat.card_pos
  nlinarith

end QuotientCore
end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure
