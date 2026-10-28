module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Initial.Center.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.Exclusion.MovingAbelian.Quotient

/-!
# Passing an offender from the radius center quotient to its moving section

Fixed classes in V/Z(V), restricted to P = [V,Ltilde], remain fixed in
P/Z(P). Comparing their preimage indices proves that fixed codimension
cannot increase. The action on each quotient is literal conjugation by
the same vertex stabilizer.

`HasRadiusCenterOffender` records the source FF bound using an actual
projection with kernel Q. Only the image of the actor must be elementary;
its full preimage and the action of Q on the quotient remain unrestricted.
Constructing this witness under failure of the center containment is the
geometric first paragraph of MS93 (4.6.1), not a conclusion of this module.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.6.1), printed pp.900--901.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation.BinaryOffender
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Initial
open NaturalStructure.Exclusion

private theorem fixedSpace_subgroup_index {G T : Type*} [Group G] [Group T]
    [IsElementaryAbelian 2 T] [Finite T] (action : G →* MulAut T) (A : Subgroup G) :
    (Subgroup.toAddSubgroup.symm
      (fixedSpace (Offenders.linearize action) A).toAddSubgroup).index =
      2 ^ fixedCodim (Offenders.linearize action) A := by
  let ρ := Offenders.linearize action
  let C := Subgroup.toAddSubgroup.symm (fixedSpace ρ A).toAddSubgroup
  let e : fixedSpace ρ A ≃ C := {
    toFun := fun v => ⟨v.val.toMul, v.property⟩
    invFun := fun x => ⟨Additive.ofMul x.val, x.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hC : Nat.card C = 2 ^ Module.finrank (ZMod 2) (fixedSpace ρ A) := by
    have hf := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace ρ A)
    rw [Nat.card_zmod] at hf
    exact (Nat.card_congr e).symm.trans hf
  have hT : Nat.card T = 2 ^ Module.finrank (ZMod 2) (Additive T) :=
    (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive T)).trans (by rw [Nat.card_zmod])
  have hdim := fixedCodim_add_finrank ρ A
  have hmul := C.card_mul_index
  rw [hC, hT, ← hdim, pow_add, Nat.mul_comm (2 ^ fixedCodim ρ A)] at hmul
  exact Nat.eq_of_mul_eq_mul_left (by positivity) hmul

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- Restricting the radius central quotient to its moving central section
does not increase the displacement of any subgroup of the actual stabilizer. -/
theorem moving_fixedCodim_le_radiusCenter
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (a : Vertex R) (ha : color R a = false)
    (hfixed : ⁅V R a, V R a⁆ ≤ fixedCore R a)
    (A : Subgroup (stabilizer R a)) :
    letI := radiusCenterQuotient_elementary common hb a ha
    letI := moving_central_quotient_elementary geometry (by omega) a ha hfixed
    fixedCodim (Offenders.linearize (movingQuotientAction a)) A ≤
      fixedCodim (Offenders.linearize (radiusCenterQuotientAction a)) A := by
  let := radiusCenterQuotient_elementary common hb a ha
  let := moving_central_quotient_elementary geometry (by omega) a ha hfixed
  let := finite_radius common a ha
  let := finite_moving geometry common.large_distance a ha
  let P := Vcirc R a
  let hPV : P ≤ V R a := le_normalizer_iff_commutator_le_left.mp
    ((Ltilde_le_stabilizer a).trans (V_normalized a))
  let qV := QuotientGroup.mk' (center (V R a))
  let qP := QuotientGroup.mk' (center P)
  let C := Subgroup.toAddSubgroup.symm
    (fixedSpace (Offenders.linearize (radiusCenterQuotientAction a)) A).toAddSubgroup
  let D := Subgroup.toAddSubgroup.symm
    (fixedSpace (Offenders.linearize (movingQuotientAction a)) A).toAddSubgroup
  let K := C.comap qV
  have hKD : K.comap (inclusion hPV) ≤ D.comap qP := by
    intro p hp g
    have hfix : radiusCenterQuotientAction a g.val (qV (inclusion hPV p)) =
        qV (inclusion hPV p) := congrArg Additive.toMul (hp g)
    obtain ⟨z, hz, he⟩ := (radiusCenterQuotientAction_fixed_iff a g.val
      (inclusion hPV p)).mp hfix
    let d : P := movingAction a g.val p / p
    have hd : (d : FreeAmalgam R) = ⁅(g.val : FreeAmalgam R), (p : FreeAmalgam R)⁆ := by
      change (movingAction a g.val p : FreeAmalgam R) / (p : FreeAmalgam R) = _
      rw [movingAction_apply, div_eq_mul_inv, commutatorElement_def]
    have hdc : d ∈ center P := by
      apply mem_center_iff.mpr
      intro v
      apply Subtype.ext
      have h := congrArg Subtype.val (mem_center_iff.mp hz (inclusion hPV v))
      change (v : FreeAmalgam R) * (d : FreeAmalgam R) =
        (d : FreeAmalgam R) * (v : FreeAmalgam R)
      rw [hd]
      change (v : FreeAmalgam R) * (z : FreeAmalgam R) =
        (z : FreeAmalgam R) * (v : FreeAmalgam R) at h
      rw [show (z : FreeAmalgam R) =
        ⁅(g.val : FreeAmalgam R), (p : FreeAmalgam R)⁆ from he] at h
      exact h
    change Additive.ofMul (movingQuotientAction a g.val (qP p)) = Additive.ofMul (qP p)
    apply congrArg Additive.ofMul
    rw [movingQuotientAction_apply]
    exact QuotientGroup.eq_iff_div_mem.mpr hdc
  have hindex : D.index ≤ C.index := calc
    D.index = (D.comap qP).index :=
      (D.index_comap_of_surjective (QuotientGroup.mk'_surjective (center P))).symm
    _ ≤ (K.comap (inclusion hPV)).index :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero (K.comap (inclusion hPV)).index_ne_zero_of_finite)
        (index_dvd_of_le hKD)
    _ = K.relIndex (inclusion hPV).range := K.index_comap _
    _ ≤ K.relIndex ⊤ := relIndex_le_of_le_right le_top (by
      rw [relIndex_top_right]
      exact K.index_ne_zero_of_finite)
    _ = K.index := K.relIndex_top_right
    _ = C.index := C.index_comap_of_surjective (QuotientGroup.mk'_surjective (center (V R a)))
  rw [fixedSpace_subgroup_index, fixedSpace_subgroup_index] at hindex
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hindex

/-- A projected offender on the source central quotient. The marked quotient
has precisely kernel Q, and the elementary condition concerns the actor image. -/
def HasRadiusCenterOffender (common : CommonFacts R source geometry)
    (hb : geometry.b R = 4) (a : Vertex R) (ha : color R a = false) : Prop :=
  letI := radiusCenterQuotient_elementary common hb a ha
  ∃ (π : stabilizer R a →* SL) (A : Subgroup (stabilizer R a)),
    Function.Surjective π ∧ π.ker = (Q R a).subgroupOf (stabilizer R a) ∧
    IsElementaryAbelian 2 (A.map π) ∧ A.map π ≠ ⊥ ∧
    fixedCodim (Offenders.linearize (radiusCenterQuotientAction a)) A ≤ rank (A.map π)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Initial
