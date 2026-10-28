module

public import Theory.AlgebraicGroup.RootSystems.G2ChevalleyBorelWeylExchange
public import Theory.AlgebraicGroup.RootSystems.G2ChevalleyRankOneExchange
public import Theory.AlgebraicGroup.Tori.UnipotentIntersection

set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

/-!
# Root exclusion for normal unipotents in the explicit `G2` carrier

This module isolates the characteristic-free rank-one obstruction needed by
the normal-unipotent argument for the explicit fourteen-dimensional `G2`
Chevalley carrier.  If a closed subgroup contains a simple root curve and is
normal, its longest-Weyl conjugates contain the opposite simple curve.  The
nonsingular rank-one exchange of these two curves then puts a nontrivial
simple coroot point in the subgroup.  Since that point belongs to the split
torus, the torus/unipotent intersection theorem contradicts unipotence.

Only the displayed carrier, root curves, longest-Weyl conjugation, and
rank-one exchange are used.  In particular the argument does not use any
semisimplicity, center calculation, or general Chevalley classification, and
the integral exchange identities keep it valid in characteristics two and
three.
-/

open Theory AlgebraicGroup

namespace Theory.AlgebraicGroup.G2Chevalley

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

private lemma rootCorootTorusFactor_ne_one (i : Fin 2) (c : kˣ) (hc : c ≠ 1) :
    rootCorootTorusFactor (k := k) (simpleRoot i) c ≠ 1 := by
  letI : AlgebraicGroup (splitTorus (k := k)).carrierVariety :=
    (splitTorus (k := k)).carrierAlgebraicGroup
  intro h
  let p : Variety.Point (dVariety k 2) :=
    rootCorootTorusPoint (k := k) (simpleRoot i) c
  let p1 : Variety.Point (dVariety k 2) :=
    rootCorootTorusPoint (k := k) (simpleRoot i) 1
  have hp1 : p1 = 1 := by
    apply (dPointEquiv 2).injective
    rw [dPointEquiv_one]
    funext j
    fin_cases i <;> fin_cases j <;>
    simp [p1, rootCorootTorusPoint, rootCorootTorusParameter, simpleRoot,
      Root.short, Root.long]
  have hfac1 : rootCorootTorusFactor (k := k) (simpleRoot i) 1 = 1 := by
    change (splitTorusMorphism (k := k)).onPoints p1 = 1
    rw [hp1]
    exact (splitTorusMorphism (k := k)).onPoints.map_one
  have hi : (splitTorusMorphism (k := k)).onPoints p =
      (splitTorusMorphism (k := k)).onPoints p1 := by
    change rootCorootTorusFactor (k := k) (simpleRoot i) c =
      rootCorootTorusFactor (k := k) (simpleRoot i) 1
    rw [h, hfac1]
  have hi' : (splitTorus (k := k)).inclusion.onPoints
      ((splitTorusIso (k := k)).hom.onPoints p) =
      (splitTorus (k := k)).inclusion.onPoints
        ((splitTorusIso (k := k)).hom.onPoints p1) := by
    rw [splitTorusIso_inclusion_apply, splitTorusIso_inclusion_apply]
    exact hi
  have hp : p = p1 := by
    have hs : (splitTorusIso (k := k)).hom.onPoints p =
        (splitTorusIso (k := k)).hom.onPoints p1 :=
      (splitTorus (k := k)).inclusion_injective hi'
    apply congrArg (splitTorusIso (k := k)).inv.onPoints at hs
    rw [(splitTorusIso (k := k)).hom_inv_id,
      (splitTorusIso (k := k)).hom_inv_id] at hs
    exact hs
  have hcoord := congrArg (dPointEquiv 2) hp
  fin_cases i
  · have h0 := congrFun hcoord 0
    have hv : (c : k) = 1 := by
      simpa [p, p1, rootCorootTorusPoint, rootCorootTorusParameter, simpleRoot,
        Root.short, Root.long] using h0
    exact hc (Units.ext_iff.mpr hv)
  · have h1 := congrFun hcoord 1
    have hv : (c : k) = 1 := by
      simpa [p, p1, rootCorootTorusPoint, rootCorootTorusParameter, simpleRoot,
        Root.short, Root.long] using h1
    exact hc (Units.ext_iff.mpr hv)

private lemma middle_mem_of_factorization
    {G : Type*} [Group G] {H : Subgroup G}
    {a b c d : G} (heq : a = b * c * d)
    (ha : a ∈ H) (hb : b ∈ H) (hd : d ∈ H) : c ∈ H := by
  have heqc : c = b⁻¹ * a * d⁻¹ := by rw [heq]; group
  rw [heqc]
  exact H.mul_mem (H.mul_mem (H.inv_mem hb) ha) (H.inv_mem hd)

set_option maxHeartbeats 800000 in
/-- A simple root subgroup cannot lie in a normal unipotent subgroup. -/
public theorem rootSubgroup_le_normal_unipotent_false
    (U : ClosedSubgroup (Carrier (k := k)))
    (hUnormal : U.toSubgroup.Normal)
    (hUunipotent : @IsUnipotentAlgebraicGroup k _ U.carrierVariety
      U.carrierAlgebraicGroup)
    (i : Fin 2)
    (hroot : rootSubgroup (k := k) (simpleRoot i) ≤ U) : False := by
  letI : AlgebraicGroup (splitTorus (k := k)).carrierVariety :=
    (splitTorus (k := k)).carrierAlgebraicGroup
  obtain ⟨u, hu⟩ := exists_unit_zpow_ne_one (k := k) (z := (1 : ℤ)) (by norm_num)
  have hu0 : (u : k) ≠ 0 := Units.ne_zero u
  have hu1 : u ≠ 1 := by
    intro h
    apply hu
    simpa [h]
  have hplus (a : k) :
      (rootMorphism (k := k) (simpleRoot i)).onPoints (kPlusPoint a) ∈ U.toSubgroup := by
    apply hroot
    change (rootMorphism (k := k) (simpleRoot i)).onPoints (kPlusPoint a) ∈
      (rootMorphism (k := k) (simpleRoot i)).image
    exact ⟨kPlusPoint a, rfl⟩
  have hminus (b : k) :
      (rootMorphism (k := k) (-simpleRoot i)).onPoints (kPlusPoint b) ∈ U.toSubgroup := by
    obtain ⟨c, hc⟩ := carrierLongestWeyl_root_conjugation_exists
      (k := k) (-simpleRoot i) b
    have hc' : carrierWeylWord (k := k) (canonicalWeylWord 11) *
          (rootMorphism (k := k) (-simpleRoot i)).onPoints (kPlusPoint b) *
          (carrierWeylWord (k := k) (canonicalWeylWord 11))⁻¹ =
        (rootMorphism (k := k) (simpleRoot i)).onPoints (kPlusPoint c) := by
      simpa only [Root.neg_neg] using hc
    have hxc := hplus c
    have hconj := hUnormal.conj_mem
      ((rootMorphism (k := k) (simpleRoot i)).onPoints (kPlusPoint c)) hxc
      (carrierWeylWord (k := k) (canonicalWeylWord 11))⁻¹
    rw [← hc'] at hconj
    simpa [mul_assoc] using hconj
  have hprod := carrier_oppositeRootProduct_nonsingular
    (k := k) (simpleRoot i) 1 (1 - (u : k)) (by simpa using hu0)
  let c0 : kˣ := Units.mk0 (1 - 1 * (1 - (u : k))) (by simpa using hu0)
  have hc0 : c0 = u := by
    apply Units.ext_iff.mpr
    dsimp [c0]
    ring
  have hprodU :
      (rootMorphism (k := k) (simpleRoot i)).onPoints (kPlusPoint 1) *
          (rootMorphism (k := k) (-simpleRoot i)).onPoints
            (kPlusPoint (1 - (u : k))) ∈ U.toSubgroup :=
    U.toSubgroup.mul_mem (hplus 1) (hminus _)
  have hcorootC : rootCorootTorusFactor (k := k) (simpleRoot i) c0⁻¹ ∈ U.toSubgroup := by
    have hprod' :
            (rootMorphism (k := k) (simpleRoot i)).onPoints (kPlusPoint 1) *
            (rootMorphism (k := k) (-simpleRoot i)).onPoints
              (kPlusPoint (1 - (u : k))) =
          (rootMorphism (k := k) (-simpleRoot i)).onPoints
              (kPlusPoint ((1 - (u : k)) * (c0⁻¹ : kˣ))) *
            rootCorootTorusFactor (k := k) (simpleRoot i) c0⁻¹ *
            (rootMorphism (k := k) (simpleRoot i)).onPoints
              (kPlusPoint (1 * (c0⁻¹ : kˣ))) := by
      dsimp [c0]
      exact hprod
    apply middle_mem_of_factorization hprod'
    · exact hprodU
    · exact hminus _
    · exact hplus _
  have hcoroot : rootCorootTorusFactor (k := k) (simpleRoot i) u⁻¹ ∈ U.toSubgroup := by
    simpa [hc0] using hcorootC
  have hinter :
      rootCorootTorusFactor (k := k) (simpleRoot i) u⁻¹ ∈
        (splitTorus (k := k)).toSubgroup ⊓ U.toSubgroup := by
    exact ⟨by
      change _ ∈ (splitTorus (k := k)).toSubgroup
      exact ⟨rootCorootTorusPoint (k := k) (simpleRoot i) u⁻¹, rfl⟩,
      hcoroot⟩
  have hbot := subtorus_inf_unipotent_eq_bot
      (splitTorus (k := k)) U (splitTorus_isSubtorus (k := k)) hUunipotent
  have hone : rootCorootTorusFactor (k := k) (simpleRoot i) u⁻¹ = 1 := by
    rw [hbot] at hinter
    exact Subgroup.mem_bot.mp hinter
  exact rootCorootTorusFactor_ne_one i u⁻¹ (by
    intro h
    exact hu1 (inv_eq_one.mp h)) hone

end Theory.AlgebraicGroup.G2Chevalley
