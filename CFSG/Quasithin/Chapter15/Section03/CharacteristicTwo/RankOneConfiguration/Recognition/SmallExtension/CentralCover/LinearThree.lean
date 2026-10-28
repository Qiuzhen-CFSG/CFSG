module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.CentralCover.Bridge
public import Theory.Representation.SLHigherNaturalFirstCohomology.SLThreeBinary
public import Theory.Representation.GeneralLinearNatural
import Mathlib.Tactic.FinCases

/-!
# The binary linear-three extension calculation

The exceptional SL₃(2) cocycle has a nonzero spare coordinate at a
transvection, whereas all principal cocycles have zero there. Thus a cocycle
vanishing at that transvection is principal. A cubic rotation of the marked
plane, together with a transvection fixing the plane pointwise, has no common
fixed vector. Restriction to these two actual matrices therefore detects every
cocycle. The argument also handles two natural summands with the same marking.

This is the dual-cover calculation required in 15.3.31 for C.1.34(1)--(3).
It uses the checked I.1.6(4) normal form underlying B.4.8, not I.2.3, whose
list does not include L₃(2). The matrix marking must still be supplied by
the MS configuration's marked V₂-plane.

Source: Aschbacher--Smith, B.4.8(1),(3), I.1.5--6, and 15.3.31.
The spare-coordinate argument also appears in the checked private proof in
ChapterC/.../ModuleAlternatives/CentralAttachments/Involution.lean.
-/

@[expose] public section

open Matrix Matrix.SpecialLinearGroup Representation Representation.OneCohomology

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.CentralCover.LinearThree

abbrev SL := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)
abbrev Space := Fin 3 → ZMod 2
abbrev natural : Representation (ZMod 2) SL Space := specialLinearNatural 3

/-- A transvection with the marked coordinate plane as its axis. -/
def planeTransvection : SL := transvection (show (0 : Fin 3) ≠ 2 by decide) 1

/-- The cubic rotation on the marked plane spanned by coordinates zero and one. -/
def planeRotation : SL :=
  transvection (show (0 : Fin 3) ≠ 1 by decide) 1 *
    transvection (show (1 : Fin 3) ≠ 0 by decide) 1

/-- The B.4.8(3) extension calculation at the indicated involution, expressed
on the universal dual cover by its cocycle coordinates. -/
theorem principal_of_zero_at_planeTransvection (f : cocycles natural)
    (hf : f.val planeTransvection = 0) : ∃ v, principal natural v = f := by
  obtain ⟨a,v,hv⟩ := SLHigherNatural.SLThreeBinary.normal_form f
  have hex : SLHigherNatural.SLThreeBinary.exceptional.val planeTransvection 1 = 1 :=
    SLHigherNatural.SLThreeBinary.exceptional_spare 0 2 1 (by decide) (by decide) (by decide)
  have hp : (principal natural v).val planeTransvection 1 = 0 := by
    unfold planeTransvection
    rw [SLHigherNatural.principal_transvection]
    simp only [Pi.single_eq_of_ne (by decide : (1 : Fin 3) ≠ 0)]
  have ha : a = 0 := by
    have h := congrArg (fun c : cocycles natural => c.val planeTransvection 1) hv
    change f.val planeTransvection 1 =
      a * SLHigherNatural.SLThreeBinary.exceptional.val planeTransvection 1 +
        (principal natural v).val planeTransvection 1 at h
    rw [hf,hex,hp,mul_one,add_zero] at h
    exact h.symm
  exact ⟨v, by simpa only [ha,zero_smul,zero_add] using hv.symm⟩

/-- A fixed vector of this involution on the universal dual cover lies in
the original natural module, embedded by principal cocycles. -/
theorem universal_fixed_transvection_is_principal (f : cocycles natural)
    (hf : universalAction natural planeTransvection f = f) :
    ∃ v, principal natural v = f := by
  apply principal_of_zero_at_planeTransvection f
  apply principal_injective (SLHigherNatural.fixed_eq_bot (K := ZMod 2) (by decide : 2 ≤ 3))
  change f + principal natural (f.val planeTransvection) = f at hf
  simpa only [map_zero] using add_eq_left.mp hf

private theorem rotation_apply (v : Space) :
    natural planeRotation v = ![v 1, v 0 + v 1, v 2] := by
  rw [planeRotation, map_mul, Module.End.mul_apply]
  change specialLinearNatural 3 _ (specialLinearNatural 3 _ v) = _
  rw [SLHigherNatural.action_transvection, SLHigherNatural.action_transvection]
  ext i
  fin_cases i <;> simp <;> ring_nf
  simp only [show (2 : ZMod 2) = 0 by decide, mul_zero, zero_add]

/-- The actual marked plane rotation and radical transvection have no
common nonzero fixed vector on the natural module. -/
theorem fixed_marked_matrices_eq_zero (v : Space)
    (ht : natural planeTransvection v = v) (hr : natural planeRotation v = v) : v = 0 := by
  have ht0 := congrFun ht 0
  have hr0 := congrFun hr 0
  have hr1 := congrFun hr 1
  rw [rotation_apply] at hr0 hr1
  have hv10 : v 1 = v 0 := hr0
  have hv0 : v 0 = 0 := add_eq_right.mp hr1
  have hv1 : v 1 = 0 := hv10.trans hv0
  change specialLinearNatural 3 _ v 0 = v 0 at ht0
  rw [planeTransvection, SLHigherNatural.action_transvection] at ht0
  have hv2 : v 2 = 0 := by simpa [Pi.single_apply, hv0] using ht0
  ext i
  fin_cases i <;> assumption

/-- The complete cocycle restriction calculation for an actual subgroup
containing the two marked matrices. It detects the principal part as well. -/
theorem detectedOn_of_marked_matrices (B : Subgroup SL)
    (ht : planeTransvection ∈ B) (hr : planeRotation ∈ B) : DetectedOn natural B := by
  intro f hf
  obtain ⟨v,hv⟩ := principal_of_zero_at_planeTransvection f (hf _ ht)
  have hv0 : v = 0 := fixed_marked_matrices_eq_zero v
    (sub_eq_zero.mp (by
      have h := congrArg (fun c : cocycles natural => c.val planeTransvection) hv
      exact h.trans (hf _ ht)))
    (sub_eq_zero.mp (by
      have h := congrArg (fun c : cocycles natural => c.val planeRotation) hv
      exact h.trans (hf _ hr)))
  rw [← hv, hv0, map_zero]

/-- The doubled-natural case uses both copies with one common actor marking. -/
theorem detectedOn_two_natural (B : Subgroup SL)
    (ht : planeTransvection ∈ B) (hr : planeRotation ∈ B) :
    DetectedOn (natural.prod natural) B :=
  detectedOn_prod natural natural B (detectedOn_of_marked_matrices B ht hr)
    (detectedOn_of_marked_matrices B ht hr)

/-- Faithfulness is inherited from either natural coordinate. -/
theorem two_natural_injective : Function.Injective (natural.prod natural) := by
  intro a b h
  apply specialLinearNatural_injective 3
  apply LinearMap.ext
  intro v
  exact congrArg Prod.fst (LinearMap.congr_fun h (v,0))

variable {G : Type*} [Group G]

/-- The one-natural centralizing branch, once the genuine MS configuration
has supplied its coefficient model and the two indicated marked actors. -/
theorem centralizerImage_eq_bot_one_natural (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) [(actionKernel I c.L).Normal]
    (hYL : d.Yplus ≤ c.L) (hnormal : (c.L.subgroupOf I).Normal)
    (m : CenterModel c.L natural)
    (hDQ : yplusCentralizer d I ≤ Subgroup.centralizer (extensionCore c.L : Set G))
    (ht : planeTransvection ∈ (d.Yplus.subgroupOf c.L).map m.actorMap)
    (hr : planeRotation ∈ (d.Yplus.subgroupOf c.L).map m.actorMap) :
    plusImage I c.L (yplusCentralizer d I) = ⊥ :=
  centralizerImage_eq_bot_of_detected_model d c hYL hnormal m
    (specialLinearNatural_injective 3) hDQ (detectedOn_of_marked_matrices _ ht hr)

/-- The same conclusion for two natural summands. Both use the same actual
quotient isomorphism, so independently twisted coordinate markings are excluded. -/
theorem centralizerImage_eq_bot_two_natural (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) [(actionKernel I c.L).Normal]
    (hYL : d.Yplus ≤ c.L) (hnormal : (c.L.subgroupOf I).Normal)
    (m : CenterModel c.L (natural.prod natural))
    (hDQ : yplusCentralizer d I ≤ Subgroup.centralizer (extensionCore c.L : Set G))
    (ht : planeTransvection ∈ (d.Yplus.subgroupOf c.L).map m.actorMap)
    (hr : planeRotation ∈ (d.Yplus.subgroupOf c.L).map m.actorMap) :
    plusImage I c.L (yplusCentralizer d I) = ⊥ :=
  centralizerImage_eq_bot_of_detected_model d c hYL hnormal m
    two_natural_injective hDQ (detectedOn_two_natural _ ht hr)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.CentralCover.LinearThree
