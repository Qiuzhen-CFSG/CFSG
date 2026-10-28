module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.SymmetricLocal.ExchangedModel.JointCore
public import Theory.GroupAction.ExtraspecialInvolutionFixed
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Fixed-point obstruction to a single-factor residual

An involution on Uˣ fixes at least sixteen elements, by the general
extraspecial fixed-point bound. This subgroup lies in the common core D.
If an actor fixes at least sixteen elements of the elementary group D of
order 64, their intersection has order at least four. Consequently this
actor cannot have only the central involution fixed in Uˣ.

In the source, the actor is a cubic element of the original K₀. Its
sixteen fixed points in D must be supplied by the original marked A₅
module calculation. The finite matrix classification must still show
that a non-swapping involution with nonsolvable residual would give a
cubic actor with only the center fixed in Uˣ. Neither premise is asserted
here, and this file does not yet prove component interchange.

Source: Aschbacher–Smith, Lemma 14.4.9, printed p.1010.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal
variable {G : Type*} [Group G] [Finite G]

private theorem external_involution_fixed_card_bound
    (V : Subgroup G) [IsExtraspecial 2 V] (z : G)
    (hzV : z ∈ normalizer (V : Set G)) (hz : z ^ 2 = 1)
    (hVcard : Nat.card V = 512) :
    16 ≤ Nat.card (V ⊓ centralizer ({z} : Set G) : Subgroup G) := by
  let n : normalizer (V : Set G) := ⟨z,hzV⟩
  let a := V.normalizerMonoidHom n
  have ha : a ^ 2 = 1 := by
    have hn : n ^ 2 = 1 := Subtype.ext hz
    change (V.normalizerMonoidHom n) ^ 2 = 1
    rw [← map_pow, hn, map_one]
  have he : FixedPoints.subgroup (zpowers a) V =
      (centralizer ({z} : Set G)).subgroupOf V := by
    ext v
    constructor
    · intro hv
      have hh := congrArg Subtype.val (hv ⟨a,mem_zpowers a⟩)
      change z * (v : G) * z⁻¹ = (v : G) at hh
      exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro hv b
      have hh : a v = v := by
        apply Subtype.ext
        change z * (v : G) * z⁻¹ = (v : G)
        exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hv).symm
      exact smul_eq_self_of_mem_zpowers b.property hh
  have hbound := a.extraspecial_card_le_twice_fixed_card_sq ha
  rw [hVcard, he] at hbound
  have hc : Nat.card ((centralizer ({z} : Set G)).subgroupOf V) =
      Nat.card (V ⊓ centralizer ({z} : Set G) : Subgroup G) := by
    simpa only [inf_subgroupOf_left] using Nat.card_congr (subgroupOfEquivOfLe
      (show V ⊓ centralizer ({z} : Set G) ≤ V from inf_le_left)).toEquiv
  rw [hc] at hbound
  by_contra! hsmall
  nlinarith

theorem sixteen_le_exchanged_centralizer_card
    (U : Subgroup G) [IsExtraspecial 2 U] (z x : G)
    (hz : orderOf z = 2)
    (hUcore : (centralizer ({z} : Set G)).pCoreIn 2 = U)
    (hUcard : Nat.card U = 512)
    (hiz : conjugateElement z x ∈ centralizer ({z} : Set G)) :
    16 ≤ Nat.card (conjugateCore U x ⊓ centralizer ({z} : Set G) : Subgroup G) := by
  let V := conjugateCore U x
  let e := U.equivMapOfInjective (MulAut.conj x⁻¹).toMonoidHom
    (MulAut.conj x⁻¹).injective
  let : IsExtraspecial 2 V := IsExtraspecial.of_mulEquiv e inferInstance
  have hVcard : Nat.card V = 512 := (Nat.card_congr e.toEquiv).symm.trans hUcard
  have hVi : (centralizer ({conjugateElement z x} : Set G)).pCoreIn 2 = V :=
    conjugateCore_eq_core U z x hUcore
  have hzV : z ∈ normalizer (V : Set G) := by
    have hzC : z ∈ centralizer ({conjugateElement z x} : Set G) :=
      mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hiz).symm
    rw [← hVi]
    exact ((centralizer ({conjugateElement z x} : Set G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))) hzC
  exact external_involution_fixed_card_bound V z hzV (hz ▸ pow_orderOf_eq_one z) hVcard

private theorem four_le_intersection_card
    (D C F : Subgroup G) [IsMulCommutative D]
    (hD : Nat.card D = 64) (hCD : C ≤ D) (hFD : F ≤ D)
    (hC : 16 ≤ Nat.card C) (hF : 16 ≤ Nat.card F) :
    4 ≤ Nat.card (C ⊓ F : Subgroup G) := by
  have hnorm : F ≤ normalizer (C : Set G) :=
    ((hFD.trans D.le_centralizer).trans (centralizer_le hCD)).trans
      (centralizer_le_normalizer (C : Set G))
  have hcount := card_mul_eq_card_inf_mul_card_sup_of_normalizes C F hnorm
  have hsup : Nat.card (C ⊔ F : Subgroup G) ≤ 64 := hD ▸ card_le_of_le (sup_le hCD hFD)
  have hlower := Nat.mul_le_mul hC hF
  rw [hcount] at hlower
  have hupper := hlower.trans (Nat.mul_le_mul_left (Nat.card (C ⊓ F : Subgroup G)) hsup)
  omega

/-- An actor fixing at least sixteen points of D cannot act fixed-point-freely
on the central quotient of Uˣ. This is the fixed-point obstruction for the
single-factor residual in the component-preserving branch. -/
theorem four_le_exchanged_actor_centralizer_card
    (U : Subgroup G) [IsExtraspecial 2 U] (z x : G)
    (hz : orderOf z = 2)
    (hUcore : (centralizer ({z} : Set G)).pCoreIn 2 = U)
    (hUcard : Nat.card U = 512)
    (hiz : conjugateElement z x ∈ centralizer ({z} : Set G))
    (hD : IsElementaryAbelian 2 (centralizerLift U z (conjugateElement z x)))
    (hDcard : Nat.card (centralizerLift U z (conjugateElement z x)) = 64)
    (hDcore : (centralizer ({z} : Set G) ⊓
      centralizer ({conjugateElement z x} : Set G)).pCoreIn 2 =
        centralizerLift U z (conjugateElement z x))
    (r : G) (hfix : 16 ≤ Nat.card
      (centralizerLift U z (conjugateElement z x) ⊓ centralizer ({r} : Set G) : Subgroup G)) :
    4 ≤ Nat.card (conjugateCore U x ⊓ centralizer ({r} : Set G) : Subgroup G) := by
  let D := centralizerLift U z (conjugateElement z x)
  let C := conjugateCore U x ⊓ centralizer ({z} : Set G)
  let F := D ⊓ centralizer ({r} : Set G)
  let : IsElementaryAbelian 2 D := hD
  have hCD : C ≤ D := by
    change C ≤ centralizerLift U z (conjugateElement z x)
    rw [← hDcore]
    exact exchanged_centralizer_le_joint_core U z x hUcore
  have hfour := four_le_intersection_card D C F hDcard hCD inf_le_left
    (sixteen_le_exchanged_centralizer_card U z x hz hUcore hUcard hiz) hfix
  exact hfour.trans (card_le_of_le
    (show C ⊓ F ≤ conjugateCore U x ⊓ centralizer ({r} : Set G) from
      le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_right)))

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal
