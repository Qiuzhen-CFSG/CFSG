module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPoint
public import Theory.Representation.HexacodeAction.EvenOrbitWeights

/-!
# The original even-orbit point is a full-weight scalar plane

The original quotient chart identifies the entire K-conjugacy orbit with
the even hexacode orbit. Orbit-stabilizer therefore transfers the actual
relative centralizer index, including its parity. The computed weight-orbit
theorem then marks the same field line and its literal inverse image Vt.

This supplies the full-weight point in 12.7.4. The A5 vector stabilizer,
natural quotient action and nonsplit extension remain separate calculations.
Source: Aschbacher--Smith, combined manuscript of 1 March 2004, 12.7.4(1–2),
printed pp.839–840.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

private theorem chart_conjugate (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (k : K) (v : U) :
    ((tripleSixPointCoordinates D a).symm (Multiplicative.ofAdd
      (Hexacode.evenAction (a.groupEquiv (QuotientGroup.mk' (pCore 2 K) k))
        ((tripleSixPointCoordinates D a v).toAdd))) : G) =
      (k : G) * (v : G) * (k : G)⁻¹ := by
  let w : D.space := (D.spaceEquiv.symm v).toAdd
  have he := a.intertwines (QuotientGroup.mk' (pCore 2 K) k) w
  change (D.spaceEquiv (Multiplicative.ofAdd (a.linearEquiv.symm
    (Hexacode.evenAction (a.groupEquiv (QuotientGroup.mk' (pCore 2 K) k))
      (a.linearEquiv w)))) : G) = _
  rw [← he, a.linearEquiv.symm_apply_apply, D.spaceEquiv_apply]
  have hw : (w.val.toMul.val : G) = (v : G) :=
    (D.spaceEquiv_apply w).symm.trans
      (congrArg (fun z : U => (z : G)) (D.spaceEquiv.apply_symm_apply v))
  change (k : G) * (w.val.toMul.val : G) * (k : G)⁻¹ = _
  rw [hw]

/-- The chart preserves the full original K-orbit cardinality, expressed as
the index of the actual point centralizer. -/
theorem tripleSixPoint_orbit_card (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) :
    (Set.range fun g : Atlas.Codes.HexEvenAutomorphisms =>
      Hexacode.evenAction g (tripleSixPointCoordinates D a t).toAdd).ncard =
        (centralizer ({(t : G)} : Set G)).relIndex K := by
  let f := tripleSixPointCoordinates D a
  let w := (f t).toAdd
  let j : Atlas.Codes.hexacode → G := fun v => f.symm (Multiplicative.ofAdd v)
  have hj : Function.Injective j := by
    intro v v' he
    exact Multiplicative.ofAdd.injective (f.symm.injective (Subtype.ext he))
  have himage : j '' (Set.range fun g : Atlas.Codes.HexEvenAutomorphisms =>
      Hexacode.evenAction g w) = conjugacyOrbit K (t : G) := by
    ext v
    constructor
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective (pCore 2 K) (a.groupEquiv.symm g)
      refine ⟨k, ?_⟩
      have he := chart_conjugate D a k t
      rw [hk, a.groupEquiv.apply_symm_apply] at he
      exact he.symm
    · rintro ⟨k, rfl⟩
      refine ⟨Hexacode.evenAction (a.groupEquiv (QuotientGroup.mk' (pCore 2 K) k)) w,
        ⟨a.groupEquiv (QuotientGroup.mk' (pCore 2 K) k), rfl⟩, ?_⟩
      exact chart_conjugate D a k t
  have hc : (Set.range fun g : Atlas.Codes.HexEvenAutomorphisms =>
      Hexacode.evenAction g w).ncard = (conjugacyOrbit K (t : G)).ncard := by
    rw [← himage, Set.ncard_image_of_injective _ hj]
  refine hc.trans ?_
  let : MulAction K G := MulAction.compHom G (MulAut.conj.comp K.subtype)
  have hs : MulAction.stabilizer K (t : G) =
      (centralizer ({(t : G)} : Set G)).subgroupOf K := by
    ext k
    change (k : G) * (t : G) * (k : G)⁻¹ = t ↔
      (k : G) ∈ centralizer ({(t : G)} : Set G)
    rw [mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
  exact (MulAction.index_stabilizer K (t : G)).symm.trans (congrArg Subgroup.index hs)

/-- The original even relative index marks this exact chart's field line
as one of the six full-weight scalar planes. -/
theorem tripleSixPoint_full_weight (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K) :
    Hexacode.IsFullWeightScalarPlane
      ((Submodule.span Hexacode.F {(tripleSixPointCoordinates D a t).toAdd}).restrictScalars
        (ZMod 2)) := by
  apply Hexacode.evenAction_full_weight_point_of_even_orbit
  · intro h
    have hh : tripleSixPointCoordinates D a t = 1 := h
    exact ht ((tripleSixPointCoordinates D a).injective
      (hh.trans (tripleSixPointCoordinates D a).map_one.symm))
  · rwa [tripleSixPoint_orbit_card D a t]

/-- The literal row and the original even-orbit point give a common chart,
its full-weight field line and the same actual central four-group Vt. -/
theorem original_tripleSix_full_point (D : ChosenModule T K U)
    (eK : (K ⧸ pCore 2 K) ≃* Atlas.Codes.HexEvenAutomorphisms)
    (hd : Module.finrank (ZMod 2) D.space = 6)
    (hf : Function.Injective D.quotientAction) (hi : IsIrreducible D.quotientAction)
    (t : G) (htU : t ∈ U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({t} : Set G)).relIndex K) :
    ∃ a : ActionEquiv D.quotientAction Hexacode.evenAction,
      Hexacode.IsFullWeightScalarPlane
        ((Submodule.span Hexacode.F {(tripleSixPointCoordinates D a ⟨t, htU⟩).toAdd}).restrictScalars
          (ZMod 2)) ∧
      t ∈ tripleSixPoint D a ⟨t, htU⟩ ∧ tripleSixPoint D a ⟨t, htU⟩ ≤ U ∧
      Nat.card (tripleSixPoint D a ⟨t, htU⟩) = 4 ∧
      IsElementaryAbelian 2 (tripleSixPoint D a ⟨t, htU⟩) ∧
      K ⊓ centralizer ({t} : Set G) ≤ centralizer (tripleSixPoint D a ⟨t, htU⟩ : Set G) := by
  obtain ⟨a⟩ := original_tripleSix_coordinates D eK hd hf hi
  have ht' : (⟨t, htU⟩ : U) ≠ 1 := fun h => ht (congrArg Subtype.val h)
  exact ⟨a, tripleSixPoint_full_weight D a ⟨t, htU⟩ ht' heven,
    tripleSixPoint_properties D a ⟨t, htU⟩ ht'⟩

end CFSG.Quasithin.Chapter12.Section07
