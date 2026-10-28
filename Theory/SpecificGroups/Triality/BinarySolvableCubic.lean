module
public import Theory.SpecificGroups.Triality.BinarySolvableEscape
public import Theory.SpecificGroups.Triality.ConcreteBruhat.FixedCellCount
public import Theory.GroupTheory.Hall.PermutingCubic
import all Theory.SpecificGroups.Triality.BinaryThreeFreeSylow

/-!
# An escaping cubic in the actual binary-triality actor

The literal solvable actor intersection has central local factor or full
central parabolic as its image under the supplied marking. Its order is
therefore divisible by three. Hall restriction to this same intersection
produces an actual cubic inside the original odd actor and the layer.
The intersection of the arms and central parabolics is the Borel, whose
order is prime to three, so this cubic cannot normalize the arms parabolic.

The marking, odd actor, and original containing subgroup are retained.
The internal import reuses the central local-factor order calculation in
the same binary-triality proof family without exposing its private helper.
Source: Aschbacher--Smith 5.1.13, printed p.636; GLS3 §§2.3--2.6.
The original quotient lift is in RankOneModuleGenericExceptionalCartanLocalBinaryCentral.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace Triality.Standard.BinarySolvableEscape
open Parabolics
local notation "P" => binaryParameters 1 Nat.zero_lt_one
local notation "M" => BinaryCarrier 1 Nat.zero_lt_one

/-- Every actual cubic in the central parabolic moves the arms parabolic. -/
theorem cubic_not_normalizes_arms (D : Subgroup M) (hc : Nat.card D = 3)
    (hD : D ≤ parabolic P .central) : ¬ D ≤ normalizer (parabolic P .arms : Set M) := by
  intro hn
  rw [normalizer_parabolic_binary P rfl .arms] at hn
  have hb : D ≤ borel P := by
    rw [←parabolic_inf_binary P rfl]
    exact le_inf hn hD
  have hd := card_dvd_of_le hb
  rw [hc,ConcreteBruhat.FixedCellCount.card_borel] at hd
  norm_num [binaryParameters_q] at hd

/-- The actual odd actor contains a cubic in the same layer moving its
marked arms parabolic. No independent cubic witness is assumed. -/
theorem marked_actor_cubic {G : Type*} [Group G] [Finite G]
    (C R A : Subgroup G) [C.Normal] (S : Sylow 2 G) (e : C ≃* M)
    (hRC : R ≤ C)
    (hR : (R.subgroupOf C).map e.toMonoidHom = parabolic P .arms)
    (ho : Odd (Nat.card A))
    (hperm : (A : Set G) * (S : Set G) = (S : Set G) * (A : Set G))
    (hcases : (((A ⊔ (S : Subgroup G)).subgroupOf C).map e.toMonoidHom = localFactor P .central ∨
      ((A ⊔ (S : Subgroup G)).subgroupOf C).map e.toMonoidHom = parabolic P .central)) :
    ∃ D : Subgroup G, D ≤ A ∧ D ≤ C ∧ Nat.card D = 3 ∧
      ¬ D ≤ normalizer (R : Set G) := by
  let J := A ⊔ (S : Subgroup G)
  let I := J ⊓ C
  let X := (J.subgroupOf C).map e.toMonoidHom
  change X = localFactor P .central ∨ X = parabolic P .central at hcases
  have hLX : localFactor P .central ≤ X := by
    rcases hcases with he | he
    · exact he.symm ▸ le_rfl
    · exact he.symm ▸ localFactor_le_parabolic P .central
  have hXP : X ≤ parabolic P .central := by
    rcases hcases with he | he
    · exact he.symm ▸ localFactor_le_parabolic P .central
    · exact he.symm ▸ le_rfl
  have hcard : Nat.card I = Nat.card X := by
    rw [card_map_of_injective e.injective,←inf_subgroupOf_right J C]
    exact (Nat.card_congr (subgroupOfEquivOfLe (show I ≤ C from inf_le_right)).toEquiv).symm
  have hthree : 3 ∣ Nat.card I := by
    rw [hcard]
    have hd := card_dvd_of_le hLX
    rw [BinaryThreeFreeSylow.central_local_card] at hd
    exact (by decide : 3 ∣ 12288).trans hd
  obtain ⟨D,hDA,hDC,hDc⟩ := OddHall.exists_cubic_in_intersection A S C ho S.isPGroup' hperm
    (by rw [normalizer_eq_top]; exact le_top) hthree
  refine ⟨D,hDA,hDC,hDc,?_⟩
  let E := (D.subgroupOf C).map e.toMonoidHom
  have hEc : Nat.card E = 3 := by
    rw [card_map_of_injective e.injective,
      Nat.card_congr (subgroupOfEquivOfLe hDC).toEquiv,hDc]
  have hEP : E ≤ parabolic P .central :=
    (map_mono (comap_mono (hDA.trans (show A ≤ J from le_sup_left)))).trans hXP
  intro hn
  have hh : D.subgroupOf C ≤ normalizer (R.subgroupOf C : Set C) := by
    rw [←subgroupOf_normalizer_eq hRC]
    exact comap_mono hn
  have hh' := map_mono (f := e.toMonoidHom) hh
  rw [map_equiv_normalizer_eq,hR] at hh'
  exact cubic_not_normalizes_arms E hEc hEP hh'

end Triality.Standard.BinarySolvableEscape
