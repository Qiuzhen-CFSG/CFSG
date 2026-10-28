module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalBorel
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Fundamental
public import Theory.SpecificGroups.PSL3.LinearAmbientGeometry.AffineCentralizer

/-!
# Excluding an affine local factor from an original A₅ context

The chosen flag line contains a nonidentity element of the original
two-core. Its point centralizer has index five in the component, whose
two-core quotient is A₅, so that centralizer has order divisible by three.
In an affine SL₂ group every nonidentity core element has a two-group
centralizer. These literal centralizers exclude the affine local factor
without bounding the field or replacing the original module.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}

/-- The original A₅ flag has a point centralizer with an odd cubic divisor. -/
theorem original_point_centralizer_three_dvd
    (d : Context T L V V₁ V₂ V₃) :
    3 ∣ Nat.card (L ⊓ centralizer (V₁ : Set G) : Subgroup G) := by
  let C := L ⊓ centralizer (V₁ : Set G)
  have hcard := (C.subgroupOf L).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (show C ≤ L from inf_le_left)).toEquiv] at hcard
  change Nat.card C * C.relIndex L = Nat.card L at hcard
  rw [d.point_centralizer_relIndex] at hcard
  have hthree : 3 ∣ Nat.card L := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 L),
      Nat.card_congr d.quotient.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
    exact dvd_mul_of_dvd_left (by decide : 3 ∣ 60) _
  rw [←hcard] at hthree
  exact (Nat.Prime.dvd_mul (by decide : Nat.Prime 3)).mp hthree |>.resolve_right (by decide)

/-- An original A₅ component is never the native affine SL₂ local factor. -/
theorem original_context_not_affine_equiv
    (d : Context T L V V₁ V₂ V₃)
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    (e : L ≃* Matrix.SL2.Affine F) : False := by
  have hne : V₁ ≠ ⊥ := by
    intro he
    have hc := d.flag.one_card
    rw [he] at hc
    simp at hc
  obtain ⟨⟨z,hz⟩,hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hzQ : z ∈ L.pCoreIn 2 :=
    d.chosen.le_componentCore (d.flag.two_le_V (d.flag.one_le_two hz))
  have hp := Matrix.PSL3.LinearAmbientGeometry.affine_core_centralizer_isPGroup L e z hzQ
    (fun he => hz1 (Subtype.ext he))
  have hpC : IsPGroup 2 (L ⊓ centralizer (V₁ : Set G) : Subgroup G) :=
    hp.to_le (inf_le_inf_left L (centralizer_le (Set.singleton_subset_iff.mpr hz)))
  obtain ⟨n,hn⟩ := hpC.exists_card_eq
  have hd := original_point_centralizer_three_dvd d
  rw [hn] at hd
  exact (by decide : ¬ 3 ∣ 2) ((Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 3)) hd)

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
