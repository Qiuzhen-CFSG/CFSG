module

public import Theory.SpecificGroups.Tits.ConverseLocalCoverage
public import Theory.SpecificGroups.Tits.SharpOuterBound.Kernel
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.Orders
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Sylow centralizers of three-divisible actors in Tits

Every nontrivial normal subgroup of the marked Sylow two-group contains its
unique central involution r5. Its centralizer has order prime to three, so a
Sylow-invariant subgroup of order divisible by three has trivial Sylow
centralizer. Moreover an automorphism fixing both the Sylow group and such an
actor is trivial: the certified restriction calculation makes it fix the first
reflection, and Sylow-overgroup coverage then makes its fixed subgroup all of
Tits. These statements concern the full automorphism group.

Source: Parrott (1972), §5, p.683; the intrinsic calculations used in
Aschbacher--Smith 15.3.43, printed p.1140.
-/

public section
namespace Tits.SylowActorCentralizer
open Subgroup ExceptionalParabolics OuterOddSubgroups

private theorem r5_mem_of_normalized (W : Subgroup Atlas1600Group)
    (hle : W ≤ S) (hne : W ≠ ⊥) (hn : S ≤ normalizer (W : Set Atlas1600Group)) :
    atlas1600R5 ∈ W := by
  let N := W.subgroupOf S
  have hN : N ≠ ⊥ := by
    intro h
    apply hne
    have hm := congrArg (fun A : Subgroup S => A.map S.subtype) h
    simpa only [N, map_subgroupOf_eq_of_le hle, Subgroup.map_bot] using hm
  let : N.Normal := normal_subgroupOf_of_le_normalizer hn
  let : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hN
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  let : Fact (IsPGroup 2 S) := ⟨IsPGroup.of_card (n := 11)
    (by norm_num [sylow_card])⟩
  obtain ⟨w, hw, hwc⟩ := exists_nontrivial_center_mem_normal (p := 2) N
  rcases (atlas1600SylowTwo_mem_center_iff w.val).mp hwc with he | he
  · exact (hw (Subtype.ext (Subtype.ext he))).elim
  · exact he ▸ w.property

/-- A Sylow-invariant three-divisible subgroup has trivial Sylow centralizer. -/
theorem sylow_inf_centralizer_eq_bot (Y : Subgroup Atlas1600Group)
    (hn : S ≤ normalizer (Y : Set Atlas1600Group)) (hthree : 3 ∣ Nat.card Y) :
    S ⊓ centralizer (Y : Set Atlas1600Group) = ⊥ := by
  by_contra hne
  have hnorm : S ≤ normalizer ((S ⊓ centralizer (Y : Set Atlas1600Group)) :
      Set Atlas1600Group) :=
    (le_inf S.le_normalizer (hn.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  have hr := r5_mem_of_normalized _ inf_le_left hne hnorm
  have hY : Y ≤ first := by
    rw [RelativeParabolicNormalizers.first_eq_centralizer]
    intro y hy
    exact mem_centralizer_singleton_iff.mpr (hr.2 y hy)
  have hd := hthree.trans (card_dvd_of_le hY)
  rw [ReeLocalBlockOrders.first_card] at hd
  norm_num at hd

/-- Fixing the marked Sylow subgroup and a three-divisible subgroup pointwise
forces a full Tits automorphism to be the identity. -/
theorem eq_one_of_fixes_sylow_and_actor (Y : Subgroup Atlas1600Group)
    (hthree : 3 ∣ Nat.card Y) (a : MulAut Atlas1600Group)
    (hS : ∀ x ∈ S, a x = x) (hY : ∀ x ∈ Y, a x = x) : a = 1 := by
  have hmap : S.map a.toMonoidHom = S := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      change a x ∈ S
      rw [hS x hx]
      exact hx
    · intro x hx
      exact mem_map.mpr ⟨x, hx, hS x hx⟩
  let b : sylowStabilizer := ⟨a, hmap⟩
  let k : sylowRestriction.ker := ⟨b, (mem_sylowRestriction_ker_iff b).mpr hS⟩
  let F := a.toMonoidHom.eqLocus (MonoidHom.id Atlas1600Group)
  have hSF : S ≤ F := hS
  have hfirst : first ≤ F := sup_le hSF ((closure_le _).mpr (by
    rintro x (rfl : x = atlas1600ParrottAssignment .r1)
    exact SharpOuterBound.kernel_fixes_first_reflection k))
  have hF : F = ⊤ := by
    by_contra hproper
    rcases ConverseLocalCoverage.le_first_or_second F hproper hSF with hf | hs
    · have hd := hthree.trans (card_dvd_of_le ((show Y ≤ F from hY).trans hf))
      rw [ReeLocalBlockOrders.first_card] at hd
      norm_num at hd
    · have hd := card_dvd_of_le (hfirst.trans hs)
      rw [ReeLocalBlockOrders.first_card, second_card] at hd
      norm_num at hd
  apply MulEquiv.ext
  intro x
  exact hF.ge (mem_top x)

end Tits.SylowActorCentralizer
