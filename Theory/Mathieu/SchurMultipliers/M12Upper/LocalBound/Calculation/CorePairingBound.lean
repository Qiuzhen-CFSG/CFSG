module

public import Theory.Mathieu.SchurMultipliers.M12Upper.LocalBound.Calculation.CorePairingBound.Pairing
public import Theory.Mathieu.SchurMultipliers.M12Upper.LocalBound.Calculation.Reduction

/-!
# The kernel bound for the first M₁₂ core pairing

For the literal quaternion-core preimage in a central extension of the first
parabolic, the commutator pairing has just two generators `s,c`. The marked
commuting-lift relation identifies the two quaternion commutator coefficients.
Both generators square to one, while their images in M₁₂ are respectively
`z` and `1`. Thus only `1,c` can lie in the quotient kernel.

This proves `FirstParabolicCoreLiftBound` in every universe. Detection of the
full derived kernel inside this core-derived subgroup is a separate result;
no such detection, multiplier bound, or exponent assumption on the central
kernel is used here. The original two-group hypothesis is retained in the
public contract.

Source: the local upper-bound calculation for Aschbacher–Smith I.1.3(1),
printed p.407, with the embedded parabolic geometry of 14.2.21, printed p.988.
-/

open Subgroup
open scoped commutatorElement IsMulCommutative
namespace Sporadic.Mathieu.SchurMultipliers.M12Upper
open M12SmallPair CorePairingBound
universe u

/-- The marked commuting lifts bound the kernel in the derived core preimage. -/
public theorem firstParabolicCoreLiftBound : FirstParabolicCoreLiftBound.{u} := by
  intro D _ _ q hq hk _ hvt
  obtain ⟨B,hB,hi,hp,ha⟩ := exists_core_lift_pairing q hq hk
  have hm : B vv tt = 1 := by
    obtain ⟨a,b,ha,hb,hab⟩ := hvt
    apply Subtype.ext
    rw [hB vv tt a b ha hb]
    exact hab.commutator_eq
  have image (x y : core) : (q (B x y : D) : M12) = (⁅x,y⁆ : core) := by
    obtain ⟨a,hea⟩ := hq ⟨x, core_le_firstParabolic x.property⟩
    obtain ⟨b,heb⟩ := hq ⟨y, core_le_firstParabolic y.property⟩
    rw [hB x y a b (congrArg Subtype.val hea) (congrArg Subtype.val heb),
      map_commutatorElement, hea, heb]
    rfl
  let s : D := B li lj
  let c : D := B li rj
  have hs : s*s = 1 := by
    exact congrArg (fun a : center D => (a : D)) (show B li lj * B li lj = 1 by
      simpa only [pow_two] using hp li lj)
  have hc : c*c = 1 := by
    exact congrArg (fun a : center D => (a : D)) (show B li rj * B li rj = 1 by
      simpa only [pow_two] using hp li rj)
  have hsc : Commute s c := (mem_center_iff.mp (B li rj).property s)
  have hqs : (q s : M12) = z := (image li lj).trans (congrArg Subtype.val comm_li_lj)
  have hqc : (q c : M12) = 1 := (image li rj).trans (congrArg Subtype.val comm_li_rj)
  let N : Subgroup D := closure ({s,c} : Set D)
  have hvalues (x y : core) : (B x y : D) ∈ N := by
    have hle : closure {w : center D | ∃ x y : core, B x y = w} ≤
        N.comap (center D).subtype := by
      rw [pairing_span_eq B hp ha hi hm]
      apply (closure_le _).mpr
      rintro _ (rfl | rfl)
      · exact subset_closure (by simp [s])
      · exact subset_closure (by simp [c])
    exact hle (subset_closure ⟨x,y,rfl⟩)
  have hspan : ⁅corePreimage q,corePreimage q⁆ = N := by
    rw [core_lift_derived_eq_pairing_span q hq B hB]
    apply le_antisymm
    · apply (closure_le _).mpr
      rintro _ ⟨x,y,rfl⟩
      exact hvalues x y
    · apply (closure_le _).mpr
      rintro _ (rfl | rfl)
      · exact subset_closure ⟨li,lj,rfl⟩
      · exact subset_closure ⟨li,rj,rfl⟩
  have hle : q.ker ⊓ ⁅corePreimage q,corePreimage q⁆ ≤ zpowers c := by
    intro d hd
    have hqd : (q d : M12) = 1 := congrArg Subtype.val hd.1
    have hdN : d ∈ N := hspan ▸ hd.2
    rcases (mem_closure_pair_iff s c hs hc hsc d).mp hdN with h | h | h | h
    · rw [h]; exact (zpowers c).one_mem
    · have he : z = 1 := hqs.symm.trans (h ▸ hqd)
      exact (z_ne_one he).elim
    · rw [h]; exact mem_zpowers c
    · have he : z = 1 := by
        rw [h, map_mul] at hqd
        change (q s : M12) * (q c : M12) = 1 at hqd
        simpa only [hqs,hqc,mul_one] using hqd
      exact (z_ne_one he).elim
  exact (card_le_of_le hle).trans (by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by decide : 0 < 2)
      (orderOf_dvd_of_pow_eq_one (show c^2 = 1 by simpa only [pow_two] using hc)))

end Sporadic.Mathieu.SchurMultipliers.M12Upper
