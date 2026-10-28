module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixContainedSetup
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointCentralizer
public import CFSG.Quasithin.ChapterE.Section03.ZeroClosure

/-!
# Hyperplane centralizers in the original contained branch

Every full-weight vector is K-conjugate to the original t, so the contained
centralizer hypothesis controls all their centralizers. Every hyperplane
of U meets the literal field line Vt nontrivially. Its centralizer is
therefore contained in N_G(K), and E.6.1 puts it in N_G(U). Consequently
the original global corank parameter exceeds one.

Source: Aschbacher–Smith, 12.7.10(2), printed p.843.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource Atlas.Codes
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- Containment transfers to every full-weight vector in the actual chart. -/
theorem original_tripleSix_full_weight_centralizer_le
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (contained : centralizer ({(t : G)} : Set G) ≤ normalizer (K : Set G))
    (u : U) (hu : hammingNorm (tripleSixPointCoordinates D a u).toAdd.val = 6) :
    centralizer ({(u : G)} : Set G) ≤ normalizer (K : Set G) := by
  let c := tripleSixPointCoordinates D a
  have ht0 : (c t).toAdd ≠ 0 := by
    intro hz
    exact ht (c.injective (show c t = c 1 from hz.trans c.map_one.symm))
  have htweight := Hexacode.evenAction_full_weight_of_even_orbit (c t).toAdd ht0
    (by rwa [tripleSixPoint_orbit_card D a t])
  have horbit : (c u).toAdd ∈ Set.range (fun g : HexEvenAutomorphisms =>
      Hexacode.evenAction g (c t).toAdd) := by
    rw [Hexacode.evenAction_orbit_eq_weight _ ht0]
    exact hu.trans htweight.symm
  obtain ⟨g, hg⟩ := horbit
  change Hexacode.evenAction g (tripleSixPointCoordinates D a t).toAdd =
    (tripleSixPointCoordinates D a u).toAdd at hg
  obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective (pCore 2 K) (a.groupEquiv.symm g)
  have hku : (k : G) * (t : G) * (k : G)⁻¹ = u := by
    have hh := tripleSixPointCoordinates_conjugate D a k t
    rw [hk, a.groupEquiv.apply_symm_apply, hg] at hh
    change (c.symm (c u) : G) = _ at hh
    rw [c.symm_apply_apply] at hh
    exact hh.symm
  intro x hx
  have hx' : (k : G)⁻¹ * x * (k : G) ∈ centralizer ({(t : G)} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    have hc := mem_centralizer_singleton_iff.mp hx
    rw [← hku] at hc
    have hh := congrArg (fun z : G => (k : G)⁻¹ * z * (k : G)) hc
    simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left,
      mul_inv_cancel_right, inv_mul_cancel_right, inv_mul_cancel, mul_one] using hh
  have hkM := K.le_normalizer k.property
  have hh := (normalizer (K : Set G)).mul_mem
    ((normalizer (K : Set G)).mul_mem hkM (contained hx'))
    ((normalizer (K : Set G)).inv_mem hkM)
  simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel_right,
    mul_inv_cancel, mul_one] using hh

/-- Every original hyperplane has its full centralizer in N_G(U). -/
theorem original_tripleSix_hyperplane_centralizer_le
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (contained : centralizer ({(t : G)} : Set G) ≤ normalizer (K : Set G))
    (W : Subgroup G) (hWU : W ≤ U) (hcor : subgroupCorank U W = 1) :
    centralizer (W : Set G) ≤ normalizer (U : Set G) := by
  let := D.elementary
  let Vt := tripleSixPoint D a t
  have hp := tripleSixPoint_properties D a t ht
  have hindex : W.relIndex U = 2 := by
    rw [relIndex_eq_two_pow_quotient_finrank, ← subgroupCorank_eq_quotient_finrank, hcor]
    norm_num
  have hmeet : W ⊓ Vt ≠ ⊥ := by
    intro hz
    have hh := relIndex_le_of_le_right hp.2.1 (by omega : W.relIndex U ≠ 0)
    rw [← inf_relIndex_right W Vt, hz, relIndex_bot_left, hp.2.2.1, hindex] at hh
    omega
  obtain ⟨u, hu, hune⟩ := (W ⊓ Vt).bot_or_exists_ne_one.resolve_left hmeet
  obtain ⟨v, hv, hvu⟩ := hu.2
  have hvne : v ≠ 1 := by
    intro he
    exact hune (hvu.symm.trans (congrArg (fun z : U => (z : G)) he))
  have hP := tripleSixPoint_full_weight D a t ht heven
  have hw : hammingNorm (tripleSixPointCoordinates D a v).toAdd.val = 6 := by
    apply hP.2.2 ⟨_, hv⟩
    intro hz
    have he : tripleSixPointCoordinates D a v = 1 := congrArg Subtype.val hz
    exact hvne ((tripleSixPointCoordinates D a).injective
      (he.trans (tripleSixPointCoordinates D a).map_one.symm))
  have hC : centralizer (W : Set G) ≤ normalizer (K : Set G) :=
    (centralizer_le (Set.singleton_subset_iff.mpr hu.1)).trans (by
      rw [← hvu]
      exact original_tripleSix_full_weight_centralizer_le D a t ht heven contained v hw)
  have hWne : W ≠ ⊥ := by
    intro hz
    exact hune (mem_bot.mp (hz ▸ hu.1))
  exact ((original_chosen_hypothesisE61_at h structural D).centralizer_le_iff hWne hWU).mp hC

/-- The first strict bound in the original contained 12.7.10 argument. -/
theorem original_tripleSix_one_lt_globalR
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (contained : centralizer ({(t : G)} : Set G) ≤ normalizer (K : Set G)) :
    1 < globalR U := by
  let := D.elementary
  exact one_lt_globalR_of_hyperplane_centralizers U
    (original_tripleSix_hyperplane_centralizer_le h structural D a t ht heven contained)

end CFSG.Quasithin.Chapter12.Section07
