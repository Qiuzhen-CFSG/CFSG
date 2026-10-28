module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.J2Local
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.InnerInvolutionCores.Fusion
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.SecondParabolic.SylowCenter
public import Theory.GroupTheory.DoubleCoverCentralizer.TwoCentralSylow
public import Theory.GroupTheory.PerfectCentralSupplement

/-!
# Global non-two-central lifting in the original J₂ cover

The local centralizer has odd index 315, so central transfer supplies its
restriction premise. The non-two-central representative acts nontrivially
on the five-block quotient and lies outside its two-core. The proved local
involution exclusion therefore forces its lifts to have order four.
Exhaustive involution fusion transports this through the original cover map.

Source: Aschbacher–Smith I.2.2(5b), printed pp.411–412; the actual consumer
is the J₂ branch of 2.5.19, printed p.562.
-/

public section
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.J2Local
open Subgroup Theory.GroupTheory.DoubleCoverCentralizer
open Sporadic.LeechRelated.J2 GeneratorPair ExceptionalParabolics
open Seed FirstParabolic FirstParabolic.QuotientActions
variable {K : Type*} [Group K] [Finite K] [Group.IsPerfect K]

private def aLocal : l₁ := ⟨a, FirstFusion.a_mem_centralizer⟩

private theorem aLocal_not_core : aLocal ∉ pCore 2 l₁ := by
  intro h
  have hk : aLocal ∈ innerAction.ker := by
    rwa [innerAction_ker card_radical, ← l₁_core_eq]
  have ha := innerAction_spec aLocal (basePoint 0)
  rw [MonoidHom.mem_ker.mp hk] at ha
  have hc := letter_color_check 0 (basePoint 0)
  rw [FirstFusion.LocalCertificate.localLetterValue_eq] at hc
  change color (inclusion a (basePoint 0)) = some 4 at hc
  change color (inclusion a (basePoint 0)) = some 0 at ha
  have hn : (some (4 : Fin 5) : Option (Fin 5)) ≠ some 0 := by decide
  exact hn (hc.symm.trans ha)

private theorem z_twoCentral : TwoCentral FirstFusion.t := by
  have hz : FirstFusion.t ∈ (center s).map s.subtype := by
    rw [SecondParabolic.center_s]
    exact mem_zpowers _
  obtain ⟨u, _, he⟩ := hz
  let P : Sylow 2 Carrier := SecondParabolic.sylow card_l₁
  have hP : (P : Subgroup Carrier) = s := SecondParabolic.sylow_coe card_l₁
  have htP : FirstFusion.t ∈ P := by
    change FirstFusion.t ∈ (P : Subgroup Carrier)
    rw [hP]
    exact he ▸ u.property
  refine ⟨P, htP, mem_center_iff.mpr ?_⟩
  intro x
  apply Subtype.ext
  exact mem_centralizer_singleton_iff.mp (SecondParabolic.s_le_l₁ (hP ▸ x.property))

private theorem source_restriction
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2) :
    center K ≤ ⁅preimage e, preimage e⁆ := by
  apply central_pSubgroup_le_commutator (preimage e) (center K)
    (center_le_preimage e) le_rfl (IsPGroup.of_card (p := 2) (n := 1) (by simpa using hZ))
  rw [preimage, index_comap_of_surjective l₁ (projection_surjective e),
    SecondParabolic.l₁_index]
  decide

private theorem order_four_of_projection_eq_a
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2)
    (u : K) (hu : projection e u = a) : orderOf u = 4 := by
  let x : preimage e := ⟨u, by
    change projection e u ∈ l₁
    rw [hu]
    exact aLocal.property⟩
  have hxnot : x ∉ pCore 2 (preimage e) := by
    intro hx
    have hx' : restriction e x ∈ pCore 2 l₁ := by
      change x ∈ (pCore 2 l₁).comap (restriction e)
      rwa [core_preimage e hZ]
    have he : restriction e x = aLocal := Subtype.ext hu
    exact aLocal_not_core (he ▸ hx')
  have hnot2 : u ^ 2 ≠ 1 := by
    intro hs
    have hu1 : u ≠ 1 := by
      intro h
      have ha1 : a = 1 := by rw [← hu, h, map_one]
      have hlocal : aLocal = 1 := Subtype.ext ha1
      apply aLocal_not_core
      rw [hlocal]
      exact (pCore 2 l₁).one_mem
    have ho : orderOf x = 2 :=
      (orderOf_injective (preimage e).subtype (preimage e).subtype_injective x).symm.trans
        (orderOf_eq_prime hs hu1)
    exact hxnot ((commutator_quotient_of_restriction e hZ (source_restriction e hZ)).2 x ho)
  have hsZ : u ^ 2 ∈ center K := by
    rw [← projection_ker e, MonoidHom.mem_ker, map_pow, hu, a_pow_two]
  have hs4 : u ^ 4 = 1 := by
    have h := pow_card_eq_one' (x := (⟨u ^ 2, hsZ⟩ : center K))
    rw [hZ] at h
    simpa only [coe_pow, coe_one, ← pow_mul] using congrArg Subtype.val h
  obtain ⟨n, hn, ho⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show orderOf u ∣ 2 ^ 2 from orderOf_dvd_of_pow_eq_one hs4)
  interval_cases n
  · have hu1 : u = 1 := orderOf_eq_one_iff.mp ho
    exact (hnot2 (by rw [hu1, one_pow])).elim
  · exact (hnot2 (by simpa only [ho, pow_one] using pow_orderOf_eq_one u)).elim
  · exact ho

/-- Every lift of a non-two-central quotient involution has order four,
with the original canonical central quotient retained. -/
theorem nonTwoCentral_lift_order_four
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2)
    (u : K) (hu : orderOf (QuotientGroup.mk' (center K) u) = 2)
    (hc : ¬ TwoCentral (QuotientGroup.mk' (center K) u)) : orderOf u = 4 := by
  have hu' : orderOf (projection e u) = 2 := (e.orderOf_eq _).trans hu
  have hc' : ¬ TwoCentral (projection e u) := by
    intro h
    apply hc
    simpa only [projection, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply] using h.map e.symm
  rcases InnerInvolutionCores.involution_fusion (projection e u) hu' with ha | hz
  · obtain ⟨g, hg⟩ := isConj_iff.mp ha
    obtain ⟨k, hk⟩ := projection_surjective e g
    have hv : projection e ((MulAut.conj (k⁻¹)) u) = a := by
      change projection e (k⁻¹ * u * (k⁻¹)⁻¹) = a
      simp only [map_mul, map_inv, inv_inv, hk]
      rw [← hg]
      group
    exact ((MulAut.conj (k⁻¹)).orderOf_eq u).symm.trans
      (order_four_of_projection_eq_a e hZ _ hv)
  · obtain ⟨g, hg⟩ := isConj_iff.mp hz
    exact (hc' (hg ▸ z_twoCentral.map (MulAut.conj g))).elim

/-- I.2.2(5b)'s global lifting clause for the supplied perfect J₂ double cover.
No multiplier table or separate local restriction premise is required. -/
theorem nonTwoCentral_involution_lifting
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2) :
    NonTwoCentralInvolutionLifting K := by
  intro x hx hc
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (center K) x
  exact ⟨u, rfl, nonTwoCentral_lift_order_four e hZ u hx hc⟩

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.J2Local
