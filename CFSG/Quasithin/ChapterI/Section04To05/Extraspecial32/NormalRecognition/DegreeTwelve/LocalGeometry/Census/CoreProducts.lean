module
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.Census.LocalData
public import Theory.GroupTheory.CentralCommutatorQuotient
public import Theory.GroupTheory.PGroup.CyclicInvolution

/-!
# The four core products in the census at z

The commutator with `t` maps the elementary fusion eight to the central line
of the extraspecial core. It is nontrivial because that eight is its own
ambient centralizer and `t` lies outside it. Its kernel and complement both
have order four. A member of the eight has a product with `t` generating a
cyclic group containing `z` exactly when it is outside this kernel; the
identity and `z` lie in the kernel.

This proves the core contribution without a local orbit classification or
any count of outside-core involutions.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), 31–47, the four choices from `s^H` in the proof of Lemma 4.3.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.Census
open Subgroup
open scoped commutatorElement
variable {G : Type*} [Group G] [Finite G] {z t : G}

/-- Exactly four elements of the short core orbit satisfy the source's
cyclic-product condition for a second-class core involution. -/
public theorem core_products_card (h : Hypotheses z) (d : FusionEightData z)
    (htQ : t ∈ coreInG z) (ht : orderOf t = 2) (hnt : ¬ IsConj z t) :
    Nat.card (CoreProducts z t) = 4 := by
  classical
  let : IsExtraspecial 2 (coreInG z) := h.coreInG_extraspecial
  let : IsElementaryAbelian 2 (fusionCore z) := d.elementary
  have htF : t ∉ fusionCore z := fun hf =>
    hnt (d.fusion t hf (fun he => by simp [he] at ht))
  have hV : zpowers z ≤ centralizer (fusionCore z : Set G) := by
    rw [d.centralizer_eq]
    exact zpowers_le.mpr h.involution_mem_fusionCore
  have hr (x : G) (hx : x ∈ fusionCore z) : ⁅t, x⁆ ∈ zpowers z := by
    rw [← h.coreInG_center_image]
    have hmem : ⁅(⟨t, htQ⟩ : coreInG z), ⟨x, fusionCore_le z hx⟩⁆ ∈ center (coreInG z) :=
      (IsExtraspecial.quotient_elementary_abelian 2 (coreInG z)).commutator_le_center_of_central_quotient
        (commutator_mem_commutator (mem_top _) (mem_top _))
    exact mem_map_of_mem (coreInG z).subtype hmem
  let f := centralCommutatorHom (fusionCore z) (zpowers z) hV t hr
  have hf (x : fusionCore z) : (f x : G) = ⁅t, (x : G)⁆ := rfl
  have hk (x : fusionCore z) : x ∈ f.ker ↔ Commute t (x : G) := by
    change f x = 1 ↔ _
    rw [Subtype.ext_iff]
    exact commutatorElement_eq_one_iff_mul_comm
  have hn : f.range ≠ ⊥ := by
    intro he
    apply htF
    rw [← d.centralizer_eq]
    intro x hx
    have hx1 : f ⟨x, hx⟩ = 1 := mem_bot.mp (he ▸ (show f ⟨x, hx⟩ ∈ f.range from ⟨⟨x, hx⟩, rfl⟩))
    exact ((hk ⟨x, hx⟩).mp hx1).symm.eq
  have hZ : Nat.card (zpowers z) = 2 := (Nat.card_zpowers z).trans h.involution
  let : Fact (Nat.card (zpowers z)).Prime := ⟨by rw [hZ]; exact Nat.prime_two⟩
  have hrange : f.range = ⊤ := f.range.eq_bot_or_eq_top_of_prime_card.resolve_left hn
  have hrc : Nat.card f.range = 2 := by rw [hrange, card_top, hZ]
  have hkcard : Nat.card f.ker = 4 := by
    have hc := f.ker.card_mul_index
    rw [index_ker, hrc, d.card] at hc
    omega
  have hncard : Nat.card {x : fusionCore z // x ∉ f.ker} = 4 := by
    have hc := Nat.card_congr (Equiv.sumCompl (fun x : fusionCore z => x ∈ f.ker))
    rw [Nat.card_sum] at hc
    change Nat.card f.ker + Nat.card {x : fusionCore z // x ∉ f.ker} =
      Nat.card (fusionCore z) at hc
    rw [hkcard, d.card] at hc
    omega
  have hxp (x : fusionCore z) :
      (x : G) ≠ 1 ∧ (x : G) ≠ z ∧ z ∈ zpowers ((x : G) * t) ↔ x ∉ f.ker := by
    have hx2 : (x : G) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (x : G) x.property
    have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
    have hxi : (x : G)⁻¹ = x := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hx2)
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using ht2)
    constructor
    · rintro ⟨_, _, hcyc⟩ hker
      have hc := (hk x).mp hker
      have hp2 : ((x : G) * t) ^ 2 = 1 := by rw [hc.symm.mul_pow, hx2, ht2, one_mul]
      have hp1 : (x : G) * t ≠ 1 := by
        intro he
        apply htF
        have het : t = (x : G)⁻¹ := eq_inv_of_mul_eq_one_right he
        rw [het]
        exact (fusionCore z).inv_mem x.property
      have hpo : orderOf ((x : G) * t) = 2 := orderOf_eq_prime hp2 hp1
      have he : z = (x : G) * t := congrArg Subtype.val (IsCyclic.eq_of_orderOf_eq_two
        (x := (⟨z, hcyc⟩ : zpowers ((x : G) * t)))
        (y := ⟨(x : G) * t, mem_zpowers _⟩)
        ((Subgroup.orderOf_coe _).symm.trans h.involution)
        ((Subgroup.orderOf_coe _).symm.trans hpo))
      have het : t = (x : G)⁻¹ * z := by
        simpa only [inv_mul_cancel_left] using
          (congrArg (fun w : G => (x : G)⁻¹ * w) he).symm
      apply htF
      rw [het]
      exact (fusionCore z).mul_mem ((fusionCore z).inv_mem x.property)
        h.involution_mem_fusionCore
    · intro hker
      have hnc : ¬ Commute t (x : G) := fun hc => hker ((hk x).mpr hc)
      have hx1 : (x : G) ≠ 1 := fun he => hnc (he.symm ▸ Commute.one_right t)
      have hxz : (x : G) ≠ z := fun he =>
        hnc (he.symm ▸ (mem_centralizer_singleton_iff.mp (coreInG_le z htQ)))
      refine ⟨hx1, hxz, ?_⟩
      have hfo : orderOf (f x) = 2 := orderOf_eq_prime
        (by simpa only [hZ] using pow_card_eq_one' (x := f x)) hker
      have he : (f x : G) = z := congrArg Subtype.val (IsCyclic.eq_of_orderOf_eq_two
        hfo ((Subgroup.orderOf_coe (⟨z, mem_zpowers z⟩ : zpowers z)).symm.trans h.involution))
      have hcom : (f x : G) ∈ zpowers ((x : G) * t) := by
        rw [hf, commutatorElement_def, hti, hxi]
        have hi : t * (x : G) = ((x : G) * t)⁻¹ := by rw [mul_inv_rev, hti, hxi]
        have hm : t * (x : G) ∈ zpowers ((x : G) * t) := by
          rw [hi]
          exact inv_mem (mem_zpowers _)
        simpa only [pow_two, mul_assoc] using (pow_mem hm 2)
      exact (congrArg (fun w : G => w ∈ zpowers ((x : G) * t)) he).mp hcom
  let e : CoreProducts z t ≃ {x : fusionCore z // x ∉ f.ker} := {
    toFun x := ⟨⟨x, x.property.1⟩, (hxp ⟨x, x.property.1⟩).mp x.property.2⟩
    invFun x := ⟨x, x.val.property, (hxp x).mpr x.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  exact (Nat.card_congr e).trans hncard

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.Census
