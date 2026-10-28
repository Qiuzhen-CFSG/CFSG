module

public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts.LocalCalculations.Basic

/-!
# Replacing a faithful regular cyclic lift

Two faithful lifts of the same subgroup of Aut(V) are isomorphic through
that action image. This isomorphism intertwines actual conjugation on V,
so it preserves the displacement, fixed subgroup and regular action.
Consequently every clause of the E.6.11 cyclic-section interface transfers.

This allows the symplectic branch to choose a scalar Levi torus without
changing the action decomposition used in E.6.25. Source: Aschbacher–Smith,
combined manuscript (1 March 2004), printed pp.250,255.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts
variable {G : Type*} [Group G] {M V U X Y : Subgroup G}

private noncomputable def faithfulImageEquiv (hN : X ≤ normalizer (V : Set G))
    (hf : X ⊓ centralizer (V : Set G) = ⊥) : X ≃* inducedAutomizer V X := by
  let f : X →* inducedAutomizer V X :=
    (V.normalizerMonoidHom.rangeRestrict.comp (inclusion hN)).codRestrict _
      (fun x => ⟨⟨x, hN x.property⟩, x.property, rfl⟩)
  apply MulEquiv.ofBijective f
  constructor
  · apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro x hx
    have he : V.normalizerMonoidHom ⟨x, hN x.property⟩ = 1 :=
      congrArg (fun a : inducedAutomizer V X => (a.val : MulAut V)) hx
    have hc : (x : G) ∈ centralizer (V : Set G) := by
      have hk : (⟨x, hN x.property⟩ : normalizer (V : Set G)) ∈
          V.normalizerMonoidHom.ker := he
      rwa [Subgroup.normalizerMonoidHom_ker] at hk
    apply mem_bot.mpr
    apply Subtype.ext
    exact mem_bot.mp (hf ▸ (show (x : G) ∈ X ⊓ centralizer (V : Set G) from
      ⟨x.property, hc⟩))
  · rintro ⟨a, n, hn, he⟩
    exact ⟨⟨n, hn⟩, Subtype.ext he⟩

private theorem exists_equiv_of_same_image
    (hXN : X ≤ normalizer (V : Set G)) (hYN : Y ≤ normalizer (V : Set G))
    (hXf : X ⊓ centralizer (V : Set G) = ⊥)
    (hYf : Y ⊓ centralizer (V : Set G) = ⊥)
    (hi : inducedAutomizer V Y = inducedAutomizer V X) :
    ∃ e : X ≃* Y, ∀ (x : X) (v : G), v ∈ V →
      (e x : G) * v * (e x : G)⁻¹ = (x : G) * v * (x : G)⁻¹ := by
  let eX := faithfulImageEquiv hXN hXf
  let eY := faithfulImageEquiv hYN hYf
  let e := eX.trans ((MulEquiv.subgroupCongr hi.symm).trans eY.symm)
  refine ⟨e, ?_⟩
  intro x v hv
  have he : eY (e x) = MulEquiv.subgroupCongr hi.symm (eX x) :=
    eY.apply_symm_apply _
  exact congrArg (fun a : inducedAutomizer V Y =>
    (((a.val : MulAut V) ⟨v, hv⟩ : V) : G)) he

private theorem displacement_of_equiv (e : X ≃* Y)
    (he : ∀ (x : X) (v : G), v ∈ V →
      (e x : G) * v * (e x : G)⁻¹ = (x : G) * v * (x : G)⁻¹) :
    ⁅V, Y⁆ = ⁅V, X⁆ := by
  rw [commutator_comm V Y, commutator_comm V X]
  apply le_antisymm
  · apply commutator_le.mpr
    intro y hy v hv
    obtain ⟨x, hx⟩ := e.surjective ⟨y, hy⟩
    have he' := congrArg (fun z : G => z * v⁻¹) (he x v hv)
    rw [hx] at he'
    change ⁅y, v⁆ = ⁅(x : G), v⁆ at he'
    rw [he']
    exact commutator_mem_commutator x.property hv
  · apply commutator_le.mpr
    intro x hx v hv
    have he' := congrArg (fun z : G => z * v⁻¹) (he ⟨x, hx⟩ v hv)
    change ⁅(e ⟨x, hx⟩ : G), v⁆ = ⁅x, v⁆ at he'
    rw [← he']
    exact commutator_mem_commutator (e ⟨x, hx⟩).property hv

/-- All clauses of the regular cyclic section survive replacement by a
faithful lift of exactly the same induced action image. -/
theorem regularCyclicSection_of_same_image (hX : RegularCyclicSection M V U X)
    (hY : Y ≤ localNormalizer M V ⊓ centralizer (U : Set G))
    (hYf : Y ⊓ centralizer (V : Set G) = ⊥)
    (hi : inducedAutomizer V Y = inducedAutomizer V X) :
    RegularCyclicSection M V U Y := by
  have hXN := hX.contained.trans (inf_le_left.trans inf_le_right)
  have hYN := hY.trans (inf_le_left.trans inf_le_right)
  obtain ⟨e, he⟩ := exists_equiv_of_same_image hXN hYN hX.faithful hYf hi
  have hd := displacement_of_equiv e he
  have hfixed : V ⊓ centralizer (Y : Set G) = V ⊓ centralizer (X : Set G) := by
    apply le_antisymm
    · rintro v ⟨hv, hc⟩
      refine ⟨hv, mem_centralizer_iff.mpr ?_⟩
      intro x hx
      have hh := mem_centralizer_iff.mp hc (e ⟨x, hx⟩) (e ⟨x, hx⟩).property
      have he' := he ⟨x, hx⟩ v hv
      rw [hh, mul_inv_cancel_right] at he'
      exact (mul_inv_eq_iff_eq_mul.mp he'.symm)
    · rintro v ⟨hv, hc⟩
      refine ⟨hv, mem_centralizer_iff.mpr ?_⟩
      intro y hy
      obtain ⟨x, hx⟩ := e.surjective ⟨y, hy⟩
      have hh := mem_centralizer_iff.mp hc x x.property
      have he' := he x v hv
      rw [hx, hh, mul_inv_cancel_right] at he'
      exact mul_inv_eq_iff_eq_mul.mp he'
  refine ⟨hY, ?_, ?_, hYf, hfixed.trans hX.fixed, ?_, ?_, ?_, ?_⟩
  · let _ := hX.cyclic
    exact isCyclic_of_surjective e e.surjective
  · exact (Nat.card_congr e.toEquiv).symm.trans hX.card_eq
  · rw [hd]; exact hX.spanning
  · rw [hd]; exact hX.disjoint
  · rw [hd]
    intro v hv hv1 w hw hw1
    have hvV := (le_normalizer_iff_commutator_le_left.mp hXN) hv
    obtain ⟨x, hx, hu⟩ := hX.regular v hv hv1 w hw hw1
    refine ⟨e x, (he x v hvV).trans hx, ?_⟩
    intro y hy
    obtain ⟨z, rfl⟩ := e.surjective y
    exact congrArg e (hu z ((he z v hvV).symm.trans hy))
  · rw [hi]
    exact hX.normal_image

end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts
