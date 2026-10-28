module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.LocalSubgroups.XCensus.Projection
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.LocalSubgroups.XCensus.Five
public import Theory.GroupAction.FiveInvertingInvolutionFixed

/-!
# The actual F action in the split A5 quotient

The self-centralizing subgroup F makes the complement action faithful.
Every involution of A5 inverts a five-element, so the binary fixed-space
lemma gives exactly four fixed elements. The faithful five-action fixes
only the identity. For three-elements we reuse the established normalizer
stabilizer argument. All action statements concern conjugation on the
literal subgroup F, transported only along its isomorphism with the kernel.

Source: Janko, *A characterization of the Mathieu simple groups, I* (1968),
Section 8, Lemma 17, pp.16--17, using the Section 2 local structure.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.LocalSubgroups.XCensus

private theorem fixed_iff {E : Type*} [Group E] (a : MulAut E) (r : E) :
    r ∈ FixedPoints.subgroup (zpowers a) E ↔ a r = r := by
  constructor
  · intro hr
    exact hr ⟨a, mem_zpowers a⟩
  · intro hr t
    obtain ⟨n, hn⟩ := t.property
    change (t : MulAut E) r = r
    rw [← hn]
    exact MulAction.mem_fixedBy_zpow (show r ∈ MulAction.fixedBy E a from hr) n

private theorem five_free {E : Type*} [Group E] [Finite E]
    (hE : Nat.card E = 16) (a : MulAut E) (ha : orderOf a = 5) (r : E)
    (hr : a r = r) : r = 1 := by
  have hbot : FixedPoints.subgroup (zpowers a) E = ⊥ := by
    apply Theory.GroupAction.fixed_eq_bot_of_five_action_card_sixteen
      (by rw [Nat.card_zpowers, ha]) hE
    intro ht
    have ha1 : a = 1 := by
      ext x
      exact (fixed_iff a x).mp (ht ▸ mem_top x)
    simp [ha1] at ha
  have hm := (fixed_iff a r).mpr hr
  simpa only [hbot, mem_bot] using hm

open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

/-- The split projection and all its fiber-action hypotheses hold for the literal X. -/
public theorem exists_census_data (L : LocalAnalysisData D k) :
    ∃ (π : X D k →* alternatingGroup (Fin 5))
      (s : alternatingGroup (Fin 5) →* X D k),
      (∀ a, π (s a) = a) ∧
      (∀ r : π.ker, (r : X D k) ^ 2 = 1) ∧
      Nat.card π.ker = 16 ∧
      (∀ a : alternatingGroup (Fin 5), orderOf a = 2 →
        Nat.card {r : π.ker // Commute (s a) (r : X D k)} = 4) ∧
      (∀ a : alternatingGroup (Fin 5), orderOf a = 3 ∨ orderOf a = 5 →
        ∀ r ∈ π.ker, Commute (s a) r → r = 1) := by
  classical
  obtain ⟨π, s, hs, hker⟩ := exists_XSplitProjection D k L
  obtain ⟨w⟩ := exists_intersectionActor D k L
  let e : π.ker ≃* CaseII.F D k := (MulEquiv.subgroupCongr hker).trans
    (subgroupOfEquivOfLe (F_le_X D k L w))
  have he (r : π.ker) : (e r : G) = ((r : X D k) : G) := rfl
  have hrmem (r : X D k) (hr : r ∈ π.ker) : (r : G) ∈ CaseII.F D k := by
    have hh := hr
    rw [hker] at hh
    exact hh
  let j : X D k →* normalizer (CaseII.F D k : Set G) :=
    inclusion (X_le_normalizer_F D k)
  let ρ : alternatingGroup (Fin 5) →* MulAut (CaseII.F D k) :=
    (CaseII.F D k).normalizerMonoidHom.comp (j.comp s)
  have hρ : Function.Injective ρ := by
    apply (MonoidHom.ker_eq_bot_iff ρ).mp
    apply bot_unique
    intro a ha
    apply mem_bot.mpr
    have hh : j (s a) ∈ (CaseII.F D k).normalizerMonoidHom.ker := ha
    rw [normalizerMonoidHom_ker, CaseII.F_centralizer] at hh
    have hm : s a ∈ π.ker := by rw [hker]; exact hh
    exact (hs a).symm.trans (MonoidHom.mem_ker.mp hm)
  have hfix (a : alternatingGroup (Fin 5)) (r : π.ker) :
      Commute (s a) (r : X D k) ↔ ρ a (e r) = e r := by
    rw [Subtype.ext_iff]
    change Commute (s a) (r : X D k) ↔
      (s a : G) * (e r : G) * (s a : G)⁻¹ = (e r : G)
    rw [he, mul_inv_eq_iff_eq_mul]
    exact ⟨fun h => congrArg (fun x : X D k => (x : G)) h.eq,
      fun h => show (s a) * (r : X D k) = (r : X D k) * (s a) from Subtype.ext h⟩
  let := CaseII.F_elementary D k
  refine ⟨π, s, hs, ?_, ?_, ?_, ?_⟩
  · intro r
    apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian ((r : X D k) : G)
      (hrmem r r.property)
  · rw [Nat.card_congr e.toEquiv, CaseII.F_card]
  · intro a ha
    obtain ⟨b, hb, hab⟩ := a5_involution_inverts_five a ha
    have hbρ : orderOf (ρ b) = 5 := (orderOf_injective ρ hρ b).trans hb
    have haρ : (ρ a) ^ 2 = 1 := by
      rw [← map_pow, ← ha, pow_orderOf_eq_one, map_one]
    have habρ : ρ a * ρ b * (ρ a)⁻¹ = (ρ b)⁻¹ := by
      simpa only [map_mul, map_inv] using congrArg ρ hab
    have hc := card_fixed_of_involution_inverting_five_on_sixteen
      (CaseII.F_card D k) (ρ b) (ρ a) hbρ haρ habρ
    rw [Nat.card_congr (e.toEquiv.subtypeEquiv (fun r =>
      (hfix a r).trans (fixed_iff (ρ a) (e r)).symm))]
    exact hc
  · intro a ha r hr hc
    rcases ha with ha | ha
    · apply Subtype.ext
      apply F_three_fixed_point_free D k L (s a : G)
        (X_le_normalizer_F D k (s a).property)
      · rw [Subgroup.orderOf_coe, orderOf_injective s (Function.LeftInverse.injective hs), ha]
      · exact hrmem r hr
      · exact hc.map (X D k).subtype
    · have hh := five_free (CaseII.F_card D k) (ρ a)
        ((orderOf_injective ρ hρ a).trans ha) (e ⟨r, hr⟩) ((hfix a ⟨r, hr⟩).mp hc)
      have hh' : (⟨r, hr⟩ : π.ker) = 1 := e.injective (hh.trans e.map_one.symm)
      exact congrArg Subtype.val hh'
end Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.LocalSubgroups.XCensus
