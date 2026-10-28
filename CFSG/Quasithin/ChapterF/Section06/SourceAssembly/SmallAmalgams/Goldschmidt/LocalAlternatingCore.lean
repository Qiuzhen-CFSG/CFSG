module
public import GorensteinWalter.AutAlternatingFour
public import Theory.SpecificGroups.Alternating.FourPairCore
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad.Calculation
public import Theory.GroupTheory.NormalSubgroupCoreQuotient
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual
public import Theory.ElementaryAbelian.Injective
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# The two-core beside an alternating-four residual

If the actual two-residual R is A4, then O2(G) splits as the Klein four
O2(R) and its centralizer of R. The conjugation action on R is transported
to Aut(A4) = S4. A two-subgroup normalized by the inner A4 lies in the
Klein four core of S4, so every element of O2(G) has the same action as an
element of O2(R). The difference centralizes R, and the centerlessness of
A4 gives disjointness. Normal-core restriction gives the commutator bound.

This proves the core decomposition in Goldschmidt, *Automorphisms of
trivalent graphs* (1980), proof of (2.14), for the literal residual and core.
-/

namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt

open Subgroup
open Theory.SpecificGroups.SymmetricSix.DuadCalculation
open GroupTheory.AutAlternating

private theorem outside_core_even : ∀ σ : Four, σ ∉ core →
    (σ ^ 3 = 1 ∧ σ ≠ 1) ∨
      ∃ τ : alternatingGroup (Fin 4),
        (σ * ((τ : Four) * σ * (τ : Four)⁻¹)) ^ 3 = 1 ∧
          σ * ((τ : Four) * σ * (τ : Four)⁻¹) ≠ 1 := by
  decide +kernel

private theorem normal_two_le_core_of_even_conjugates
    (N : Subgroup Four) (hN : IsPGroup 2 N)
    (hn : ∀ σ ∈ N, ∀ τ : alternatingGroup (Fin 4),
      (τ : Four) * σ * (τ : Four)⁻¹ ∈ N) : N ≤ core := by
  have no_three (σ : Four) (hσ : σ ∈ N) (hpow : σ ^ 3 = 1)
      (hne : σ ≠ 1) : False := by
    let x : N := ⟨σ, hσ⟩
    have hc := hN.orderOf_coprime (n := 3) (by decide) x
    have hd : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one
      (show x ^ 3 = 1 from Subtype.ext hpow)
    have he : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hc (dvd_refl _) hd
    exact hne (congrArg Subtype.val (orderOf_eq_one_iff.mp he))
  intro σ hσ
  by_contra hout
  rcases outside_core_even σ hout with ⟨hpow, hne⟩ | ⟨τ, hpow, hne⟩
  · exact no_three σ hσ hpow hne
  · exact no_three _ (N.mul_mem hσ (hn σ hσ τ)) hpow hne

private theorem alternating_core_image :
    (pCore 2 (alternatingGroup (Fin 4))).map (alternatingGroup (Fin 4)).subtype =
      core := by
  have hle : (pCore 2 (alternatingGroup (Fin 4))).map
      (alternatingGroup (Fin 4)).subtype ≤ pCore 2 Four :=
    le_sSup ⟨inferInstance, pCore_isPGroup.map _⟩
  rw [← core_eq] at hle
  apply eq_of_le_of_card_ge hle
  rw [core_card, card_map_of_injective (alternatingGroup (Fin 4)).subtype_injective,
    AlternatingFourPair.twoCore_eq_kleinFour,
    alternatingGroup.kleinFour_card_of_card_eq_four (by simp)]

private noncomputable def autA4 : Four ≃* MulAut (alternatingGroup (Fin 4)) :=
  MulEquiv.ofBijective MulAut.conjNormal aut_alternatingGroup_four_bijective_conj

private noncomputable def modelAction {G : Type*} [Group G]
    (R : Subgroup G) [R.Normal] (eR : R ≃* alternatingGroup (Fin 4)) : G →* Four :=
  autA4.symm.toMonoidHom.comp ((MulAut.congr eR).toMonoidHom.comp
    (MulAut.conjNormal (H := R)))

private theorem modelAction_inner {G : Type*} [Group G]
    (R : Subgroup G) [R.Normal] (eR : R ≃* alternatingGroup (Fin 4)) (r : R) :
    modelAction R eR (r : G) = (eR r : Four) := by
  apply autA4.injective
  change autA4 (autA4.symm _) = _
  rw [autA4.apply_symm_apply]
  change (MulAut.congr eR) (MulAut.conjNormal (r : G)) =
    MulAut.conjNormal (eR r : Four)
  rw [MulAut.conjNormal_val, MulAut.conjNormal_val]
  ext x
  simp [MulAut.congr_apply, MulAut.conj_apply]

private theorem modelAction_twoCore_le {G : Type*} [Group G]
    (R : Subgroup G) [R.Normal] (eR : R ≃* alternatingGroup (Fin 4)) :
    (pCore 2 G).map (modelAction R eR) ≤ core := by
  apply normal_two_le_core_of_even_conjugates _ (pCore_isPGroup.map _)
  rintro σ ⟨q, hq, rfl⟩ τ
  let r := eR.symm τ
  have hr : modelAction R eR (r : G) = (τ : Four) := by
    rw [modelAction_inner]
    simp [r]
  refine mem_map.mpr ⟨(r : G) * q * (r : G)⁻¹,
    (inferInstance : (pCore 2 G).Normal).conj_mem q hq (r : G), ?_⟩
  simp only [map_mul, map_inv, hr]

private theorem modelAction_ker {G : Type*} [Group G]
    (R : Subgroup G) [R.Normal] (eR : R ≃* alternatingGroup (Fin 4)) :
    (modelAction R eR).ker = centralizer (R : Set G) := by
  rw [modelAction, MonoidHom.ker_comp_of_injective _ _ autA4.symm.injective,
    MonoidHom.ker_comp_of_injective _ _ (MulAut.congr eR).injective,
    conjNormal_ker_local]

private theorem embedded_core_image {G : Type*} [Group G]
    (R : Subgroup G) [R.Normal] (eR : R ≃* alternatingGroup (Fin 4)) :
    (R.pCoreIn 2).map (modelAction R eR) = core := by
  rw [pCoreIn, map_map]
  have he : (modelAction R eR).comp R.subtype =
      (alternatingGroup (Fin 4)).subtype.comp eR.toMonoidHom := by
    apply MonoidHom.ext
    intro r
    exact modelAction_inner R eR r
  rw [he, ← map_map, pCore_map_iso, alternating_core_image]

private theorem modelAction_injective_on_subgroup {G : Type*} [Group G]
    (R : Subgroup G) [R.Normal] (eR : R ≃* alternatingGroup (Fin 4)) :
    Function.Injective ((modelAction R eR).comp R.subtype) := by
  intro r s h
  apply eR.injective
  apply Subtype.ext
  exact (modelAction_inner R eR r).symm.trans
    (h.trans (modelAction_inner R eR s))

private theorem normal_alternating_core_split {G : Type*} [Group G] (R : Subgroup G) [R.Normal]
    (eR : R ≃* alternatingGroup (Fin 4)) :
    let V := R.pCoreIn 2
    let B := pCore 2 G ⊓ centralizer (R : Set G)
    pCore 2 G = V ⊔ B ∧ Disjoint V B ∧ IsElementaryAbelian 2 V ∧
      Nat.card V = 4 ∧ V ≤ centralizer (pCore 2 G : Set G) ∧
      B.Normal ∧ R ⊓ pCore 2 G = V ∧ ⁅pCore 2 G, R⁆ ≤ V := by
  let V := R.pCoreIn 2
  let B := pCore 2 G ⊓ centralizer (R : Set G)
  let φ := modelAction R eR
  have hVnormal : V.Normal := by
    dsimp [V, pCoreIn]
    infer_instance
  let := hVnormal
  have hVQ : V ≤ pCore 2 G := le_sSup ⟨inferInstance, isPGroup_pCoreIn 2 R⟩
  have hVR : V ≤ R := pCoreIn_le 2 R
  have hRQ : R ⊓ pCore 2 G = V := by
    dsimp [V, pCoreIn]
    rw [pCore_eq_comap_of_normal, map_comap_eq, range_subtype, inf_comm]
  have hi := modelAction_injective_on_subgroup R eR
  have hφV : V.map φ = core := embedded_core_image R eR
  let ψ : V →* core := (φ.comp V.subtype).codRestrict core (fun v => by
    rw [← hφV]
    exact mem_map_of_mem φ v.property)
  have hψ : Function.Injective ψ := by
    intro v w h
    apply Subtype.ext
    have h' := hi (a₁ := ⟨v, hVR v.property⟩) (a₂ := ⟨w, hVR w.property⟩)
      (congrArg Subtype.val h)
    exact congrArg (fun z : R => (z : G)) h'
  have hVe : IsElementaryAbelian 2 V := IsElementaryAbelian.of_injective ψ hψ
  let := hVe
  have hVcard : Nat.card V = 4 := by
    dsimp [V, pCoreIn]
    rw [card_map_of_injective R.subtype_injective,
      ← card_map_of_injective (K := pCore 2 R) (f := eR.toMonoidHom) eR.injective,
      pCore_map_iso, AlternatingFourPair.twoCore_eq_kleinFour,
      alternatingGroup.kleinFour_card_of_card_eq_four (by simp)]
  have hdecomp : pCore 2 G = V ⊔ B := by
    apply le_antisymm
    · intro q hq
      have hqφ : φ q ∈ core := modelAction_twoCore_le R eR (mem_map_of_mem φ hq)
      rw [← hφV] at hqφ
      obtain ⟨v, hv, he⟩ := hqφ
      have hb : v⁻¹ * q ∈ B := by
        refine ⟨(pCore 2 G).mul_mem ((pCore 2 G).inv_mem (hVQ hv)) hq, ?_⟩
        rw [← modelAction_ker R eR]
        change φ (v⁻¹ * q) = 1
        rw [map_mul, map_inv, he, inv_mul_cancel]
      have hh := (V ⊔ B).mul_mem ((le_sup_left : V ≤ V ⊔ B) hv)
        ((le_sup_right : B ≤ V ⊔ B) hb)
      simpa only [mul_inv_cancel_left] using hh
    · exact sup_le hVQ inf_le_left
  have hdisj : Disjoint V B := by
    apply disjoint_iff.mpr
    apply le_bot_iff.mp
    intro x hx
    have hxker : φ x = 1 := by
      change x ∈ φ.ker
      rw [modelAction_ker]
      exact hx.2.2
    have hh := hi (a₁ := ⟨x, hVR hx.1⟩) (a₂ := 1) (by
      change φ x = φ 1
      simpa only [map_one] using hxker)
    exact congrArg Subtype.val hh
  have hVC : V ≤ centralizer (pCore 2 G : Set G) := by
    apply le_centralizer_iff.mp
    rw [hdecomp]
    refine sup_le (le_centralizer_iff_isMulCommutative.mpr inferInstance) ?_
    exact (inf_le_right : B ≤ centralizer (R : Set G)).trans (centralizer_le hVR)
  exact ⟨hdecomp, hdisj, hVe, hVcard, hVC, inferInstance, hRQ,
    (le_inf (commutator_le_right _ _) (commutator_le_left _ _)).trans_eq hRQ⟩

/-- The actual A4 residual splits the ambient two-core into its central four
and the normal core-centralizer factor used in Goldschmidt (2.14). -/
public theorem alternating_residual_core_split {G : Type*} [Group G]
    (eR : pResidual 2 G ≃* alternatingGroup (Fin 4)) :
    let V := (pResidual 2 G).pCoreIn 2
    let B := pCore 2 G ⊓ centralizer ((pResidual 2 G : Subgroup G) : Set G)
    pCore 2 G = V ⊔ B ∧ Disjoint V B ∧ IsElementaryAbelian 2 V ∧
      Nat.card V = 4 ∧ V ≤ centralizer (pCore 2 G : Set G) ∧
      B.Normal ∧ pResidual 2 G ⊓ pCore 2 G = V ∧
      ⁅pCore 2 G, pResidual 2 G⁆ ≤ V :=
  normal_alternating_core_split (pResidual 2 G) eR

/-- The normal centralizer factor meets the whole residual trivially, as
needed by the subsequent S4 direct-product reconstruction. -/
public theorem alternating_residual_disjoint_coreCentralizer {G : Type*} [Group G]
    (eR : pResidual 2 G ≃* alternatingGroup (Fin 4)) :
    Disjoint (pResidual 2 G)
      (pCore 2 G ⊓ centralizer ((pResidual 2 G : Subgroup G) : Set G)) := by
  obtain ⟨_, hd, _, _, _, _, hi, _⟩ := alternating_residual_core_split eR
  apply disjoint_iff.mpr
  apply le_bot_iff.mp
  intro x hx
  have hxV : x ∈ (pResidual 2 G).pCoreIn 2 := by
    rw [← hi]
    exact ⟨hx.1, hx.2.1⟩
  exact (disjoint_iff.mp hd).le ⟨hxV, hx.2⟩

/-- The literal conjugation map into S4, retaining the residual marking,
kernel, and image of its two-core for the direct-product reconstruction. -/
public theorem alternating_residual_action {G : Type*} [Group G]
    (eR : pResidual 2 G ≃* alternatingGroup (Fin 4)) :
    ∃ φ : G →* Equiv.Perm (Fin 4),
      (∀ r : pResidual 2 G, φ (r : G) = (eR r : Equiv.Perm (Fin 4))) ∧
      φ.ker = centralizer ((pResidual 2 G : Subgroup G) : Set G) ∧
      ((pResidual 2 G).pCoreIn 2).map φ = core ∧
      Function.Injective (φ.comp (pResidual 2 G).subtype) :=
  ⟨modelAction (pResidual 2 G) eR, modelAction_inner (pResidual 2 G) eR,
    modelAction_ker (pResidual 2 G) eR, embedded_core_image (pResidual 2 G) eR,
    modelAction_injective_on_subgroup (pResidual 2 G) eR⟩

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
