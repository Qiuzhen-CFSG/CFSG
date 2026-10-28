module

public import Theory.GroupTheory.Recognition.ReeTwo.CentricNormalizerSetup
public import Theory.SpecificGroups.ReeTwo.CoreCharacterKernel
public import Theory.GroupTheory.IntrinsicRadicalTransport
public import Theory.GroupTheory.Recognition.ReeTwo.LargeCentricCandidates
public import Theory.GroupTheory.Recognition.ReeTwo.Order1024Enumeration
public import Theory.GroupTheory.Recognition.ReeTwo.Order1024ExceptionalObstructions
public import Theory.GroupTheory.Recognition.ReeTwo.Order2048Candidates
public import Theory.GroupTheory.Recognition.ReeTwo.SmallCentricCandidateExhaustion

/-!
# The Ree two centric candidate classification

A subgroup corresponding to the canonical order-1024 core has characteristic
restricted kernel for each alternative binary character. Transporting the
intrinsic omega-kernel calculation proves this without an ambient normalizer
hypothesis. The model-side order and census arguments are assembled here and
transported through an arbitrary Sylow realization.

Source: van Beek (2024), Proposition 3.1, p. 10, motivates the classification;
the core calculation is proved in `CoreCharacterKernel` from the verified model.
-/

namespace ReeTwo

namespace SylowModel

private theorem centric_radical_eq_coreSubgroup_of_card_eq_1024
    (U : Subgroup SylowModel)
    (hc : Subgroup.centralizer (U : Set SylowModel) ≤ U)
    (hr : U.normalizerMonoidHom.range ⊓ pCore 2 (MulAut U) ≤
      (MulAut.conj : U →* MulAut U).range)
    (hU : Nat.card U = 1024) : U = coreSubgroup := by
  rcases residualEnumeration U hc hU with hcore | ha | ⟨i, g, rfl⟩
  · exact hcore
  · have hne : U ≠ ⊤ := by
      intro h
      rw [h, Subgroup.card_top, card] at hU
      omega
    exact (hne (eq_top_of_centric_radical_of_isPGroup_mulAut U hc hr ha)).elim
  · exact (exceptionalCandidate_map_conj_not_intrinsic_radical i g hr).elim

private theorem model_candidate_classification
    (χ : SylowModel →* FiveFour.Cyclic 2)
    (hχ : χ = coreCharacter ∨ χ = mixedCharacter)
    (U : Subgroup SylowModel)
    (hc : Subgroup.centralizer (U : Set SylowModel) ≤ U)
    (hr : U.normalizerMonoidHom.range ⊓ pCore 2 (MulAut U) ≤
      (MulAut.conj : U →* MulAut U).range) :
    U = ⊤ ∨ U = firstParabolicCore ∨
      (χ.comp U.subtype).ker.Characteristic := by
  by_cases hlarge : 1024 ≤ Nat.card U
  · rcases large_subgroup_cases U hlarge with ht | h2048 | h1024
    · exact Or.inl ht
    · exact Or.inr (Or.inl
        (centric_radical_eq_firstParabolicCore_of_card_eq_2048 U hc hr h2048))
    · exact Or.inr (Or.inr (by
        rw [centric_radical_eq_coreSubgroup_of_card_eq_1024 U hc hr h1024]
        exact alternativeCharacter_core_ker_characteristic χ hχ))
  · exact Or.inr (Or.inr
      (alternativeCharacter_ker_characteristic_of_small_intrinsic_radical χ hχ U
        hc hr (lt_of_not_ge hlarge)))

end SylowModel

/-- The verified model classification transports to every finite ambient Sylow
realization. The third branch gives the characteristic restricted kernel of
the selected alternative character. -/
public theorem centric_candidate_classification
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) (e : S ≃* SylowModel)
    (χ : SylowModel →* FiveFour.Cyclic 2)
    (hχ : χ = SylowModel.coreCharacter ∨ χ = SylowModel.mixedCharacter)
    (U : Subgroup G) (hUS : U ≤ (S : Subgroup G))
    (hcent : (S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G) ≤ U)
    (hrad : (((S : Subgroup G).subgroupOf (Subgroup.normalizer (U : Set G))).map
        U.normalizerMonoidHom) ⊓ pCore 2 (MulAut U) ≤
      (MulAut.conj : U →* MulAut U).range) :
    U = (S : Subgroup G) ∨ U = firstParabolicCoreIn S e ∨
      ((χ.comp e.toMonoidHom).comp (Subgroup.inclusion hUS)).ker.Characteristic := by
  let V : Subgroup SylowModel :=
    (U.subgroupOf (S : Subgroup G)).map e.toMonoidHom
  have hcentV : Subgroup.centralizer (V : Set SylowModel) ≤ V :=
    (Subgroup.centralizer_subgroupOf_map_le_iff U (S : Subgroup G) hUS e).mpr hcent
  have hradV : V.normalizerMonoidHom.range ⊓ pCore 2 (MulAut V) ≤
      (MulAut.conj : V →* MulAut V).range :=
    (Subgroup.intrinsic_radical_subgroupOf_map_iff U (S : Subgroup G) hUS e 2).mpr hrad
  have hcardV : Nat.card V = Nat.card U := by
    exact Nat.card_congr (Subgroup.subgroupOfMapEquiv U (S : Subgroup G) hUS e).toEquiv.symm
  rcases SylowModel.model_candidate_classification χ hχ V hcentV hradV with ht | hp | hk
  · left
    have hScard : Nat.card (S : Subgroup G) = 4096 :=
      (Nat.card_congr e.toEquiv).trans SylowModel.card
    have hUcard : Nat.card U = Nat.card (S : Subgroup G) := by
      calc
        Nat.card U = Nat.card V := hcardV.symm
        _ = Nat.card (⊤ : Subgroup SylowModel) := by rw [ht]
        _ = 4096 := by rw [Subgroup.card_top, SylowModel.card]
        _ = Nat.card (S : Subgroup G) := hScard.symm
    apply Subgroup.eq_of_le_of_card_ge hUS
    exact hUcard.symm.le
  · right; left
    apply le_antisymm
    · intro x hx
      have hxS : x ∈ (S : Subgroup G) := hUS hx
      let y : S := ⟨x, hxS⟩
      have hyV : e y ∈ V := by
        let z : U.subgroupOf (S : Subgroup G) := ⟨y, hx⟩
        exact ⟨z, z.property, rfl⟩
      have hyP : e y ∈ SylowModel.firstParabolicCore := by simpa [hp] using hyV
      exact (mem_firstParabolicCoreIn S e y).mpr hyP
    · intro x hx
      have hxS : x ∈ (S : Subgroup G) := firstParabolicCoreIn_le S e hx
      let y : S := ⟨x, hxS⟩
      have hyP : e y ∈ SylowModel.firstParabolicCore :=
        (mem_firstParabolicCoreIn S e y).mp hx
      have hyV : e y ∈ V := by simpa [hp] using hyP
      obtain ⟨z, hzU, hzy⟩ := hyV
      have hzeq : (z : S) = y := e.injective hzy
      have hyU : (y : G) ∈ U := by
        rw [← hzeq]
        exact hzU
      exact hyU
  · right; right
    exact Subgroup.characteristic_ker_subgroupOf_map U (S : Subgroup G) hUS e χ hk

/-- The canonical core candidate satisfies the characteristic-kernel alternative
in every ambient realization of the model. -/
public theorem alternativeCharacter_ker_characteristic_of_core_image
    {G : Type*} [Group G] (S : Sylow 2 G) (e : S ≃* SylowModel)
    (χ : SylowModel →* FiveFour.Cyclic 2)
    (hχ : χ = SylowModel.coreCharacter ∨ χ = SylowModel.mixedCharacter)
    (U : Subgroup G) (hUS : U ≤ (S : Subgroup G))
    (hU : (U.subgroupOf (S : Subgroup G)).map e.toMonoidHom = SylowModel.coreSubgroup) :
    ((χ.comp e.toMonoidHom).comp (Subgroup.inclusion hUS)).ker.Characteristic := by
  let eU : U ≃* SylowModel.coreSubgroup :=
    (((Subgroup.subgroupOfEquivOfLe hUS).symm).trans
      ((U.subgroupOf (S : Subgroup G)).equivMapOfInjective e.toMonoidHom e.injective)).trans
      (MulEquiv.subgroupCongr hU)
  apply Subgroup.characteristic_iff_le_comap.mpr
  intro α x hx
  have hx' : eU x ∈ (χ.comp SylowModel.coreSubgroup.subtype).ker := hx
  have h := Subgroup.characteristic_iff_le_comap.mp
    (SylowModel.alternativeCharacter_core_ker_characteristic χ hχ)
    ((eU.symm.trans α).trans eU) hx'
  change χ ((eU (α (eU.symm (eU x)))) : SylowModel) = 1 at h
  rw [eU.symm_apply_apply] at h
  exact h

end ReeTwo
