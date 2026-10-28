module

public import Theory.SpecificGroups.ReeTwo.SquaringActionCensus
public import Theory.SpecificGroups.ReeTwo.InvertingExtensionFirstCore
public import Theory.SpecificGroups.ReeTwo.FixingNonstandardFirstCore
public import Theory.SpecificGroups.ReeTwo.FixingModelSplitTwo

/-!
# Standard cyclic extensions or a fixed marked first core

Every native squaring action is covered by the two complete action censuses.
The standard split half is retained. Every other case has intrinsic first
core of order 2048, with its actual last-root mark fixed by every automorphism.
Both the order and the fixed mark are transported from the verified models;
no finite certificate or fourth-power condition on the action is assumed.
-/

public noncomputable section
namespace ReeTwo.CyclicExtension
open Subgroup

private theorem firstCore_card_congr {H K : Type*} [Group H] [Group K]
    (e : H ≃* K) :
    Nat.card (InvertingExtension.firstCore H) = Nat.card (InvertingExtension.firstCore K) :=
  Nat.card_congr (centralizerUpperCentralSeriesEquiv e 2).toEquiv

private theorem split_nineteen_equiv :
    Nonempty (InvertingModel.Model 19 false ≃* RootTwistedSylow) := by
  have hact : Core.InvertingActionCensus.representative 19 = Core.rootTwist * Core.a := by
    apply Core.aut_ext
    intro k
    rw [Core.InvertingActionCensus.representative_root]
    exact (by decide +kernel : ∀ k : CoreRoot,
      Core.InvertingActionCensus.representativeRoots 19 k =
        (Core.rootTwist * Core.a) (Core.root k)) k
  have hgen : (SemidirectProduct.inl : Core →* RootTwistedSylow).range ⊔
      zpowers RootTwistedSylow.actor = ⊤ := by
    apply top_unique
    intro x _
    rw [←SemidirectProduct.inl_left_mul_inr_right x]
    apply Subgroup.mul_mem
    · exact (show (SemidirectProduct.inl : Core →* RootTwistedSylow).range ≤ _
        from le_sup_left) ⟨_,rfl⟩
    · have hh : SemidirectProduct.inr x.right = RootTwistedSylow.actor ^ x.right.toAdd.val := by
        rw [RootTwistedSylow.actor,←map_pow,FiveFour.generator_pow_val]
      rw [hh]
      exact (show zpowers RootTwistedSylow.actor ≤ _ from le_sup_right)
        (npow_mem_zpowers _ _)
  have hc (q : Core) : RootTwistedSylow.actor * SemidirectProduct.inl q *
      RootTwistedSylow.actor⁻¹ = SemidirectProduct.inl (Core.InvertingActionCensus.representative 19 q) := by
    rw [RootTwistedSylow.actor,←map_inv,←SemidirectProduct.inl_aut]
    rw [rootTwistedAction,FiveFour.cyclicHom_generator,hact]
  have hfour : RootTwistedSylow.actor ^ 4 =
      SemidirectProduct.inl (CyclicFourCentralExtension.mark false) := by decide +kernel
  exact ⟨CyclicFourCentralExtension.equiv SemidirectProduct.inl RootTwistedSylow.actor
    hc hfour RootTwistedSylow.card hgen⟩

private theorem inverting_zero_card (ε : Bool) :
    Nat.card (InvertingModel.firstCore 0 ε) = 2048 := by
  cases ε with
  | false =>
    obtain ⟨f⟩ := split_nineteen_equiv
    have h19 : Nat.card (InvertingModel.firstCore 19 false) = 2048 :=
      (firstCore_card_congr f).trans RootTwistedSylow.firstCore_card
    obtain ⟨e,_⟩ := InvertingModel.exists_marked_base_equiv 19 false
    change InvertingModel.Model 19 false ≃* InvertingModel.Model 0 false at e
    exact (firstCore_card_congr e).symm.trans h19
  | true =>
    obtain ⟨e,_⟩ := InvertingModel.exists_marked_base_equiv 19 true
    change InvertingModel.Model 19 true ≃* InvertingModel.Model 0 true at e
    exact (firstCore_card_congr e).symm.trans InvertingModel.NonsplitZero.K_card

private theorem inverting_card (i : Fin 20) (ε : Bool) :
    Nat.card (InvertingModel.firstCore i ε) = 2048 := by
  obtain ⟨e,_⟩ := InvertingModel.exists_marked_base_equiv i ε
  have hc := firstCore_card_congr e
  change Nat.card (InvertingModel.firstCore i ε) =
    Nat.card (InvertingModel.firstCore (InvertingModel.baseIndex i) ε) at hc
  rw [hc]
  rcases (by decide +kernel : ∀ i : Fin 20,
    InvertingModel.baseIndex i = 0 ∨ InvertingModel.baseIndex i = 6) i with h | h
  · rw [h]
    exact inverting_zero_card ε
  · rw [h]
    exact InvertingModel.Six.firstCore_card ε

private theorem fixing_nonsplit_card (i : Fin 20) :
    Nat.card (FixingModel.firstCore i true) = 2048 := by
  have hzero : Nat.card (FixingModel.firstCore 0 true) = 2048 := by
    obtain ⟨e,_⟩ := FixingModel.exists_marked_base_equiv 19 true
    change FixingModel.Model 19 true ≃* FixingModel.Model 0 true at e
    exact (firstCore_card_congr e).symm.trans FixingModel.NonsplitZero.K_card
  obtain ⟨e,_⟩ := FixingModel.exists_marked_base_equiv i true
  have hc := firstCore_card_congr e
  change Nat.card (FixingModel.firstCore i true) =
    Nat.card (FixingModel.firstCore (FixingModel.baseIndex i) true) at hc
  rw [hc]
  rcases (by decide +kernel : ∀ i : Fin 20,
    FixingModel.baseIndex i = 0 ∨ FixingModel.baseIndex i = 2) i with h | h
  · rw [h]
    exact hzero
  · rw [h]
    exact FixingModel.Two.firstCore_card true

private theorem fixing_nonstandard_card (i : Fin 20)
    (hi : ¬ Core.FixingActionCensus.IsStandard i) :
    Nat.card (FixingModel.firstCore i false) = 2048 := by
  obtain ⟨e,_⟩ := FixingModel.exists_marked_base_equiv i false
  have hc := firstCore_card_congr e
  change Nat.card (FixingModel.firstCore i false) =
    Nat.card (FixingModel.firstCore (FixingModel.baseIndex i) false) at hc
  rw [hc,FixingModel.baseIndex_eq_two_of_not_standard i hi]
  exact FixingModel.Two.firstCore_card false

/-- An actual native cyclic extension is standard and split, or its intrinsic
first core has order 2048 and fixes the actual embedded last root under every
automorphism. All nonstandard and nonsplit certificates are consumed here. -/
theorem standard_or_firstCore_obstruction
    {S : Type*} [Group S] [Finite S]
    (hcard : Nat.card S = 4096) (j : Core →* S) (s : S) (β : MulAut Core)
    (hgen : j.range ⊔ zpowers s = ⊤)
    (hc : β * Core.c * β⁻¹ = Core.c ^ 2)
    (hconj : ∀ q, s * j q * s⁻¹ = j (β q))
    (hfour : s ^ 4 = 1 ∨ s ^ 4 = j (Core.root 9)) :
    (s ^ 4 = 1 ∧ ∃ i : Fin 20, Core.FixingActionCensus.IsStandard i ∧
      β = Core.FixingActionCensus.representative i) ∨
    (Nat.card (InvertingExtension.firstCore S) = 2048 ∧
      ∃ hz : j (Core.root 9) ∈ InvertingExtension.firstCore S,
        ∀ a : MulAut (InvertingExtension.firstCore S),
          a ⟨j (Core.root 9),hz⟩ = ⟨j (Core.root 9),hz⟩) := by
  rcases Core.squaring_action_census β hc with ⟨i,rfl⟩ | ⟨i,rfl⟩
  · rcases hfour with hsplit | hnonsplit
    · by_cases hi : Core.FixingActionCensus.IsStandard i
      · exact Or.inl ⟨hsplit,i,hi,rfl⟩
      right
      have hε : s ^ 4 = j (CyclicFourCentralExtension.mark false) := by
        simpa [CyclicFourCentralExtension.mark] using hsplit
      let e : FixingModel.Model i false ≃* S :=
        CyclicFourCentralExtension.equiv j s hconj hε hcard hgen
      refine ⟨(firstCore_card_congr e).symm.trans (fixing_nonstandard_card i hi),?_⟩
      exact FixingExtension.nonstandard_firstCore_obstruction_of_two_certificate
        FixingModel.two_false_fixed hcard j s i hi hgen hconj hsplit
    · right
      have hε : s ^ 4 = j (CyclicFourCentralExtension.mark true) := hnonsplit
      let e : FixingModel.Model i true ≃* S :=
        CyclicFourCentralExtension.equiv j s hconj hε hcard hgen
      refine ⟨(firstCore_card_congr e).symm.trans (fixing_nonsplit_card i),?_⟩
      exact FixingExtension.root_nine_firstCore_obstruction hcard j s
        (Core.FixingActionCensus.representative i) hgen
        (Core.FixingActionCensus.representative_four i) hc
        (Core.FixingActionCensus.representative_root_two i) hconj hnonsplit
  · right
    obtain ⟨ε,hε⟩ : ∃ ε : Bool, s ^ 4 = j (CyclicFourCentralExtension.mark ε) := by
      rcases hfour with h | h
      · exact ⟨false,by simpa [CyclicFourCentralExtension.mark] using h⟩
      · exact ⟨true,h⟩
    let e : InvertingModel.Model i ε ≃* S :=
      CyclicFourCentralExtension.equiv j s hconj hε hcard hgen
    refine ⟨(firstCore_card_congr e).symm.trans (inverting_card i ε),?_⟩
    exact InvertingExtension.root_nine_firstCore_obstruction hcard j s
      (Core.InvertingActionCensus.representative i) hgen
      (Core.InvertingActionCensus.representative_four i) hc
      (Core.InvertingActionCensus.representative_root_two i) hconj hfour

end ReeTwo.CyclicExtension
