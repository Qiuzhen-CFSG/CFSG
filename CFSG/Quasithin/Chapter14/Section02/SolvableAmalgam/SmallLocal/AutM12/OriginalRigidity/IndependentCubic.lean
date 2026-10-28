module
public import Theory.GroupTheory.QuaternionCentralProductCubicEnlargement
public import Theory.GroupTheory.QuaternionCentralProductTransport
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.AutM12.OriginalRigidity.CoreCases

/-!
# The independent cubic in the Aut(M₁₂) source branch

The marked core trichotomy makes the actual quaternion base normal whenever
the first parabolic is proper in its characteristic-two overgroup. Its
nonsplit core has order64 and its center lies in that base. The full source
Sylow therefore supplies the hypotheses of the quaternion enlargement theorem.

The split movement embedding is used only to retain the original two factors.
The result gives an actual order-three element centralizing one factor and
acting nontrivially on the other, together with the quaternion centralizer
bound needed by the diagonal movement argument. No residual recognition or
extra automorphism marking is assumed.

Source: Aschbacher–Smith, proof of14.2.21, printed p.988 (PDF p.1005).
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.AutM12.OriginalRigidity
open Subgroup Theory.GroupTheory SourceModel.Transport
open Sporadic.Mathieu.M12ExceptionalExtension FirstParabolic
variable {D B R : Type*} [Group D] [Finite D] [Group B] [Group R]

/-- A proper recognized Aut(M₁₂) first parabolic supplies an independent
cubic on the original transported quaternion factors. The extra split
movement embedding retains the whole second-parabolic geometry. -/
theorem independent_cubic_of_proper_overgroup
    (H : Subgroup D) {α : RankTwoAmalgam H B R}
    (r : RankTwoAmalgam.Iso α ChapterF.GreenBook.AutMathieuTwelve.autAmalgam)
    (f : QuaternionSwapModel.QH →* D) (hf : Function.Injective f)
    (hbase : QuaternionSwapModel.QK.map f =
      (FourWreathTwo.base.comap (wreathMap r)).map (H.subtype.comp (pCore 2 H).subtype))
    (S : Sylow 2 D) (hSH : (S : Subgroup D) ≤ H)
    (hZcentral : (markedCore r).map (H.subtype.comp (pCore 2 H).subtype) ≤ center D)
    (hc : centralizer (pCore 2 D : Set D) ≤ pCore 2 D)
    (hproper : H ≠ ⊤) :
    Nat.card D = 1152 ∧
      centralizer (QuaternionSwapModel.QK.map f : Set D) ≤ QuaternionSwapModel.QK.map f ∧
      ∃ u : D, orderOf u = 3 ∧
        u ∈ normalizer (QuaternionSwapModel.leftFactor.map f : Set D) ∧
        u ∈ centralizer (QuaternionSwapModel.rightFactor.map f : Set D) ∧
        u ∉ centralizer (QuaternionSwapModel.leftFactor.map f : Set D) := by
  let Q := QuaternionSwapModel.QK.map f
  let P := (pCore 2 H).map H.subtype
  let k : pCore 2 H →* D := H.subtype.comp (pCore 2 H).subtype
  have hn := (normal_quaternion_or_eq H r S hSH hZcentral hc).resolve_left hproper
  let : Q.Normal := by
    change (QuaternionSwapModel.QK.map f).Normal
    rwa [hbase]
  have hQ : Nat.card Q = 32 := by
    rw [card_map_of_injective hf,QuaternionSwapModel.card_QK]
  have hP : Nat.card P = 64 := by
    rw [card_map_of_injective H.subtype_injective,
      Nat.card_congr (coreEquiv r).toEquiv,card_outerCore innerModel]
  have hQP : pCore 2 D ≤ P := by
    have hQH : pCore 2 D ≤ H := (pCore_isPGroup.le_sylow_of_normal S).trans hSH
    have hpre : (pCore 2 D).comap H.subtype ≤ pCore 2 H :=
      le_sSup ⟨inferInstance,pCore_isPGroup.comap_of_injective H.subtype H.subtype_injective⟩
    simpa only [map_comap_eq_self (show pCore 2 D ≤ H.subtype.range by
      simpa only [range_subtype] using hQH)] using map_mono (f := H.subtype) hpre
  have hEP : Q ≤ P := by
    change QuaternionSwapModel.QK.map f ≤ P
    rw [hbase]
    rintro _ ⟨x,hx,rfl⟩
    exact ⟨x,x.property,rfl⟩
  let j : pCore 2 H ≃* P := (pCore 2 H).equivMapOfInjective H.subtype H.subtype_injective
  have hz : center P ≤ Q.subgroupOf P := by
    intro x hx
    have hx' : j.symm x ∈ center (pCore 2 H) :=
      (MulEquivClass.apply_mem_center_iff j.symm).mpr hx
    have hm : coreEquiv r (j.symm x) ∈ center outerCore :=
      (MulEquivClass.apply_mem_center_iff (coreEquiv r)).mpr hx'
    rw [center_outerCore_eq innerModel] at hm
    have hmarked : j.symm x ∈ markedCore r := hm
    have hw : wreathMap r (j.symm x) = 1 := by
      apply MonoidHom.mem_ker.mp
      rwa [wreathMap_ker]
    change (x:D) ∈ QuaternionSwapModel.QK.map f
    rw [hbase]
    refine ⟨j.symm x,?_,?_⟩
    · change wreathMap r (j.symm x) ∈ FourWreathTwo.base
      rw [hw]
      exact one_mem _
    · exact congrArg Subtype.val (j.apply_symm_apply x)
  have hself : centralizer (Q : Set D) ≤ Q :=
    selfCentralizing_of_core_envelope_thirty_two Q P hQ hP hEP hQP hz hc
  let eQ : QuaternionSwapModel.QK ≃* Q :=
    QuaternionSwapModel.QK.equivMapOfInjective f hf
  let dq : QuaternionCentralProductData Q := QuaternionSwapModel.coreQuaternionData.map eQ
  have hD : Nat.card D = 1152 := card_eq_1152_of_quaternion_product_enlargement
    Q dq hself H (first_card r) hproper S hSH
  let B₀ := QuaternionSwapModel.leftFactor.map f
  let C₀ := QuaternionSwapModel.rightFactor.map f
  have hb : Nonempty (B₀ ≃* QuaternionGroup 2) :=
    ⟨(QuaternionSwapModel.leftFactor.equivMapOfInjective f hf).symm.trans
      (MonoidHom.ofInjective QuaternionSwapModel.leftEmbedding_injective).symm⟩
  have hc' : Nonempty (C₀ ≃* QuaternionGroup 2) :=
    ⟨(QuaternionSwapModel.rightFactor.equivMapOfInjective f hf).symm.trans
      (MonoidHom.ofInjective QuaternionSwapModel.rightEmbedding_injective).symm⟩
  have hinter : Nat.card (B₀ ⊓ C₀ : Subgroup D) = 2 := by
    rw [← map_inf _ _ _ hf,QuaternionSwapModel.factors_intersection,
      card_map_of_injective hf,QuaternionSwapModel.card_Z]
  have hcomm : ∀ b ∈ B₀, ∀ c ∈ C₀, b*c=c*b := by
    rintro _ ⟨b,hb,rfl⟩ _ ⟨c,hc,rfl⟩
    simpa only [map_mul] using congrArg f (QuaternionSwapModel.factors_commute b hb c hc)
  have hjoin : B₀ ⊔ C₀ = Q := (Subgroup.map_sup _ _ _).symm
  let : (B₀ ⊔ C₀).Normal := hjoin.symm ▸ inferInstanceAs Q.Normal
  exact ⟨hD,hself,exists_left_cubic_of_quaternion_product_card_1152
    B₀ C₀ hb hc' hinter hcomm (hjoin.symm ▸ hself) hD⟩

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.AutM12.OriginalRigidity

end
