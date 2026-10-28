module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityHigherSevenPlane
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BinaryCentralCovers
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168

/-!
# Central-cover exclusions for the actual containing image

The quasisimple Y-image is a local C-component for the full image of T
in N_G(R)/R. If its containing image has a binary linear central quotient
of degree three through five, the central-cover theorem forces equality;
the existing quotient-lifting theorem gives equality of the original
subgroups. The SL₂(7) case uses its canonical central projection and the
checked PSL₂(7) ≃ PSL₃(2) comparison, with the existing ATLAS attribution.

These exclusions feed LocalConfigurationRigidityHigherImageSieve.
Source: Aschbacher–Smith, original 12.2.25, printed p.805.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V H P U : Subgroup G} {d : ℕ}

/-- Central covers of the ordinary binary containing images cannot enlarge Y. -/
theorem residual_eq_containing_of_binary_central_cover
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P) (hd : 3 < d)
    {K : Subgroup G} (hKN : K ≤ normalizer (sectionRadical T U : Set G))
    (hK : (K.subgroupOf (normalizer (sectionRadical T U : Set G))).IsCComponent)
    (hYK : rigidityHyperplaneResidual L U V ≤ K)
    {Q : Type*} [Group Q] [Finite Q]
    (f : ThreeRigidity.image T U K →* Q) (hf : Function.Surjective f)
    (hk : f.ker ≤ center (ThreeRigidity.image T U K))
    {m : ℕ} (hm : m = 3 ∨ m = 4 ∨ m = 5) (hmodel : ClassicalGroup.IsPSL Q m 2) :
    rigidityHyperplaneResidual L U V = K := by
  let R := sectionRadical T U
  let N := normalizer (R : Set G)
  let S : Sylow 2 (NormalizerQuotient R) :=
    (T.subtype (sylow_normalizes_sectionRadical C)).mapSurjective
      (QuotientGroup.mk'_surjective _)
  let : Group.IsSolvable (R.subgroupOf N) := by
    let : Group.IsNilpotent (R.subgroupOf N) :=
      ((T.isPGroup'.to_le (show R ≤ (T : Subgroup G) from inf_le_left)).comap_subtype).isNilpotent
    infer_instance
  let := residual_image_quasisimple h D structural A C B hd
  apply residual_eq_containing_of_image_eq h D structural A C B hd hKN hK hYK
  exact ChapterA.Section03.SourceEmbeddings.eq_of_binary_linear_central_cover S
    (residual_image_local h D structural A C B hd) (hK.map_quotient (R.subgroupOf N))
    (map_mono (comap_mono hYK)) f hf hk hm hmodel

/-- In particular the actual SL₂(7) row forces equality, through its canonical
central quotient and the checked exceptional isomorphism. -/
theorem residual_eq_containing_of_special_linear_seven
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P) (hd : 3 < d)
    {K : Subgroup G} (hKN : K ≤ normalizer (sectionRadical T U : Set G))
    (hK : (K.subgroupOf (normalizer (sectionRadical T U : Set G))).IsCComponent)
    (hYK : rigidityHyperplaneResidual L U V ≤ K)
    (hmodel : Chapter1.Section02.LocalModels.IsSL (ThreeRigidity.image T U K) 2 7) :
    rigidityHyperplaneResidual L U V = K := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hmodel
  let := Fintype.ofFinite F
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let a : F ≃+* ZMod 7 := FiniteField.ringEquivOfCardEq (K := F) (K' := ZMod 7) (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
  let e' := e.trans (Atlas.fieldEquivSL 2 a)
  let q := QuotientGroup.mk' (center (Matrix.SpecialLinearGroup (Fin 2) (ZMod 7)))
  let j := Atlas.Comparisons.Exceptional.psl2SevenEquivSl3Two.trans Matrix.PSL3Two.equiv
  let f := j.toMonoidHom.comp (q.comp e'.toMonoidHom)
  have hf : Function.Surjective f := j.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp e'.surjective)
  have hk : f.ker ≤ center (ThreeRigidity.image T U K) := by
    intro x hx
    have hq : q (e' x) = 1 := j.injective (hx.trans j.map_one.symm)
    have hc := (QuotientGroup.eq_one_iff (e' x)).mp hq
    exact mem_center_iff.mpr (fun y => e'.injective (by
      simpa only [map_mul] using mem_center_iff.mp hc (e' y)))
  exact residual_eq_containing_of_binary_central_cover h D structural A C B hd hKN hK hYK
    f hf hk (Or.inl rfl) ⟨ZMod 2,inferInstance,inferInstance,Nat.card_zmod 2,⟨MulEquiv.refl _⟩⟩

/-- The literal central quotient is a special case of the covering map. -/
theorem residual_eq_containing_of_binary_central_quotient
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P) (hd : 3 < d)
    {K : Subgroup G} (hKN : K ≤ normalizer (sectionRadical T U : Set G))
    (hK : (K.subgroupOf (normalizer (sectionRadical T U : Set G))).IsCComponent)
    (hYK : rigidityHyperplaneResidual L U V ≤ K)
    {m : ℕ} (hm : m = 3 ∨ m = 4 ∨ m = 5)
    (hmodel : ClassicalGroup.IsPSL
      ((ThreeRigidity.image T U K) ⧸ center (ThreeRigidity.image T U K)) m 2) :
    rigidityHyperplaneResidual L U V = K :=
  residual_eq_containing_of_binary_central_cover h D structural A C B hd hKN hK hYK
    (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']) hm hmodel

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
