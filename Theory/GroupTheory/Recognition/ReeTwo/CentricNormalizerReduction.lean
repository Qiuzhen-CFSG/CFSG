module

public import Theory.GroupTheory.Recognition.ReeTwo.CentricNormalizerSetup
public import Theory.SpecificGroups.ReeTwo.SylowCenter
public import Theory.GroupTheory.BinaryCharacterNormalizerFusion
public import Theory.GroupTheory.NormalizerFusionIndexControl
public import Theory.GroupTheory.NormalizerFusionExtension
public import Theory.GroupTheory.CentricRadicalCharacterFusion
public import Theory.GroupTheory.Recognition.ReeTwo.CentricCandidateClassification

/-!
# Local steps for Ree two centric normalizer reduction

A characteristic kernel of a restricted binary character makes it invariant
under the full ambient normalizer. Equality of the internal and ambient
outer automizer indices gives another sufficient condition. Finally, the
verified Sylow center has a unique nonidentity element, so the Sylow
normalizer fixes the specified central involution and preserves both
alternative characters. A centralizer-times-normalizer factorization also
allows character invariance to pass down from a larger subgroup.

These local steps, together with the verified candidate classification and the
intrinsic radical fusion theorem, reduce centric extremal normalizers to
`C_S(Z₂(S))` under the exceptional normalizer hypothesis.

Source: the q = 2 analysis in van Beek (2024), Proposition 3.1, p. 10;
Shinoda (1975), (2.3) and (3.1), pp. 81–83 for the verified model.
-/

namespace ReeTwo

/-- A characteristic kernel in the subgroup suffices for the normalizer action. -/
public theorem normalizerRespects_of_characteristic_ker
    {G : Type*} [Group G] (S : Sylow 2 G) (e : S ≃* SylowModel)
    (χ : SylowModel →* FiveFour.Cyclic 2) (U : Subgroup G) (hU : U ≤ S)
    (hker : ((χ.comp e.toMonoidHom).comp (Subgroup.inclusion hU)).ker.Characteristic) :
    NormalizerRespects S e χ U := by
  let θ := (χ.comp e.toMonoidHom).comp (Subgroup.inclusion hU)
  let : θ.ker.Characteristic := hker
  intro g hg x y hx hxy
  let f := U.normalizerMonoidHom ⟨g⁻¹, (Subgroup.normalizer (U : Set G)).inv_mem hg⟩
  have heq := Subgroup.binary_character_apply_eq_of_characteristic_kernel θ f ⟨x, hx⟩
  have hfy : Subgroup.inclusion hU (f ⟨x, hx⟩) = y := by
    apply Subtype.ext
    change g⁻¹ * (x : G) * (g⁻¹)⁻¹ = (y : G)
    simpa only [inv_inv] using hxy
  change χ (e (Subgroup.inclusion hU (f ⟨x, hx⟩))) = χ (e x) at heq
  rw [hfy] at heq
  exact heq.symm

/-- If the Sylow subgroup realizes every outer action, its characters are invariant. -/
public theorem normalizerRespects_of_outer_index_eq
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) (e : S ≃* SylowModel)
    (χ : SylowModel →* FiveFour.Cyclic 2) (U : Subgroup G) (hU : U ≤ S)
    (hindex :
      ((U ⊔ Subgroup.centralizer (U : Set G)).subgroupOf (S : Subgroup G)).relIndex
          ((Subgroup.normalizer (U : Set G)).subgroupOf (S : Subgroup G)) =
        (U ⊔ Subgroup.centralizer (U : Set G)).relIndex (Subgroup.normalizer (U : Set G))) :
    NormalizerRespects S e χ U := by
  intro g hg x y hx hxy
  exact isConj_iff_eq.mp ((χ.comp e.toMonoidHom).map_isConj
    (Subgroup.normalizer_fusion_control_of_outer_index_eq (S : Subgroup G) U hU
      hindex g hg x y hx hxy))

/-- The ambient Sylow normalizer fixes the unique nonidentity central Sylow element. -/
public theorem normalizer_sylow_le_centralizer
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) (e : S ≃* SylowModel)
    (z : G) (hz : orderOf z = 2)
    (hcentral : (S : Subgroup G) ≤ Subgroup.centralizer {z}) :
    Subgroup.normalizer (S : Set G) ≤ Subgroup.centralizer {z} := by
  let C := Subgroup.centralizer ({z} : Set G)
  let zC : C := ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hzC : zC ∈ Subgroup.center C := by
    apply Subgroup.mem_center_iff.mpr
    intro t
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp t.property)
  have hcyclic : Subgroup.zpowers zC ≤ Subgroup.center C := Subgroup.zpowers_le.mpr hzC
  let : (Subgroup.zpowers zC).Normal := ⟨by
    intro x hx g
    have hcomm := Subgroup.mem_center_iff.mp (hcyclic hx) g
    simpa only [hcomm, mul_assoc, mul_inv_cancel, mul_one] using hx⟩
  have htwo : IsPGroup 2 (Subgroup.zpowers zC) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, pow_one]
    exact (orderOf_injective C.subtype C.subtype_injective zC).symm.trans hz
  have hzS : z ∈ S := htwo.le_sylow_of_normal (S.subtype hcentral)
    (Subgroup.mem_zpowers zC)
  let zS : S := ⟨z, hzS⟩
  have hzne : zS ≠ 1 := by
    intro h
    have hh : z = 1 := congrArg Subtype.val h
    simp [hh] at hz
  have hzSZ : zS ∈ Subgroup.center S := by
    apply Subgroup.mem_center_iff.mpr
    intro t
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hcentral t.property))
  have hunique (x : S) (hx : x ∈ Subgroup.center S) (hne : x ≠ 1) :
      e x = SylowModel.root 9 := by
    apply (SylowModel.eq_one_or_root_twelve_of_mem_center (e x) ?_).resolve_left
    · exact fun h => hne (e.injective (h.trans e.map_one.symm))
    · apply Subgroup.mem_center_iff.mpr
      intro t
      obtain ⟨t, rfl⟩ := e.surjective t
      simpa only [map_mul] using congrArg e (Subgroup.mem_center_iff.mp hx t)
  intro g hg
  let f := (S : Subgroup G).normalizerMonoidHom ⟨g, hg⟩
  have hfZ : f zS ∈ Subgroup.center S :=
    Subgroup.characteristic_iff_le_comap.mp inferInstance f hzSZ
  have hfne : f zS ≠ 1 := fun h => hzne (f.injective (h.trans f.map_one.symm))
  have hfix : f zS = zS := e.injective ((hunique _ hfZ hfne).trans (hunique _ hzSZ hzne).symm)
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  apply mul_inv_eq_iff_eq_mul.mp
  exact congrArg Subtype.val hfix

/-- Both alternative characters respect the ambient Sylow normalizer. -/
public theorem alternativeCharacters_respect_sylow_normalizer
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) (z : G) (hz : orderOf z = 2)
    (hcentral : (S : Subgroup G) ≤ Subgroup.centralizer {z})
    (ec : Subgroup.centralizer {z} ≃* Centralizer) :
    NormalizerRespects S (sylowEquivOfCentralizer S z hcentral ec)
        SylowModel.coreCharacter (S : Subgroup G) ∧
      NormalizerRespects S (sylowEquivOfCentralizer S z hcentral ec)
        SylowModel.mixedCharacter (S : Subgroup G) :=
  alternativeCharacters_respect_centralizer_normalizer S z hcentral ec (S : Subgroup G)
    (normalizer_sylow_le_centralizer S (sylowEquivOfCentralizer S z hcentral ec)
      z hz hcentral)

/-- A normalizer action extends to a larger subgroup when its elements are
products of centralizer elements and simultaneous normalizers. The centralizer
factor fixes the element being transported. -/
public theorem normalizerRespects_of_centralizer_sup_normalizer
    {G : Type*} [Group G] (S : Sylow 2 G) (e : S ≃* SylowModel)
    (χ : SylowModel →* FiveFour.Cyclic 2) (U V : Subgroup G) (hUV : U ≤ V)
    (hcover : Subgroup.normalizer (U : Set G) ≤
      Subgroup.centralizer (U : Set G) ⊔
        (Subgroup.normalizer (U : Set G) ⊓ Subgroup.normalizer (V : Set G)))
    (hV : NormalizerRespects S e χ V) : NormalizerRespects S e χ U := by
  intro g hg x y hx hxy
  obtain ⟨n, hn, heq⟩ := Subgroup.exists_normalizer_extension_of_le_sup U V hcover g hg
  exact hV n hn.2 x y (hUV hx) ((heq x hx).symm.trans hxy)

/-- The explicit Ree candidate classification reduces all centric extremal
normalizers to the exceptional first parabolic core. -/
public theorem alternativeCharacter_centricNormalizerInvariant_of_classification
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) (z : G)
    (hz : orderOf z = 2)
    (hcentral : (S : Subgroup G) ≤ Subgroup.centralizer {z})
    (ec : Subgroup.centralizer {z} ≃* Centralizer)
    (χ : SylowModel →* FiveFour.Cyclic 2)
    (hχ : χ = SylowModel.coreCharacter ∨ χ = SylowModel.mixedCharacter)
    (hexceptional : NormalizerRespects S (sylowEquivOfCentralizer S z hcentral ec)
      χ (firstParabolicCoreIn S (sylowEquivOfCentralizer S z hcentral ec))) :
    CentricNormalizerInvariant S (sylowEquivOfCentralizer S z hcentral ec) χ := by
  let e := sylowEquivOfCentralizer S z hcentral ec
  have hfusion : ∀ {x y : S}, IsConj (x : G) (y : G) → χ (e x) = χ (e y) := by
    intro x y hxy
    apply S.intrinsic_radical_character_fusion (χ.comp e.toMonoidHom) (hxy := hxy)
    intro U hUS _ hcent hrad
    rcases centric_candidate_classification S e χ hχ U hUS hcent hrad with
      rfl | rfl | hker
    · have hnormalizer := alternativeCharacters_respect_sylow_normalizer
        S z hz hcentral ec
      rcases hχ with rfl | rfl
      · exact hnormalizer.1
      · exact hnormalizer.2
    · exact hexceptional
    · exact normalizerRespects_of_characteristic_ker S e χ U hUS hker
  intro U hUS _ _ g hg x y hx hxy
  apply hfusion
  exact isConj_iff.mpr ⟨g⁻¹, by simpa only [inv_inv] using hxy⟩

end ReeTwo
