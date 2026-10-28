module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSylowSmall
public import Theory.SpecificGroups.Triality.BinaryLocalSections
public import Theory.SpecificGroups.Triality.BinaryPrimeActors
public import Theory.GroupTheory.PCoreSurjective.OddExtension

/-!
# The actual binary triality configuration at the smaller changed Sylow

In the literal quotient X/O₂(X), the right local component remains
perfect, nonsolvable, proper in its normal containing component, and
normalized by the original Sylow image. The genuine two-parabolic
placement identifies its marked arm section. Restricting X's quotient
map and removing the two-cores then identifies the original R/O₂(R)
with PSL₂(8), not merely an auxiliary subgroup with the same family tag.

The prime actor acts faithfully on the containing component. Binary
triality's automorphism group is five-free, so this actor has order three.
Combined with the preceding family exclusions, these conclusions describe
the entire remaining rank-two branch on the actual changed-Sylow witness.

No equality between the original Input exponent and the arm field degree
is assumed. Source selection, that comparison, the other containing
families, larger-Sylow branch and final normalization remain with
qt-d-1222-rankone-cartan-local-to-global. Source: Aschbacher–Smith 5.1.13
and 5.2.2, printed pp.636 and 648–649.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- The binary triality endpoint forces the original right component's
literal two-core quotient to be PSL₂(8). -/
theorem LocalData.source_overcomponent_binaryTriality_right_section
    {T : Sylow 2 G} {L W H B D R X K : Subgroup G} {n : ℕ} {κ : GroupClass}
    (d : LocalData T L H B D R) (h : Input κ T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R) X)
    (hRX : R ≤ X) (hKX : K ≤ X) (hRK : R < K)
    (hK : (K.subgroupOf X).IsCComponent) (hKn : (K.subgroupOf X).Normal)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (K ⧸ pCore 2 K)) :
    ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 8 := by
  let q := QuotientGroup.mk' (pCore 2 X)
  let Rbar := (R.subgroupOf X).map q
  let Kbar := (K.subgroupOf X).map q
  obtain ⟨S,hS⟩ := hSyl
  have hTX : normalizingSylow T R ≤ X := hS ▸ map_subtype_le (S : Subgroup X)
  have heS : (S : Subgroup X) = (normalizingSylow T R).subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [map_subgroupOf_eq_of_le hTX]
    exact hS
  let P := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 X))
  have hlocal : R.subgroupOf X ∈ Chapter1.L X ((normalizingSylow T R).subgroupOf X) :=
    (Chapter1.mem_LIn_iff_subgroupOf hTX hRX).mp ⟨hRX,d.right_mem_local_family h hH⟩
  have hlocalbar : Rbar ∈ ChapterA.Section03.localCComponents P := by
    change Rbar ∈ ChapterA.Section03.localCComponents ((S : Subgroup X).map q)
    rw [heS]
    exact Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents hlocal
  have hRns : ¬ Group.IsSolvable Rbar := by
    intro hs
    let := hs
    exact hlocalbar.not_isSolvable
      (Group.isSolvable_of_isSolvable_injective
        (f := (subgroupOfEquivOfLe (show Rbar ≤ Rbar ⊔ (P : Subgroup (X ⧸ pCore 2 X)) from le_sup_left)).toMonoidHom)
        (subgroupOfEquivOfLe le_sup_left).injective)
  have hlt : Rbar < Kbar := d.right_image_lt h hH ⟨S,hS⟩ hRX hKX hRK hK
  let : (K.subgroupOf X).Normal := hKn
  let : Kbar.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hn : (P : Subgroup (X ⧸ pCore 2 X)) ≤ normalizer (Rbar : Set (X ⧸ pCore 2 X)) := by
    change (S : Subgroup X).map q ≤ _
    rw [heS]
    apply (map_mono (f := q) ?_).trans (le_normalizer_map q)
    rw [←subgroupOf_normalizer_eq hRX]
    exact comap_mono (show normalizingSylow T R ≤ normalizer (R : Set G) from inf_le_right)
  obtain ⟨U,hU⟩ := P.exists_subgroupOf_eq_of_normal Kbar
  let R' := Rbar.subgroupOf Kbar
  let b : R' ≃* Rbar := subgroupOfEquivOfLe hlt.le
  let := Chapter1.mem_L_isPerfect hlocal
  let : Group.IsPerfect Rbar := Group.IsPerfect.ofSurjective (q.subgroupMap_surjective _)
  let : Group.IsPerfect R' := Group.IsPerfect.ofSurjective (f := b.symm.toMonoidHom) b.symm.surjective
  have hproper : R' ≠ ⊤ := fun he => hlt.not_ge (subgroupOf_eq_top.mp he)
  have hns : ¬ Group.IsSolvable R' := by
    intro hs
    let := hs
    exact hRns (Group.isSolvable_of_surjective (f := b.toMonoidHom) b.surjective)
  have hUR : (U : Subgroup Kbar) ≤ normalizer (R' : Set Kbar) := by
    rw [hU,←subgroupOf_normalizer_eq hlt.le]
    exact comap_mono hn
  let ec := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKX)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hKX))
  let eK : Kbar ≃* (K ⧸ pCore 2 K) := (cComponentTwoCoreQuotientEquiv hK).symm.trans ec
  have hm' : Triality.Standard.IsTrialityGroupAt (2 ^ 1) (K ⧸ pCore 2 K) := by
    simpa only [pow_one] using hm
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff
    (K ⧸ pCore 2 K) 1 Nat.zero_lt_one).mp hm'
  obtain ⟨a,ha,hRL,eR,heR⟩ := Triality.Standard.BinaryLocalSections.marked_arm_quotient
    (eK.trans e) U R' hproper hns hUR
  let r := q.subgroupMap (R.subgroupOf X)
  have hr : IsPGroup 2 r.ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let eRX := (subgroupOfEquivOfLe hRX).symm
  let e₁ := QuotientGroup.congr _ _ eRX (pCore_map_iso 2 eRX)
  let e₂ := r.quotientPCoreEquivOfSurjective (q.subgroupMap_surjective _) hr
  let e₃ := QuotientGroup.congr _ _ b.symm (pCore_map_iso 2 b.symm)
  let e₄ := Triality.Standard.Parabolics.localFactorArmsQuotientEquivPSL2
    (Triality.Standard.binaryParameters 1 Nat.zero_lt_one) rfl
  exact ⟨Triality.Standard.ExtensionField (Triality.Standard.binaryParameters 1 Nat.zero_lt_one),
    inferInstance,inferInstance,by rw [Triality.Standard.card_extensionField]; rfl,
    ⟨e₁.trans (e₂.trans (e₃.trans (eR.trans e₄)))⟩⟩

/-- The entire rank-two containing family forces the marked right quotient
PSL₂(8), after the previously proved nonbinary and small-model exclusions. -/
theorem LocalData.source_overcomponent_rankTwo_right_section
    {T : Sylow 2 G} {L W H A B D R K : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
      (generated L H D R ⊔ normalizingSylow T R))
    (hRK : R < K) (hKX : K ≤ generated L H D R ⊔ normalizingSylow T R)
    (hK : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).IsCComponent)
    (hKn : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).Normal)
    (hm : Chapter1.Section02.LocalModels.RankTwoTheoremC (K ⧸ pCore 2 K)) :
    Triality.Standard.IsTrialityGroupAt 2 (K ⧸ pCore 2 K) ∧
      ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 8 := by
  have ht := d.source_overcomponent_rankTwo_binaryTriality h hH c hd hSyl hRK hKX hK hKn hm
  exact ⟨ht,d.source_overcomponent_binaryTriality_right_section h hH hSyl
    (le_sup_left.trans (le_sup_right.trans le_sup_left)) hKX hRK hK hKn ht⟩

/-- Faithfulness on the actual containing quotient rules out the quintic
actor at binary triality. -/
theorem LocalData.source_overcomponent_binaryTriality_prime
    {T : Sylow 2 G} {L W H A B D R K : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
      (generated L H D R ⊔ normalizingSylow T R))
    (hRK : R < K) (hKX : K ≤ generated L H D R ⊔ normalizingSylow T R)
    (hK : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).IsCComponent)
    (hKn : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).Normal)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (K ⧸ pCore 2 K)) : p = 3 := by
  let X := generated L H D R ⊔ normalizingSylow T R
  let q := QuotientGroup.mk' (pCore 2 X)
  let Rbar := (R.subgroupOf X).map q
  let Kbar := (K.subgroupOf X).map q
  let Dbar := (D.subgroupOf X).map q
  have hRX : R ≤ X := le_sup_left.trans (le_sup_right.trans le_sup_left)
  have hDX : D ≤ X := le_sup_left.trans le_sup_left
  have hlt : Rbar < Kbar := d.right_image_lt h hH hSyl hRX hKX hRK hK
  obtain ⟨hc,hdis,_⟩ := d.right_quotient_prime_orbit h hH c hd hz hRX hDX hSyl
  let : (K.subgroupOf X).Normal := hKn
  let : Kbar.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hn : Dbar ≤ normalizer (Kbar : Set (X ⧸ pCore 2 X)) := le_normalizer_of_normal
  have hi := normalizer_action_injective_of_disjoint_normalizer hlt.le hn hdis
  let ec := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKX)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hKX))
  let eK : Kbar ≃* (K ⧸ pCore 2 K) := (cComponentTwoCoreQuotientEquiv hK).symm.trans ec
  have hm' : Triality.Standard.IsTrialityGroupAt (2 ^ 1) (K ⧸ pCore 2 K) := by
    simpa only [pow_one] using hm
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff
    (K ⧸ pCore 2 K) 1 Nat.zero_lt_one).mp hm'
  exact Triality.Standard.BinaryPrimeActors.prime_eq_three (eK.trans e)
    (Kbar.normalizerMonoidHom.comp (inclusion hn)) hi hd.prime hc

/-- The remaining rank-two configuration is binary triality with its actual
PSL₂(8) right section and cubic prime actor. -/
theorem LocalData.source_overcomponent_rankTwo_configuration
    {T : Sylow 2 G} {L W H A B D R K : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
      (generated L H D R ⊔ normalizingSylow T R))
    (hRK : R < K) (hKX : K ≤ generated L H D R ⊔ normalizingSylow T R)
    (hK : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).IsCComponent)
    (hKn : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).Normal)
    (hm : Chapter1.Section02.LocalModels.RankTwoTheoremC (K ⧸ pCore 2 K)) :
    Triality.Standard.IsTrialityGroupAt 2 (K ⧸ pCore 2 K) ∧
      ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 8 ∧ p = 3 := by
  obtain ⟨ht,hr⟩ := d.source_overcomponent_rankTwo_right_section h hH c hd hSyl hRK hKX hK hKn hm
  exact ⟨ht,hr,d.source_overcomponent_binaryTriality_prime h hH c hd hz hSyl hRK hKX hK hKn ht⟩

/-- Keep the concrete binary configuration on the original changed-Sylow
witness. The larger alternative is still an actual ambient Sylow. -/
theorem LocalData.changedSylow_binary_configuration
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥) :
    ∃ P : Sylow 2 (extension T L H B D R),
      let T₁ := (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype
      normalizingSylow T R ≤ T₁ ∧
      T₁ ≤ normalizer ((D ⊔ normalizingSylow T R : Subgroup G) : Set G) ∧
      ((T₁ = normalizingSylow T R ∧
        let X := generated L H D R ⊔ normalizingSylow T R
        let q := QuotientGroup.mk' (pCore 2 X)
        ∃ K : Subgroup G, R < K ∧ K ≤ X ∧
          (K.subgroupOf X).IsCComponent ∧ (K.subgroupOf X).Normal ∧
          (R.subgroupOf X).map q < (K.subgroupOf X).map q ∧
          (Chapter1.Section02.LocalModels.RankTwoTheoremC (K ⧸ pCore 2 K) →
            Triality.Standard.IsTrialityGroupAt 2 (K ⧸ pCore 2 K) ∧
            ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 8 ∧ p = 3)) ∨
        ∃ U : Sylow 2 G, (U : Subgroup G) = T₁) := by
  obtain ⟨_,_,P,hTP,_,hD,_,hcases⟩ := d.changedSylow_action h hH c hd hz
  refine ⟨P,hTP,hD,?_⟩
  rcases hcases with he | ha
  · have hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
        (generated L H D R ⊔ normalizingSylow T R) :=
      Chapter1.IsSylowIn.restrict ⟨P,he⟩ le_sup_right le_sup_left
    obtain ⟨K,hRK,hKX,hK,hKn,hlt,_⟩ := d.source_overcomponent_nonBender h hH c hd hz hSyl
    exact Or.inl ⟨he,K,hRK,hKX,hK,hKn,hlt,
      d.source_overcomponent_rankTwo_configuration h hH c hd hz hSyl hRK hKX hK hKn⟩
  · exact Or.inr ha

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
