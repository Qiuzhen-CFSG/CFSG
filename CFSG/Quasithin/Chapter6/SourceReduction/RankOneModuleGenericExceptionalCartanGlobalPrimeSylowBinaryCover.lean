module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSylowBinaryTriality
public import Theory.SpecificGroups.Triality.BinaryGeneratedExtension

/-!
# The whole smaller overgroup quotient at binary triality

Let X = G₀T₀ in the smaller changed-Sylow branch. The actual quotient
X/O₂(X) has three-rank at most two, so its cubic prime actor is contained
in the normal triality component. That component and the original Sylow
image generate X/O₂(X). Binary triality has no outer two-extension, and
the quotient's two-core is trivial; hence the component is the whole quotient.

Lifting through the two-core places the original actor D in K. The perfect
component K is exactly O²(X), and its inclusion induces the isomorphism
K/O₂(K) ≃ X/O₂(X). The final theorem retains this marking on the actual
changed-Sylow witness and the already identified PSL₂(8) right section.

This identifies the remaining binary configuration; it does not exclude it.
The original field degree is not identified with the arm field degree.
Binary exclusion, source selection, higher-field reduction, other containing
families and the larger-Sylow argument remain with
qt-d-1222-rankone-cartan-local-to-global. Source: Aschbacher–Smith 5.2.2,
printed pp.648–649, and A.3.18, pp.51–53.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- The binary containing component fills the literal two-core quotient of
G₀T₀. The cubic rank bound places the prime actor in the component image. -/
theorem LocalData.source_overcomponent_binaryTriality_image_top
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
    (hm : Triality.Standard.IsTrialityGroupAt 2 (K ⧸ pCore 2 K)) :
    let X := generated L H D R ⊔ normalizingSylow T R
    (K.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X)) = ⊤ := by
  let X := generated L H D R ⊔ normalizingSylow T R
  let q := QuotientGroup.mk' (pCore 2 X)
  let Kbar := (K.subgroupOf X).map q
  let Dbar := (D.subgroupOf X).map q
  let Sbar := ((normalizingSylow T R).subgroupOf X).map q
  have hp : p = 3 := d.source_overcomponent_binaryTriality_prime h hH c hd hz hSyl hRK hKX hK hKn hm
  have hDp : IsPGroup 3 D := IsPGroup.of_card (n := 1) (by simpa [hp] using hd.card)
  have hS : IsPGroup 2 Sbar :=
    ((T.isPGroup'.to_le (show normalizingSylow T R ≤ (T : Subgroup G) from inf_le_left)).comap_subtype).map q
  have hDX : D ≤ X := le_sup_left.trans le_sup_left
  have hgen : D ⊔ K ⊔ normalizingSylow T R = X := by
    apply le_antisymm (sup_le (sup_le hDX hKX) le_sup_right)
    exact sup_le (sup_le (le_sup_left.trans le_sup_left)
      (sup_le (hRK.le.trans (le_sup_right.trans le_sup_left))
        ((d.sourceS_le_normalizingSylow h hH).trans le_sup_right))) le_sup_right
  have hgen' : D.subgroupOf X ⊔ K.subgroupOf X ⊔
      (normalizingSylow T R).subgroupOf X = ⊤ := by
    rw [←subgroupOf_sup hDX hKX,←subgroupOf_sup (sup_le hDX hKX) le_sup_right,
      hgen,subgroupOf_self]
  have hgenbar : Dbar ⊔ Kbar ⊔ Sbar = ⊤ := by
    simpa only [Subgroup.map_sup,map_top_of_surjective q (QuotientGroup.mk'_surjective _)] using
      congrArg (map q) hgen'
  have hQ := (Chapter3.sqtk_of_mem_H h.qtke (d.extension_core_ne_bot hz)).subgroup
    (X.subgroupOf (extension T L H B D R))
  have hrX : primeRank 3 X ≤ 2 := by
    rw [←primeRank_equiv 3 (subgroupOfEquivOfLe
      (show X ≤ extension T L H B D R from le_sup_left))]
    exact hQ.stronglyQuasithin 3 Nat.prime_three (by decide)
  have hr : primeRank 3 (X ⧸ pCore 2 X) ≤ 2 :=
    (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup).trans hrX
  let : (K.subgroupOf X).Normal := hKn
  let : Kbar.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let ec := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKX)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hKX))
  let eK : Kbar ≃* (K ⧸ pCore 2 K) := (cComponentTwoCoreQuotientEquiv hK).symm.trans ec
  have hm' : Triality.Standard.IsTrialityGroupAt (2 ^ 1) (K ⧸ pCore 2 K) := by
    simpa only [pow_one] using hm
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff
    (K ⧸ pCore 2 K) 1 Nat.zero_lt_one).mp hm'
  exact Triality.Standard.BinaryGeneratedExtension.eq_top_of_generated Kbar Dbar Sbar
    (eK.trans e) hr (pCore_quotient_pCore_eq_bot 2)
    (hDp.comap_subtype.map q) hS hgenbar

/-- In the binary branch the original actor lies in K, and inclusion of K
induces the isomorphism with the whole smaller overgroup quotient.
The containing component is the literal two-residual of that overgroup. -/
theorem LocalData.source_overcomponent_binaryTriality_cover
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
    (hm : Triality.Standard.IsTrialityGroupAt 2 (K ⧸ pCore 2 K)) :
    let X := generated L H D R ⊔ normalizingSylow T R
    D ≤ K ∧ K = residual X ∧ K ⊔ normalizingSylow T R = X ∧
      Triality.Standard.IsTrialityGroupAt 2 (X ⧸ pCore 2 X) ∧
      ∃ e : (K ⧸ pCore 2 K) ≃* (X ⧸ pCore 2 X),
        ∀ k : K, e (QuotientGroup.mk' (pCore 2 K) k) =
          QuotientGroup.mk' (pCore 2 X) (inclusion hKX k) := by
  let X := generated L H D R ⊔ normalizingSylow T R
  let q := QuotientGroup.mk' (pCore 2 X)
  let Kx := K.subgroupOf X
  let : Kx.Normal := hKn
  have htop : Kx.map q = ⊤ :=
    d.source_overcomponent_binaryTriality_image_top h hH c hd hz hSyl hRK hKX hK hKn hm
  have hsupp : Kx ⊔ pCore 2 X = ⊤ := by
    simpa only [comap_map_eq,q,QuotientGroup.ker_mk',comap_top] using congrArg (comap q) htop
  have hquot : IsPGroup 2 (X ⧸ Kx) :=
    isPGroup_quotient_of_sup_eq_top Kx (pCore 2 X) pCore_isPGroup hsupp
  have hp : p = 3 := d.source_overcomponent_binaryTriality_prime h hH c hd hz hSyl hRK hKX hK hKn hm
  have hDp : IsPGroup 3 D := IsPGroup.of_card (n := 1) (by simpa [hp] using hd.card)
  have hDX : D ≤ X := le_sup_left.trans le_sup_left
  let qK := QuotientGroup.mk' Kx
  have hdis := (hDp.comap_subtype (K := X)).map qK |>.disjoint_of_coprime
    (hquot.to_subgroup ⊤) (by decide : Nat.Coprime 3 2)
  have hDK : D ≤ K := by
    intro x hx
    have he : qK (⟨x,hDX hx⟩ : X) = 1 :=
      hdis.le_bot ⟨mem_map_of_mem qK (show (⟨x,hDX hx⟩ : X) ∈ D.subgroupOf X from hx),mem_top _⟩
    exact show (⟨x,hDX hx⟩ : X) ∈ Kx from (QuotientGroup.eq_one_iff _).mp he
  have hKS : K ⊔ normalizingSylow T R = X := by
    apply le_antisymm (sup_le hKX le_sup_right)
    exact sup_le (sup_le (hDK.trans le_sup_left)
      (sup_le (hRK.le.trans le_sup_left)
        ((d.sourceS_le_normalizingSylow h hH).trans le_sup_right))) le_sup_right
  have hres : K = residual X := by
    let : Group.IsPerfect Kx := hK.perfect
    let : Group.IsNilpotent (X ⧸ pResidual 2 X) :=
      (isPGroup_quotient_pResidual 2).isNilpotent
    have he : pResidual 2 X = Kx := le_antisymm
      (sInf_le ⟨inferInstance,hquot⟩)
      (le_of_isPerfect_of_solvable_quotient Kx (pResidual 2 X))
    change K = (pResidual 2 X).map X.subtype
    rw [he,map_subgroupOf_eq_of_le hKX]
  let f := q.comp (inclusion hKX)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨k,hk,he⟩ := mem_map.mp (htop.symm ▸ mem_top y)
    exact ⟨⟨k.val,hk⟩,he⟩
  have hk : IsPGroup 2 f.ker := by
    dsimp only [f]
    rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hKX)
  have hker : f.ker = pCore 2 K := by
    simpa only [pCore_quotient_pCore_eq_bot,MonoidHom.comap_bot] using f.comap_pCore_of_ker_isPGroup hf hk
  let e : (K ⧸ pCore 2 K) ≃* (X ⧸ pCore 2 X) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  obtain ⟨P,hP,⟨ee⟩⟩ := hm
  exact ⟨hDK,hres,hKS,⟨P,hP,⟨e.symm.trans ee⟩⟩,e,fun _ => rfl⟩

/-- The actual changed Sylow retains the marked covering of the whole
smaller quotient. Its cubic actor belongs to the original containing component,
which is identified with the two-residual of the smaller overgroup. -/
theorem LocalData.changedSylow_binary_cover
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
        ∃ K : Subgroup G, R < K ∧ ∃ hKX : K ≤ X,
          (K.subgroupOf X).IsCComponent ∧ (K.subgroupOf X).Normal ∧
          (R.subgroupOf X).map q < (K.subgroupOf X).map q ∧
          (Chapter1.Section02.LocalModels.RankTwoTheoremC (K ⧸ pCore 2 K) →
            Triality.Standard.IsTrialityGroupAt 2 (K ⧸ pCore 2 K) ∧
            ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 8 ∧ p = 3 ∧
            D ≤ K ∧ K = residual X ∧ K ⊔ normalizingSylow T R = X ∧
            Triality.Standard.IsTrialityGroupAt 2 (X ⧸ pCore 2 X) ∧
            ∃ e : (K ⧸ pCore 2 K) ≃* (X ⧸ pCore 2 X),
              ∀ k : K, e (QuotientGroup.mk' (pCore 2 K) k) = q (inclusion hKX k))) ∨
        ∃ U : Sylow 2 G, (U : Subgroup G) = T₁) := by
  obtain ⟨P,hTP,hD,hcases⟩ := d.changedSylow_binary_configuration h hH c hd hz
  refine ⟨P,hTP,hD,?_⟩
  rcases hcases with ⟨he,K,hRK,hKX,hK,hKn,hlt,hm⟩ | ha
  · refine Or.inl ⟨he,K,hRK,hKX,hK,hKn,hlt,?_⟩
    intro hmodel
    obtain ⟨htrial,hr,hp⟩ := hm hmodel
    have hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
        (generated L H D R ⊔ normalizingSylow T R) :=
      Chapter1.IsSylowIn.restrict ⟨P,he⟩ le_sup_right le_sup_left
    exact ⟨htrial,hr,hp,d.source_overcomponent_binaryTriality_cover
      h hH c hd hz hSyl hRK hKX hK hKn htrial⟩
  · exact Or.inr ha

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
