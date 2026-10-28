module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalSmall
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalSieve.SeedReduction
public import Theory.SpecificGroups.Triality.BinaryLocalSections
public import Theory.SpecificGroups.Triality.ConcreteBruhat.FixedCellCount

/-!
# The remaining rank-two container in the original local Cartan sieve

The small and nonbinary exclusions leave genuine ³D₄(2). Its order is
prime to five, whereas every moved source seed has an A₅ two-core
quotient. Thus the seed equals the original residual and the containing
component is normal in the original Y. The marked arm calculation then
identifies that residual's actual two-core quotient with PSL₂(8).

The proof uses the image in Y/O₂(Y), restricts its full Sylow to the actual
containing component, and transports the arm quotient through the original
two-group kernel. No equality with the left field degree is asserted.
The binary triality exclusion and the remaining non-Lie containing rows
are still needed before constructing the escaping inverted cubic.

Source: Aschbacher--Smith 5.1.12--13, printed pp.635--636; GLS3 §§2.3--2.6
for the actual triality root parabolics.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
variable {G : Type*} [Group G] [Finite G]

private theorem five_dvd_image {Q : Type*} [Group Q]
    (q : G →* Q) (R : Subgroup G)
    (hk : IsPGroup 2 (q.subgroupMap R).ker) (h5 : 5 ∣ Nat.card R) :
    5 ∣ Nat.card (R.map q) := by
  have hnot : ¬ 5 ∣ Nat.card (q.subgroupMap R).ker := by
    intro hh
    obtain ⟨n,hn⟩ := hk.exists_card_dvd_pow
    have := Nat.prime_five.dvd_of_dvd_pow (hh.trans hn)
    norm_num at this
  have hc := (q.subgroupMap R).ker.card_mul_index
  rw [Subgroup.index_ker,MonoidHom.range_eq_top_of_surjective _
    (q.subgroupMap_surjective R),card_top] at hc
  exact (Nat.prime_five.dvd_mul.mp (hc.symm ▸ h5)).resolve_left hnot

/-- A containing quotient of order prime to five forces the source seed
to be the whole residual: the only moved seed has an A₅ quotient. -/
theorem seed_eq_residual_of_five_free_container
    {T : Sylow 2 G} {K H A Y : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hfive : ¬ 5 ∣ Nat.card (C ⧸ pCore 2 C)) : K = residual H := by
  by_contra hmoved
  have hm := moved_seed_linear_four_of_escape hG hK hKT horbit hmoved hY hescape
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  obtain ⟨e5⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  have hK5 : 5 ∣ Nat.card K := by
    have hd := card_quotient_dvd_card (pCore 2 K)
    rw [Nat.card_congr (e.trans e5).toEquiv,nat_card_alternatingGroup,Nat.card_fin] at hd
    exact (by decide : 5 ∣ 60).trans (by norm_num at hd; exact hd)
  let q := QuotientGroup.mk' (pCore 2 Y)
  have hk : IsPGroup 2 (q.subgroupMap (K.subgroupOf Y)).ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  have h5 : 5 ∣ Nat.card ((K.subgroupOf Y).map q) := five_dvd_image q _ hk (by
    rw [Nat.card_congr (subgroupOfEquivOfLe (hKH.trans hY.2)).toEquiv]
    exact hK5)
  have hKC' : K.subgroupOf Y ≤ C := by
    change K.comap Y.subtype ≤ C
    have hh := comap_mono (f := Y.subtype) hKC
    simpa only [comap_map_eq_self_of_injective Y.subtype_injective] using hh
  apply hfive
  rw [Nat.card_congr (cComponentTwoCoreQuotientEquiv hC).toEquiv]
  exact h5.trans (card_dvd_of_le (map_mono hKC'))

/-- In binary triality the actual seed is unmoved, and its original
containing C-component is normal in Y. -/
theorem binaryTriality_seed_eq_residual_and_normal
    {T : Sylow 2 G} {K H A Y : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hKH : K ≤ H) (hTH : (T : Subgroup G) ≤ H)
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C)) :
    K = residual H ∧ C.Normal := by
  have hm' : Triality.Standard.IsTrialityGroupAt (2 ^ 1) (C ⧸ pCore 2 C) := by
    simpa only [pow_one] using hm
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff _ 1 Nat.zero_lt_one).mp hm'
  have hfive : ¬ 5 ∣ Nat.card (C ⧸ pCore 2 C) := by
    rw [Nat.card_congr e.toEquiv,Triality.Standard.ConcreteBruhat.FixedCellCount.card_carrier,
      Triality.Standard.ConcreteBruhat.FixedCellCount.card_borel]
    norm_num [Triality.Standard.binaryParameters_q]
  have he := seed_eq_residual_of_five_free_container hG hKH hK hKT horbit hY hescape
    C hC hKC hfive
  refine ⟨he,?_⟩
  by_contra hn
  exact nonnormal_container_seed_moved hG hKH hTH hK hY C hC hKC hn he

/-- The remaining binary triality row has the actual PSL₂(8) residual
quotient; its two-core is not replaced by a solvable radical. -/
theorem binaryTriality_residual_section
    {T : Sylow 2 G} {K H A Y : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hKH : K ≤ H) (hTH : (T : Subgroup G) ≤ H)
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C)) :
    K = residual H ∧ C.Normal ∧
      ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 8 := by
  obtain ⟨hKR,hCn⟩ := binaryTriality_seed_eq_residual_and_normal hG hKH hTH hK hKT horbit
    hY hescape C hC hKC hm
  let q := QuotientGroup.mk' (pCore 2 Y)
  let Kbar := (K.subgroupOf Y).map q
  let Cbar := C.map q
  let S := T.subtype (hTH.trans hY.2)
  let P := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 Y))
  have hlocal : K.subgroupOf Y ∈ Chapter1.L Y (S : Subgroup Y) :=
    (Chapter1.mem_LIn_iff_subgroupOf (hTH.trans hY.2) (hKH.trans hY.2)).mp
      ⟨hKH.trans hY.2,hK⟩
  have hlocalbar : Kbar ∈ ChapterA.Section03.localCComponents P := by
    change (K.subgroupOf Y).map q ∈ ChapterA.Section03.localCComponents ((S : Subgroup Y).map q)
    exact Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents hlocal
  have hlt : Kbar < Cbar := seed_image_lt_container hG hKH hTH hK horbit hY hescape C hC hKC
  let := hCn
  let : Cbar.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hn : (P : Subgroup (Y ⧸ pCore 2 Y)) ≤ normalizer (Kbar : Set _) := by
    apply (map_mono (f := q) ?_).trans (le_normalizer_map q)
    rw [←subgroupOf_normalizer_eq (hKH.trans hY.2)]
    exact comap_mono (hKR ▸ hTH.trans (le_normalizer_residual H))
  obtain ⟨U,hU⟩ := P.exists_subgroupOf_eq_of_normal Cbar
  let R := Kbar.subgroupOf Cbar
  let b : R ≃* Kbar := subgroupOfEquivOfLe hlt.le
  let := Chapter1.mem_L_isPerfect hlocal
  let : Group.IsPerfect Kbar := Group.IsPerfect.ofSurjective (q.subgroupMap_surjective _)
  let : Group.IsPerfect R := Group.IsPerfect.ofSurjective (f := b.symm.toMonoidHom) b.symm.surjective
  have hproper : R ≠ ⊤ := fun he => hlt.not_ge (subgroupOf_eq_top.mp he)
  have hns : ¬ Group.IsSolvable R := by
    intro hs
    let := hs
    let : Group.IsSolvable Kbar := Group.isSolvable_of_surjective (f := b.toMonoidHom) b.surjective
    exact hlocalbar.not_isSolvable (Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (show Kbar ≤ Kbar ⊔ (P : Subgroup _) from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe le_sup_left).injective)
  have hUR : (U : Subgroup Cbar) ≤ normalizer (R : Set Cbar) := by
    rw [hU,←subgroupOf_normalizer_eq hlt.le]
    exact comap_mono hn
  have hm' : Triality.Standard.IsTrialityGroupAt (2 ^ 1) (C ⧸ pCore 2 C) := by
    simpa only [pow_one] using hm
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff _ 1 Nat.zero_lt_one).mp hm'
  let eC : Cbar ≃* (C ⧸ pCore 2 C) := (cComponentTwoCoreQuotientEquiv hC).symm
  obtain ⟨a,ha,hRL,eR,heR⟩ := Triality.Standard.BinaryLocalSections.marked_arm_quotient
    (eC.trans e) U R hproper hns hUR
  let r := q.subgroupMap (K.subgroupOf Y)
  have hr : IsPGroup 2 r.ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let eKY := (subgroupOfEquivOfLe (hKH.trans hY.2)).symm
  let e₁ := QuotientGroup.congr _ _ eKY (pCore_map_iso 2 eKY)
  let e₂ := r.quotientPCoreEquivOfSurjective (q.subgroupMap_surjective _) hr
  let e₃ := QuotientGroup.congr _ _ b.symm (pCore_map_iso 2 b.symm)
  let e₄ := Triality.Standard.Parabolics.localFactorArmsQuotientEquivPSL2
    (Triality.Standard.binaryParameters 1 Nat.zero_lt_one) rfl
  have hmodel : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 8 :=
    ⟨Triality.Standard.ExtensionField (Triality.Standard.binaryParameters 1 Nat.zero_lt_one),
      inferInstance,inferInstance,by rw [Triality.Standard.card_extensionField]; rfl,
      ⟨e₁.trans (e₂.trans (e₃.trans (eR.trans e₄)))⟩⟩
  let eK : (pResidual 2 H) ≃* residual H :=
    (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
  rw [hKR] at hmodel
  exact ⟨hKR,hCn,hmodel.of_mulEquiv (QuotientGroup.congr _ _ eK (pCore_map_iso 2 eK))⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

/-- On the original escaping input, the complete rank-two containing row
is reduced to binary triality with the unmoved residual and its literal
PSL₂(8) quotient. The original seed, quotient images, and full orbit remain. -/
theorem localCartan_escape_seed_rankTwo_reduction
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧ K ⊔ (T : Subgroup G) = H ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧
      componentOrbit K (T : Subgroup G) = residual H ∧
      ∃ C : Subgroup Y, C.IsCComponent ∧ K ≤ C.map Y.subtype ∧
        residual H < componentOrbit (C.map Y.subtype) (T : Subgroup G) ∧
        ((componentOrbit (C.map Y.subtype) (T : Subgroup G)).subgroupOf Y).Normal ∧
        (K.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y)) <
          C.map (QuotientGroup.mk' (pCore 2 Y)) ∧
        ¬ SolvableSylowOvergroups (C ⧸ pCore 2 C) ∧
        (∀ m : ℕ, 0 < m → ¬ (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨
          IsSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨ IsSU (C ⧸ pCore 2 C) 3 (2 ^ m))) ∧
        (RankTwoTheoremC (C ⧸ pCore 2 C) →
          K = residual H ∧ C.Normal ∧
          Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C) ∧
          ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 8) := by
  obtain ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,⟨hC,hKC,hlt,hn⟩,_⟩ :=
    LocalSieve.exists_escape_seed_embedding h.qtke h.sylow_normalizes hH hgen hY hescape
  refine ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,
    LocalSieve.seed_image_lt_container h.qtke hKH hH.1.1.2 hKL hR hY hescape C hC hKC,
    LocalSieve.not_solvableSylow_container h.qtke hKH hH.1.1.2 hKL hR hY hescape C hC hKC,
    fun _ hm => LocalSieve.not_binary_ternary_container h hH hgen c hKH hKL hR hY hescape C hC hKC hm,?_⟩
  intro hm
  have ht := LocalSieve.rankTwo_container_binaryTriality h hH hgen c hKH hKL hR hY hescape C hC hKC hm
  obtain ⟨he,hCn,hsection⟩ := LocalSieve.binaryTriality_residual_section h.qtke hKH hH.1.1.2
    hKL hKT hR hY hescape C hC hKC ht
  exact ⟨he,hCn,ht,hsection⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
