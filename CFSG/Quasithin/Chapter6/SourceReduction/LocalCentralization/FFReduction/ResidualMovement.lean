module
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.FFReduction.ExceptionalFixed
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.FFReduction.LeftThompson
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.FieldAction
public import GorensteinWalter.PSL2Cardinality
/-!
# The original Cartan residual moves the Sylow-center section

The residual has a PSL2(4) quotient and therefore its action image has order
divisible by five: the reduced component kernel is its actual two-core.
If it fixed the original omega-center section, it would fix the full
Sylow-fixed subspace. The faithful A7 extension's five-free fixed kernel
excludes this, in both the four-space and deleted-seven action.
Source: Aschbacher--Smith 5.1.13, printed p.637.
-/
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open ChapterB.InternalThompsonAction

private theorem five_dvd_range_of_two_kernel
    {A Q : Type*} [Group A] [Finite A] [Group Q]
    (f : A →* Q) (hk : IsPGroup 2 f.ker) (h5 : 5 ∣ Nat.card A) :
    5 ∣ Nat.card f.range := by
  have hnot : ¬5 ∣ Nat.card f.ker := by
    intro hh
    obtain ⟨n,hn⟩ := hk.exists_card_dvd_pow
    have := Nat.prime_five.dvd_of_dvd_pow (hh.trans hn)
    norm_num at this
  have hc := f.ker.card_mul_index
  rw [Subgroup.index_ker] at hc
  exact (Nat.prime_five.dvd_mul.mp (hc.symm ▸ h5)).resolve_left hnot

private theorem five_dvd_component_image
    {A : Type*} [Group A] [Finite A] (B U R : Subgroup A)
    [B.Normal] [U.Normal] [IsElementaryAbelian 2 U]
    [IsQuasisimple (B ⧸ pCore 2 B)]
    (hr : IsPReduced 2 U) (hz : center (B ⧸ pCore 2 B) = ⊥)
    (hm : ⁅U,B⁆ ≠ ⊥) (hRB : R ≤ B) (h5 : 5 ∣ Nat.card R) :
    5 ∣ Nat.card (R.map (actionMk U)) := by
  let q := actionMk U
  let i := inclusion hRB
  have he : (q.subgroupMap R).ker ≤ (pCore 2 B).comap i := by
    intro r hr'
    change i r ∈ pCore 2 B
    rw [←reduced_quasisimple_subgroupMap_ker U B hr hz hm]
    apply MonoidHom.mem_ker.mpr
    apply Subtype.ext
    change q (r : A) = 1
    exact congrArg Subtype.val (show (q.subgroupMap R) r = 1 from hr')
  have hk := (pCore_isPGroup (p := 2) (G := B)).comap_of_injective i
    (inclusion_injective hRB)
  have hh := five_dvd_range_of_two_kernel (q.subgroupMap R) (hk.to_le he) h5
  simpa only [MonoidHom.range_eq_top_of_surjective (q.subgroupMap R)
    (q.subgroupMap_surjective R),card_top] using hh

private theorem classified_fixed_kernel_five_free
    {A : Type*} [Group A] [Finite A] (P : Sylow 2 A) (B U : Subgroup A)
    [B.Normal] [U.Normal] [IsElementaryAbelian 2 U]
    [IsQuasisimple (B ⧸ pCore 2 B)]
    (hr : IsPReduced 2 U) (hz : center (B ⧸ pCore 2 B) = ⊥)
    (hm : ⁅U,B⁆ = U) (hne : U ≠ ⊥)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7))
    (hth : ⁅B,elementaryAbelianMaxJ (P : Subgroup A)⁆ = B)
    (hc : Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      ((action U).comp (offenderSubgroup (action U)).subtype)
      ((B.map (actionMk U)).subgroupOf (offenderSubgroup (action U)))))
    (F : Subgroup (A ⧸ centralizer (U : Set A)))
    (hF : ∀ f ∈ F, ∀ v ∈ fixedSpace (action U)
      (P.mapSurjective (QuotientGroup.mk'_surjective (centralizer (U : Set A)))),
      action U f v = v) : ¬5 ∣ Nat.card F := by
  let q := actionMk U
  let C := B.map q
  let N := offenderSubgroup (action U)
  let D := C.subgroupOf N
  let : N.Normal := offenderSubgroup_normal _
  let : C.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hCN : C ≤ N := by
    change B.map q ≤ N
    rw [←hth,map_commutator]
    exact (commutator_mono le_rfl (thompson_image_le P U)).trans (commutator_le_right _ _)
  let j := reducedQuasisimpleImageEquiv U B hr hz (by rwa [hm])
  have hz' : center D = ⊥ := by
    apply bot_unique
    intro d hd
    have hh : ((subgroupOfEquivOfLe hCN).trans j.symm) d ∈ center (B ⧸ pCore 2 B) :=
      MulEquivClass.apply_mem_center ((subgroupOfEquivOfLe hCN).trans j.symm) hd
    rw [hz] at hh
    exact ((subgroupOfEquivOfLe hCN).trans j.symm).injective
      (by simpa only [mem_bot,map_one] using hh)
  have hmove : ChapterB.QuasisimpleSource.moved ((action U).comp N.subtype) D = ⊤ := by
    change subspaceCommutator ((action U).comp N.subtype) ⊤ D = ⊤
    rw [Representation.BinaryOffender.subspaceCommutator_comp_map,
      map_subgroupOf_eq_of_le hCN]
    change subspaceCommutator (NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) ⊤ (B.map q) = ⊤
    rw [←NormalElementaryQuotient.commutatorSpace_eq U q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) B]
    apply top_unique
    intro v _
    change (v.toMul : A) ∈ ⁅U,B⁆
    rw [hm]
    exact v.toMul.property
  obtain ⟨c⟩ := hc
  exact ExceptionalFixed.sylow_fixedKernel_five_free (action U) (action_faithful U)
    C N hCN c (j.symm.trans e) hz' hmove
    (P.mapSurjective (QuotientGroup.mk'_surjective _)) F hF

/-- A residual of order divisible by five cannot fix the original Sylow-center
section of the fully moved, reduced, classified A7 module. -/
theorem classified_residual_moves
    {A : Type*} [Group A] [Finite A] (P : Sylow 2 A) (B U R : Subgroup A)
    [B.Normal] [U.Normal] [IsElementaryAbelian 2 U]
    [IsQuasisimple (B ⧸ pCore 2 B)]
    (hr : IsPReduced 2 U) (hz : center (B ⧸ pCore 2 B) = ⊥)
    (hUP : U ≤ (P : Subgroup A))
    (hm : ⁅U,B⁆ = U) (hne : U ≠ ⊥)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7))
    (hth : ⁅B,elementaryAbelianMaxJ (P : Subgroup A)⁆ = B)
    (hc : Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      ((action U).comp (offenderSubgroup (action U)).subtype)
      ((B.map (actionMk U)).subgroupOf (offenderSubgroup (action U)))))
    (hRB : R ≤ B) (h5 : 5 ∣ Nat.card R) :
    ⁅omegaOneCenterAmbient (P : Subgroup A) ⊓ U,R⁆ ≠ ⊥ := by
  intro he
  have hcentral : R ≤ centralizer
      ((omegaOneCenterAmbient (P : Subgroup A) ⊓ U : Subgroup A) : Set A) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rwa [commutator_comm]
  have hf := classified_fixed_kernel_five_free P B U hr hz hm hne e hth hc
    (R.map (actionMk U)) (by
      rintro _ ⟨r,hr',rfl⟩ v hv
      have hvC := (NormalElementaryQuotient.mem_fixedSpace_image U (actionMk U)
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) (P : Subgroup A) v).mp hv
      have hvZ : (v.toMul : A) ∈ omegaOneCenterAmbient (P : Subgroup A) := by
        apply (mem_omegaOneCenterAmbient_iff _ _).mpr
        exact ⟨hUP v.toMul.property,
          elemPow_eq_one_of_isElementaryAbelian (p := 2) _ v.toMul.property,
          fun p hp => hvC p hp⟩
      have hvR : (v.toMul : A) ∈ centralizer (R : Set A) :=
        (le_centralizer_iff.mp hcentral) ⟨hvZ,v.toMul.property⟩
      exact (NormalElementaryQuotient.mem_fixedSpace_image U (actionMk U)
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) R v).mpr hvR
          ⟨actionMk U r,mem_map_of_mem _ hr'⟩)
  exact hf (five_dvd_component_image B U R hr hz (by rwa [hm]) hRB h5)

namespace LocalOmega
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {K R : Subgroup G}

/-- The same original residual moves the actual omega-center section. -/
theorem residual_moves (hE : IsEvenCharacteristicAt T)
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hm : LocalExceptionalQuotient K)
    (hU : localOmegaModule T K ∈ reducedFamily (K ⊔ (T : Subgroup G)))
    (hne : localOmegaModule T K ≠ ⊥)
    (hth : ⁅K,elementaryAbelianMaxJ (T : Subgroup G)⁆ = K)
    (ha : ClassifiedAction hU)
    (he : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (hRK : R ≤ K) (h5 : 5 ∣ Nat.card R) :
    ⁅omegaOneCenterAmbient (T : Subgroup G) ⊓ localOmegaModule T K,R⁆ ≠ ⊥ := by
  let M := K ⊔ (T : Subgroup G)
  let B := K.subgroupOf M
  let U := (localOmegaModule T K).subgroupOf M
  let P := T.subtype (show (T : Subgroup G) ≤ M from le_sup_right)
  have hr : IsPReduced 2 U := reduced_internal hU
  let := hr.normal
  let := hr.elementary
  let : B.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hn)
  let e := QuotientGroup.congr (pCore 2 B) (pCore 2 K)
    (subgroupOfEquivOfLe (show K ≤ M from le_sup_left))
    (pCore_map_iso 2 (subgroupOfEquivOfLe (show K ≤ M from le_sup_left)))
  let := quotient_quasisimple hK hm
  let : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv e.symm
  have hz : center (B ⧸ pCore 2 B) = ⊥ := by
    apply bot_unique
    intro b hb
    have hh : e b ∈ center (K ⧸ pCore 2 K) := MulEquivClass.apply_mem_center e hb
    rw [quotient_center hK hm] at hh
    exact e.injective (by simpa only [mem_bot,map_one] using hh)
  have hmove : ⁅U,B⁆ = U := by
    apply map_injective M.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hU.1,
      map_subgroupOf_eq_of_le (show K ≤ M from le_sup_left),full_movement hE hK hn]
  have hPmap : (P : Subgroup M).map M.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le le_sup_right
  have hth' : ⁅B,elementaryAbelianMaxJ (P : Subgroup M)⁆ = B := by
    apply map_injective M.subtype_injective
    rw [map_commutator,←elementaryAbelianMaxJ_map_injective M.subtype M.subtype_injective,
      hPmap,map_subgroupOf_eq_of_le (show K ≤ M from le_sup_left),hth]
  have hUT : localOmegaModule T K ≤ (T : Subgroup G) :=
    (le_normalizer_iff_commutator_le_left.mp (le_normalizer_conjugateSpanBy _ _)).trans
      (span_elementary_le_sylow T K hE hK hn).2
  have hnon : U ≠ ⊥ := by
    intro he'
    apply hne
    apply bot_unique
    intro x hx
    have hh : (⟨x,hU.1 hx⟩ : M) ∈ U := hx
    exact mem_bot.mpr (congrArg Subtype.val (mem_bot.mp (he'.le hh)))
  have hh := classified_residual_moves P B U (R.subgroupOf M) hr hz
    (fun _ hx => hUT hx) hmove hnon (e.trans he) hth' ha.2
    (comap_mono hRK) (by rwa [Nat.card_congr
      (subgroupOfEquivOfLe (hRK.trans (show K ≤ M from le_sup_left))).toEquiv])
  intro hc
  apply hh
  apply (map_injective M.subtype_injective)
  rw [map_commutator,Subgroup.map_inf _ _ M.subtype M.subtype_injective,
    ←omegaOneCenterAmbient_map_injective M.subtype M.subtype_injective,hPmap,
    map_subgroupOf_eq_of_le hU.1,
    map_subgroupOf_eq_of_le (hRK.trans (show K ≤ M from le_sup_left)),Subgroup.map_bot,hc]
end LocalOmega

private theorem five_dvd_residual_of_linear_four
    {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 4) :
    5 ∣ Nat.card (residual H) := by
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
    (by simpa [Nat.card_eq_fintype_card] using hcard)
  have hq : Nat.card ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) = 60 := by
    rw [Nat.card_congr e.toEquiv,
      ←Nat.card_congr (BenderSuzuki.ZD.Linear.sl2QuotientEquiv F).toEquiv,
      GorensteinWalter.sl2_card_formula,hcard]
    norm_num
  have hp : 5 ∣ Nat.card (pResidual 2 H) :=
    (by decide : 5 ∣ 60).trans (hq ▸ card_quotient_dvd_card (pCore 2 (pResidual 2 H)))
  rwa [card_map_of_injective H.subtype_injective]

/-- The complete literal FF configuration in the original Cartan argument.
Only the independently owned earlier Baumann input remains explicit. -/
theorem localCartan_ffReduction_source
    {G : Type*} [Group G] [Finite G]
    (hbaum : RankOneBaumannNormalizerControl G) : LocalCartanFFReduction G := by
  intro T L W n h H hH _ A B _ Y hY X D d hXC
  obtain ⟨K,hXK,hK,hn,hm,_,hth,hU,hne,hspan,ha⟩ :=
    localCartan_maximal_thompson_source hbaum h hH hY d hXC
  obtain ⟨he,hcard,hi⟩ := LocalOmega.action_consequences
    (h.qtke.evenCharacteristic T) hK.1 hn hm hU hne hth ha
  have hR := LocalOmega.residual_moves (h.qtke.evenCharacteristic T) hK.1 hn hm
    hU hne hth ha he.some (d.residual_le.trans hXK)
    (five_dvd_residual_of_linear_four H d.residual_linear)
  have hZ : ¬ omegaOneCenterAmbient (T : Subgroup G) ≤ (center H).map H.subtype := by
    intro hc
    apply hR
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro z hz r hr
    obtain ⟨c,hc,rfl⟩ := hc hz.1
    have hrH : r ∈ H := (map_subtype_le (pResidual 2 H)) hr
    exact congrArg H.subtype ((mem_center_iff.mp hc) ⟨r,hrH⟩)
  refine ⟨K,⟨hXK,hK,hn,he,hth,h.thompson_commutator_of_noncentral_omega hH hZ,
    hU,hcard,hi,hspan,?_,hR⟩⟩
  exact LocalOmega.fixed_eq_bot_of_irreducible T K hK.1 (fun hc => hXC (hXK.trans hc)) hi

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
