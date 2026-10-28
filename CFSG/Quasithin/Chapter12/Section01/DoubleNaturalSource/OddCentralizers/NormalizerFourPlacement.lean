module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.OddCentralizers.NormalizerFourLocal

/-!
# The original degree-four residual in its containing component

The original L₄(2) quotient descends through the full covering center with
only a two-group kernel. Its perfect image retains cubic rank two and order
divisible by 105. The original moved seed supplies the normalized nontrivial
two-subgroup. This applies both to the odd fixed residual and to the literal
intersection residual in the C.2.8 pushing-up witness.

For an inner odd-normalizer component, the full doubled orbit gives rank
eight. The complete local-model exclusions leave Sp₆(2) or J₄, and original
nonsingular centralizer control excludes the latter with its odd center
intact. The remaining symplectic and outer cases are not asserted here.
Source: Aschbacher--Smith 4.4.10--12 and 12.1.9(1), pp.621--623,793.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter12.Section01.DoubleNaturalSource
open Chapter4.Section02.RankOneReciprocalEscape
open BinaryLinear.OuterCyclic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)

private abbrev Four := alternatingGroup (Fin 8)
/-- The canonical projective and exceptional identifications of the residual quotient. -/
def doubledFour_linearEquiv : LinearGroup 4 ≃* alternatingGroup (Fin 8) :=
  (projectiveEquivLinear (by decide : 0 < 4)).symm.trans
    Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8

private theorem four_card : Nat.card Four = 20160 := by
  rw [nat_card_alternatingGroup,Nat.card_fin]
  decide

private theorem four_center : center Four = ⊥ := by
  let : IsSimpleGroup Four := alternatingGroup.isSimpleGroup (by simp)
  rcases (inferInstance : (center Four).Normal).eq_bot_or_eq_top with hb | ht
  · exact hb
  · exact (Group.IsPerfect.not_isMulCommutative Four (center_eq_top_iff.mp ht)).elim

private theorem central_kernel_le_twoCore
    {F K : Type*} [Group F] [Finite F] [Group K]
    (e : (F ⧸ pCore 2 F) ≃* Four)
    (j : F →* K) (hj : Function.Injective j) :
    ((QuotientGroup.mk' (center K)).comp j).ker ≤ pCore 2 F := by
  let π : F →* Four := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 F))
  have hs : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  intro x hx
  have hc : j x ∈ center K := (QuotientGroup.eq_one_iff _).mp hx
  have hcx : x ∈ center F := mem_center_iff.mpr (fun y => hj (by
    simpa only [map_mul] using mem_center_iff.mp hc (j y)))
  have hcπ : π x ∈ center Four := mem_center_iff.mpr (by
    intro y
    obtain ⟨z,rfl⟩ := hs y
    simpa only [map_mul] using congrArg π (mem_center_iff.mp hcx z))
  have he : π x = 1 := by simpa only [four_center,mem_bot] using hcπ
  apply (QuotientGroup.eq_one_iff x).mp
  exact e.injective (he.trans (map_one e).symm)


include D in
/-- A moved seed in a placed L₄(2) residual supplies its literal local image. -/
theorem doubledFour_placed_local
    {F K : Subgroup G} [Group.IsPerfect F]
    (hFK : F ≤ K) (hVF : V ≤ F) (hFL : F ≤ L)
    (hm : V = ⁅V,F⁆)
    (e : (F ⧸ pCore 2 F) ≃* alternatingGroup (Fin 8)) :
    FourComponentLocalData (K ⧸ center K) := by
  let j := inclusion hFK
  let f := (QuotientGroup.mk' (center K)).comp j
  let W := V.subgroupOf F
  have hFW : F ≤ normalizer (V : Set G) := hFL.trans D.normalizes
  have hn : (⊤ : Subgroup F) ≤ normalizer (W : Set F) := by
    intro x _ y
    exact hFW x.property (y : G)
  let := D.elementary
  have hP : IsPGroup 2 (W.map f) := (IsElementaryAbelian.isPGroup 2 V).comap_subtype.map f
  have hne : W.map f ≠ ⊥ := by
    intro hb
    have hk := (map_eq_bot_iff W).mp hb
    have hc : V ≤ centralizer (F : Set G) := by
      intro v hv y hy
      have hz : j (⟨v,hVF hv⟩ : F) ∈ center K :=
        (QuotientGroup.eq_one_iff _).mp (hk hv)
      have he : (⟨y,hy⟩ : F) * ⟨v,hVF hv⟩ = ⟨v,hVF hv⟩ * (⟨y,hy⟩ : F) :=
        (inclusion_injective hFK) (by
          simpa only [map_mul] using mem_center_iff.mp hz (j ⟨y,hy⟩))
      exact congrArg Subtype.val he
    exact D.ne_bot (hm.trans (commutator_eq_bot_iff_le_centralizer.mpr hc))
  have hk : IsPGroup 2 f.ker := pCore_isPGroup.to_le
    (central_kernel_le_twoCore e j (inclusion_injective hFK))
  have hr : 2 ≤ primeRank 3 F := by
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 F) pCore_isPGroup,
      primeRank_equiv 3 (e)]
    exact alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)
  have hr' : primeRank 3 f.range = primeRank 3 F := by
    rw [MonoidHom.range_eq_map f]
    exact (ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide : Odd 3) f hk
      (⊤ : Subgroup F)).trans (primeRank_equiv 3 Subgroup.topEquiv)
  have h105F : 105 ∣ Nat.card F := by
    have hd : 105 ∣ Nat.card (F ⧸ pCore 2 F) := by
      rw [Nat.card_congr e.toEquiv,four_card]
      decide
    exact hd.trans (card_quotient_dvd_card _)
  have h105 : 105 ∣ Nat.card f.range := by
    have hcount : Nat.card f.ker * Nat.card f.range = Nat.card F := by
      rw [←index_ker]
      exact f.ker.card_mul_index
    obtain ⟨n,hn⟩ := hk.exists_card_eq
    have hc : Nat.Coprime 105 (Nat.card f.ker) := by
      rw [hn]
      exact (by decide : Nat.Coprime 105 2).pow_right n
    exact hc.dvd_of_dvd_mul_left (hcount.symm ▸ h105F)
  refine ⟨f.range,W.map f,Group.IsPerfect.range f,hr' ▸ hr,hP,hne,?_,map_le_range f W,h105⟩
  simpa only [←MonoidHom.range_eq_map] using
    (map_mono (f := f) hn).trans (W.le_normalizer_map f)

include D h in
/-- The literal odd fixed residual supplies the degree-four local configuration. -/
theorem doubledFour_oddNormalizer_placed_local (B : DoubledBranch T L V 4)
    (A : Subgroup G)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G))
    (ho : Odd (Nat.card A))
    (K : Subgroup (normalizer (A : Set G)))
    (hFK : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype) :
    FourComponentLocalData (K ⧸ center K) := by
  let F := oddActorResidual L A
  obtain ⟨_,hm,hVF,_⟩ := D.doubledOrbit_oddActorResidual_cover h A hA ho
  obtain ⟨e,_⟩ := D.doubledOrbit_oddActorResidual_marking h B A hA ho
  let : Group.IsPerfect F := oddActorResidual_isPerfect L A
  let q := (K.equivMapOfInjective (normalizer (A : Set G)).subtype
    (normalizer (A : Set G)).subtype_injective).symm
  have hmove : V = ⁅V,F⁆ := by
    obtain ⟨_,hm,_,_⟩ := chosen_oddActorResidual_cover h.toHypothesis1221 D A
      (hA.trans inf_le_left)
      ((le_sectionCentralizer_iff A L).mp
        (hA.trans (D.doubledOrbit_relative_centralizer_le_sectionCentralizer h))).2 ho
      ((hA.trans inf_le_right).trans (centralizer_le (le_componentOrbit V T)))
    exact hm
  have hV : V ≤ F := (le_componentOrbit V T).trans (hVF.trans (pCoreIn_le 2 F))
  exact (D.doubledFour_placed_local hFK hV ((oddActorResidual_le L A).trans inf_le_left)
    hmove (e.trans doubledFour_linearEquiv)).of_mulEquiv (centerQuotientCongr q)

include D h in
/-- A placed inner odd-normalizer component has the actual binary Sp₆ quotient.
The J₄ alternative is excluded by the already proved nonsingular control. -/
theorem doubledFour_oddNormalizer_inner_symplectic_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) (A : Subgroup G)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G))
    (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G))
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K)
    (houtK : ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G))
    (hi : (oddActorResidual L A).subgroupOf (normalizer (A : Set G)) ≤
      K ⊔ centralizer (K : Set (normalizer (A : Set G))))
    (hm : ChapterA.Section02.IsTheoremBModel (K ⧸ center K)) :
    K.Normal ∧ componentOrbit V (T : Subgroup G) ≤ K.map (normalizer (A : Set G)).subtype ∧
      oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
      ClassicalGroup.IsPSp (K ⧸ center K) 3 2 := by
  obtain ⟨hn,hw,hf,hc,hr⟩ :=
    D.doubledOrbit_oddNormalizer_inner_placement h B A hA ho hu hout K hK houtK hi
  rcases (D.doubledFour_oddNormalizer_placed_local h B A hA ho K hf).remaining_models hm hr with
    hs | hj
  · exact ⟨hn,hw,hf,hs⟩
  · obtain ⟨e⟩ := hj
    let N := normalizer (A : Set G)
    have hZC : (center K).map K.subtype ≤ centralizer (K : Set N) := by
      rintro _ ⟨z,hz,rfl⟩ y hy
      exact congrArg K.subtype (mem_center_iff.mp hz ⟨y,hy⟩)
    have hoC : Odd (Nat.card (centralizer (K : Set N))) := by
      rw [hc]
      exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
    have hoZ : Odd (Nat.card (center K)) := by
      have hh := hoC.of_dvd_nat (card_dvd_of_le hZC)
      rwa [card_map_of_injective K.subtype_injective] at hh
    exact (D.doubledOrbit_no_janko_odd_cover_of_many h B hmany (N.subtype.comp K.subtype)
      (N.subtype_injective.comp K.subtype_injective)
      (by simpa only [MonoidHom.range_comp,range_subtype] using hw) hoZ e).elim

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
