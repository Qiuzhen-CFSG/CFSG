module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalOddNormalizer.BinaryG2Application
public import CFSG.Quasithin.Chapter4.Section04.OddActorComponents.OddCentralizer
public import Theory.GroupTheory.GeneralizedFitting.OddComponentCentralizer
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.Quasithin.CoprimeRank
public import Theory.ElementaryAbelian.PrimeRankCard

/-!
# The normal component of the original unitary odd normalizer

The original binary G₂ action is inner on the selected component. Residual
uniqueness kills the module's projection to its component centralizer and
then every involution of that centralizer. The component is therefore normal
and contains both the whole chosen module and the perfect fixed residual.
Its odd center preserves the module's six-dimensional rank.

Source: Aschbacher--Smith 4.4.10--11, printed p.621, applied in 13.3.16.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup Theory.GroupTheory Chapter4 Chapter4.Section04 ChapterE
open OriginalPlaneCentralizers Chapter12.Section02
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

private theorem original_card_V (s : Context T L V) : Nat.card V = 64 := by
  have hd : Module.finrank (ZMod 2) (Additive V) = 6 :=
    s.coordinates.finrank_eq.trans (Atlas.G2.Natural.finrank_space (ZMod 2))
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
  rw [Nat.card_zmod, hd] at hc
  exact hc

private theorem original_faithful_core (s : Context T L V) :
    L ⊓ centralizer (V : Set G) ≤ L.pCoreIn 2 := by
  let : IsSimpleGroup Atlas.G2.Natural.BinaryNormalizer.Derived :=
    Atlas.G2.isSimple_commutator_binary
  let : IsSimpleGroup (L ⧸ pCore 2 L) := s.quotient.isSimpleGroup
  have hc := congrArg (map L.subtype) (s.chosen.centralizer_eq_core_of_simple
    s.quotient.isSimpleGroup)
  exact (show L ⊓ centralizer (V : Set G) = L.pCoreIn 2 by
    simpa only [pCoreIn, subgroupOf_map_subtype, inf_comm] using hc).le


/-- The original selected component is normal and contains the whole module
and fixed residual. The genuine uniqueness premise is discharged in the
original-flag application, using the completed relative-Sylow J₄ exclusion. -/
theorem unitary_original_normal_component
    (s : Context T L V) (A : Subgroup G) [IsMulCommutative A]
    (hne : A ≠ ⊥) (hAN : A ≤ normalizer (L : Set G))
    (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2) (hodd : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    ∃ K : Subgroup (normalizer (A : Set G)),
      IsComponent (normalizer (A : Set G)) K ∧ K.Normal ∧
      ⁅K,V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
      ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
      pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
      V ≤ K.map (normalizer (A : Set G)).subtype ∧
      oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
      centralizer (K : Set (normalizer (A : Set G))) =
        pPrimeCore 2 (normalizer (A : Set G)) ∧
      Odd (Nat.card (center K)) ∧ 6 ≤ primeRank 2 (K ⧸ center K) := by
  have h12 := (unitary_original_hypothesis1223 s.hypothesis s.maximal s.quotient).toHypothesis1221
  have hfaith := original_faithful_core s
  obtain ⟨K,hK,hm,houtK,hcore,hmodel,_,_⟩ :=
    chosen_oddNormalizer_exists_theoremB_component
      (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
      (fun X _ _ => ChapterA.Section02.theoremB_knownSimple (G := X))
      h12 s.chosen (original_card_V s) A hne hAN hcomm hodd hAV hu hout
  have hi := chosen_oddNormalizer_inner_of_binary_derived_outer_section
    h12 s.chosen hfaith s.actor A hAN hcomm hodd hAV K hK hmodel
  have hv := chosen_oddNormalizer_module_le_of_component_inner_action
    h12 s.chosen A hAN hcomm hodd hAV hu K houtK hi
  have ho := chosen_oddNormalizer_component_centralizer_odd
    h12 s.chosen hfaith A hAN hcomm hodd hAV hu hout K hK houtK hv
  let N := normalizer (A : Set G)
  let R := oddActorResidual L A
  have hRN : R ≤ N := ((oddActorResidual_le L A).trans inf_le_right).trans
    (Subgroup.centralizer_le_normalizer _)
  let : Group.IsPerfect R := oddActorResidual_isPerfect L A
  let : Group.IsPerfect (R.subgroupOf N) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hRN).symm.toMonoidHom)
    (subgroupOfEquivOfLe hRN).symm.surjective
  have hr : R ≤ K.map N.subtype := by
    have hh := map_mono (f := N.subtype)
      (hK.perfect_actor_le_of_odd_centralizer ho (R.subgroupOf N) hi)
    rwa [map_subgroupOf_eq_of_le hRN] at hh
  have hz : Odd (Nat.card (center K)) := by
    have hZC : (center K).map K.subtype ≤ centralizer (K : Set N) := by
      rintro _ ⟨z,hz,rfl⟩ y hy
      exact congrArg K.subtype (mem_center_iff.mp hz ⟨y,hy⟩)
    have hh := ho.of_dvd_nat (card_dvd_of_le hZC)
    rwa [card_map_of_injective K.subtype_injective] at hh
  have hVR : primeRank 2 V ≤ primeRank 2 K := by
    have hh := primeRank_mono 2 hv
    rwa [← primeRank_equiv 2 (K.equivMapOfInjective N.subtype N.subtype_injective)] at hh
  have hrank := hVR.trans (primeRank_le_of_coprime_ker 2 (QuotientGroup.mk' (center K)) (by
    rw [QuotientGroup.ker_mk']; exact hz.coprime_two_left))
  have hrV : primeRank 2 V = 6 := by
    have hh := IsElementaryAbelian.log_card_eq_primeRank (p := 2) V
    rw [original_card_V s] at hh
    exact hh.symm
  exact ⟨K,hK,hK.normal_of_odd_centralizer ho,hm,houtK,hcore,hmodel,hv,hr,
    hK.centralizer_eq_oddCore_of_odd_centralizer ho,hz,hrV ▸ hrank⟩

/-- The fixed residual embeds in the component central quotient. Its central
kernel is simultaneously a two-group (the simple core quotient is centerless)
and of odd order (the component centralizer has odd order). -/
theorem unitary_original_residual_embedding
    (s : Context T L V) (A : Subgroup G)
    (hAN : A ≤ normalizer (L : Set G)) (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2)
    (hodd : Odd (Nat.card A)) (hAV : A ≤ centralizer (V : Set G))
    (K : Subgroup (normalizer (A : Set G)))
    (hr : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype)
    (hz : Odd (Nat.card (center K))) :
    let R := oddActorResidual L A
    let i : R →* K := (K.equivMapOfInjective (normalizer (A : Set G)).subtype
      (normalizer (A : Set G)).subtype_injective).symm.toMonoidHom.comp (inclusion hr)
    let j := (QuotientGroup.mk' (center K)).comp i
    Function.Injective j ∧ 387072 ∣ Nat.card j.range := by
  dsimp only
  let R := oddActorResidual L A
  let N := normalizer (A : Set G)
  let i : R →* K := (K.equivMapOfInjective N.subtype N.subtype_injective).symm.toMonoidHom.comp
    (inclusion hr)
  let j := (QuotientGroup.mk' (center K)).comp i
  have hi : Function.Injective i :=
    (K.equivMapOfInjective N.subtype N.subtype_injective).symm.injective.comp
      (inclusion_injective hr)
  have h12 := (unitary_original_hypothesis1223 s.hypothesis s.maximal s.quotient).toHypothesis1221
  obtain ⟨e,he⟩ := chosen_oddActorResidual_quotient h12 s.chosen A hAN hcomm hodd hAV
  let a := e.trans s.quotient
  let : Group.IsPerfect R := oddActorResidual_isPerfect L A
  let : Group.IsPerfect (R ⧸ pCore 2 R) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  let : IsSimpleGroup Atlas.G2.Natural.BinaryNormalizer.Derived := Atlas.G2.isSimple_commutator_binary
  let : IsSimpleGroup (R ⧸ pCore 2 R) := a.isSimpleGroup
  have hzR : center (R ⧸ pCore 2 R) = ⊥ :=
    (inferInstance : (center (R ⧸ pCore 2 R)).Normal).eq_bot_or_eq_top.resolve_right
      (fun ht => Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp ht))
  have hk : j.ker ≤ pCore 2 R := by
    intro x hx
    have hc : i x ∈ center K := (QuotientGroup.eq_one_iff _).mp hx
    have hcx : x ∈ center R := mem_center_iff.mpr (fun y => hi (by
      simpa only [map_mul] using mem_center_iff.mp hc (i y)))
    have hq : QuotientGroup.mk' (pCore 2 R) x ∈ center (R ⧸ pCore 2 R) :=
      mem_center_iff.mpr (by
        intro y
        obtain ⟨z,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 R) y
        simpa only [map_mul] using congrArg (QuotientGroup.mk' (pCore 2 R))
          (mem_center_iff.mp hcx z))
    have hxq : x ∈ (QuotientGroup.mk' (pCore 2 R)).ker := by
      simpa only [hzR,mem_bot,MonoidHom.mem_ker] using hq
    rwa [QuotientGroup.ker_mk'] at hxq
  have hkodd : Odd (Nat.card j.ker) := by
    let k : j.ker →* center K := (i.comp j.ker.subtype).codRestrict _
      (fun x => (QuotientGroup.eq_one_iff _).mp x.property)
    exact hz.of_dvd_nat (card_dvd_of_injective k
      (fun x y h => Subtype.ext (hi (congrArg Subtype.val h))))
  have hki : Function.Injective j := by
    apply (MonoidHom.ker_eq_bot_iff j).mp
    apply card_eq_one.mp
    obtain ⟨n,hn⟩ := (pCore_isPGroup.to_le hk).exists_card_eq
    have hn0 : n = 0 := by
      by_contra hn0
      exact (Nat.not_even_iff_odd.mpr hkodd) (hn ▸ even_two.pow_of_ne_zero hn0)
    simpa only [hn0,pow_zero] using hn
  refine ⟨hki,?_⟩
  have hVcore := (chosen_oddActorResidual_cover h12 s.chosen A hAN hcomm hodd hAV).2.2.1
  have h64 : 64 ∣ Nat.card (pCore 2 R) := by
    have hh := card_dvd_of_le hVcore
    change Nat.card V ∣ Nat.card ((pCore 2 R).map R.subtype) at hh
    rwa [original_card_V s,card_map_of_injective R.subtype_injective] at hh
  have h6048 : Nat.card (R ⧸ pCore 2 R) = 6048 := by
    rw [Nat.card_congr a.toEquiv]
    exact Atlas.G2.LieAutomorphismExtensions.card_binaryDerived
  have hd : 387072 ∣ Nat.card R := by
    have hh := Nat.mul_dvd_mul h64 (dvd_refl 6048)
    have hc : Nat.card R = Nat.card (pCore 2 R) * 6048 := by
      rw [← (pCore 2 R).card_mul_index, index_eq_card, h6048]
    rwa [←hc] at hh
  simpa only [Nat.card_congr (MonoidHom.ofInjective hki).toEquiv] using hd

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
