module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.OddCentralizers.NormalizerFourPlacement
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.ParabolicRestrictions

/-!
# Degree-four pushing up has an escaping constrained component

Reciprocal containment would make the original L an index-two-normalizer
C-component. Its original L₄(2) quotient has cubic rank two and trivial
center, forcing relative normality and contradicting that index.

Every ordinary component in the resulting C.2.8 witness contains the whole
original doubled orbit, which embeds in its central quotient with rank eight.
The actual residual's local image leaves Sp₆(2) and J₄. Strong quasithinness
excludes Sp₆(2); nonsingular centralizer control excludes the full central
two-cover of J₄. Thus failure of residual uniqueness supplies an actual
escaping constrained component. Its remaining C.2.7 module alternatives
are not assumed excluded.

Source: Aschbacher--Smith 4.2.5--13, 4.4.6 and 12.1.9(1), pp.609--612,620,793.
The literal odd-normalizer obstruction consumes this in the Chapter12 adapter.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter12.Section01.DoubleNaturalSource
open Chapter4.Section02.RankOneReciprocalEscape
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)

private theorem normal_of_binaryFour_core_quotient
    {B : Subgroup G} (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (hB : B.IsCComponent)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 8)) : B.Normal := by
  let Q := alternatingGroup (Fin 8)
  let : IsSimpleGroup Q := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (B ⧸ pCore 2 B) := e.isSimpleGroup
  have hz : center (B ⧸ pCore 2 B) = ⊥ := by
    rcases (inferInstance : (center (B ⧸ pCore 2 B)).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · let : Group.IsPerfect (B ⧸ pCore 2 B) :=
        Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
      exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp ht)).elim
  let : Group.IsPerfect (B ⧸ pCore 2 B) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let : IsQuasisimple (B ⧸ pCore 2 B) := {
    simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup }
  have hr : 2 ≤ primeRank 3 (B ⧸ pCore 2 B) := by
    rw [primeRank_congr 3 (e)]
    exact alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)
  exact hB.normal_of_coprime_core_center_primeRank (by decide : Odd 3)
    (by rw [hz]; simp) hr (hG.stronglyQuasithin 3 (by decide) (by decide))


include D h in
theorem doubledFour_pushingUp_escape (B : DoubledBranch T L V 4)
    {A J H U : Subgroup G} (hw : Witness L V A J H U) :
    ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ (normalizer (L : Set G)).subgroupOf H := by
  intro hf
  rcases hw with ⟨hJ,hpush,hH,hJH,hstrict,hVJ,hc,hcover,hn,hmove,hVF,⟨e,he⟩,hrest⟩
  let M := normalizer (L : Set G)
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect h.maximal_faithful.1.1
  let := h.quasisimple
  let : IsQuasisimple (F ⧸ pCore 2 F) := IsQuasisimple.of_mulEquiv e.symm
  have hM : IsMaximalTwoLocal M := (D.doubledNormalizer_unique h).1
  have hne : H ≠ M := fun he => hstrict.ne (by rw [he,inf_idem])
  have hs := h.simpleQTKE.twoLocal_sqtk hM.1
  have hd := reciprocal_setup hH hM hs hne hf
  have hFL : F = L := residual_eq_of_fitting_contained L.le_normalizer le_rfl hH hM hs hne hcover hf
  obtain ⟨hcomp,hnorm,hi⟩ := index_two_of_fitting_contained hc hn hstrict hd.1 hf
  have hLH : L ≤ H := hFL ▸ (map_subtype_le (solvableResidual (L ⊓ H : Subgroup G))).trans inf_le_right
  let eL : L.subgroupOf H ≃* L := subgroupOfEquivOfLe hLH
  let q := (QuotientGroup.congr _ _ eL (pCore_map_iso 2 eL)).trans
    (B.component.trans doubledFour_linearEquiv)
  have hcompL : (L.subgroupOf H).IsCComponent := hFL ▸ hcomp
  have hnormL : normalizer (L.subgroupOf H : Set H) = M.subgroupOf H := hFL ▸ hnorm
  let : (L.subgroupOf H).Normal := normal_of_binaryFour_core_quotient hc.sqtk hcompL q
  rw [normalizer_eq_top] at hnormL
  rw [←hnormL,index_top] at hi
  norm_num at hi

include D h in
theorem doubledFour_pushingUp_no_ordinary_of_many (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4)
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWU : componentOrbit V (T : Subgroup G) ≤ U)
    (K : Subgroup H) (hK : IsComponent H K) :
    False := by
  rcases hw with ⟨hJ,hpush,hH,hJH,hstrict,hVJ,hc,hcover,hN,hmove,hVF,⟨e,he⟩,hrest⟩
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let Kg := K.map H.subtype
  have hFH : F ≤ H := (map_subtype_le _).trans inf_le_right
  have hFL : F ≤ L := (map_subtype_le _).trans inf_le_left
  have hFK : F ≤ Kg := by
    have hh := map_mono (f := H.subtype) (hc.ordinary_component_contains_original K hK)
    rwa [map_subgroupOf_eq_of_le hFH] at hh
  have hUK : U ≤ Kg := by
    have hh := map_mono (f := H.subtype) ((hc.ordinary_module_placement K hK).1.trans inf_le_right)
    rwa [map_subgroupOf_eq_of_le (hc.module_le.trans (conjugateSpanBy_le
      (hc.component_le.trans hc.local_le) (hc.local_le.trans H.le_normalizer)))] at hh
  have hWK := hWU.trans hUK
  let : Group.IsPerfect F := Group.IsPerfect.map _
  let : IsQuasisimple K := hK.2
  let q : Kg ≃* K := (K.equivMapOfInjective H.subtype H.subtype_injective).symm
  let z := centerQuotientCongr q
  have hkg := hc.sqtk.subgroup K
  have hmodel := ChapterA.Section02.quasisimple_centralQuotient_theoremBModel
    ChapterA.Section02.theoremA_knownSimple ChapterA.Section02.theoremB_knownSimple
    hkg.stronglyQuasithin.quasithin hkg.isKGroup
  have hr : 8 ≤ primeRank 2 (K ⧸ center K) := by
    have hi := D.doubledOrbit_cover_quotient_injective h B hWK hFK hcover
    let W := componentOrbit V (T : Subgroup G)
    let := D.doubledOrbit_elementary h
    let : IsElementaryAbelian 2 (⊤ : Subgroup W) :=
      IsElementaryAbelian.of_injective (⊤ : Subgroup W).subtype (⊤ : Subgroup W).subtype_injective
    have hcW : Nat.card W = 2 ^ 8 := by
      have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W)
      rw [Nat.card_congr Additive.toMul,B.finrank_eq,Nat.card_zmod] at hh
      exact hh
    have hv : 8 ≤ primeRank 2 W := IsElementaryAbelian.primeRank_ge_of_card
      (⊤ : Subgroup W) (by simpa only [Nat.card_congr (topEquiv : (⊤ : Subgroup W) ≃* W).toEquiv] using hcW)
    have hh := hv.trans (Theory.GroupTheory.primeRank_le_of_injective 2 _ hi)
    rwa [primeRank_congr 2 z] at hh
  let eFour := B.component.trans doubledFour_linearEquiv
  have hlocal := (D.doubledFour_placed_local hFK hVF hFL hmove (e.trans eFour)).of_mulEquiv z
  have hZK : IsPGroup 2 (center K) := by
    rw [IsQuasisimple.center_eq_pCore (hK.1.pPrimeCore_eq_bot hc.oddCore_eq_bot K)]
    exact pCore_isPGroup
  rcases hlocal.remaining_models hmodel hr with hs | hj
  · have hthree := ChapterA.Section02.EvenLie.symplectic_six_binary_three_rank hs
    rw [primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (center K) hZK] at hthree
    have := hkg.stronglyQuasithin 3 (by decide) (by decide)
    omega
  · obtain ⟨ej⟩ := hj
    have hZ : IsPGroup 2 (center Kg) := hZK.of_equiv (centerCongr q.symm)
    exact D.doubledOrbit_no_janko_two_cover_of_many h B hmany Kg hWK hZ (z.trans ej)
      (D.doubledOrbit_cover_quotient_injective h B hWK hFK hcover)

include D h in
/-- The remaining pushing-up obstruction is a genuine constrained component,
with the original whole orbit, residual, radical and C.2.8 witness retained. -/
theorem doubledFour_pushingUp_constrained_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) (A : Subgroup G)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G))
    (ho : Odd (Nat.card A))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    ∃ J H U : Subgroup G, Witness L V A J H U ∧
      componentOrbit V (T : Subgroup G) ≤ U ∧
      componentOrbit V (T : Subgroup G) ≤ J.pCoreIn 2 ∧
      ∃ K : Subgroup H, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
        ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H ∧
        generalizedFitting K = pCore 2 K := by
  obtain ⟨J,H,U,hw,hWU,hWJ,_⟩ := D.doubledOrbit_pushingUp_full_configuration h B A hA ho hnot
  have hc := hw.2.2.2.2.2.2.1
  have hf := D.doubledFour_pushingUp_escape h B hw
  have hf' : ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H :=
    fun hh => hf (hh.trans (comap_mono inf_le_right))
  obtain ⟨K,hK,hq,hout,hFK,hcases⟩ := hc.ordinary_or_constrained_escape hf'
  refine ⟨J,H,U,hw,hWU,hWJ,K,hK,hq,hout,?_⟩
  exact hcases.resolve_left (D.doubledFour_pushingUp_no_ordinary_of_many h hmany B hw hWU K)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
