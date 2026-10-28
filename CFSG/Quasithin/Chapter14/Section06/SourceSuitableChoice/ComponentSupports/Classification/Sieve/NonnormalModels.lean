module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Classification.Sieve.NormalModels
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.SourceModels.PairedActor
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NonnormalOrdinary.Source

/-!
# The F.9.18 exchanged-component model clause on the Chapter14 setup

Restrict to the literal group J = ⟨K^T⟩T, which remains outside M. Its
perfect normal component orbit is O²(J), so the source placed quadratic
actor acts faithfully on that orbit in J/O₂(J). A.3.8 gives the actual
index-two normalizer and earlier nonnormal component catalogue. Applying
the completed quadratic-actor theorem gives PSL₂ in characteristic two,
Suzuki, or PSL₃(2), with the original K/O₂(K) marking retained.

The final consumer combines this branch with NormalModels and removes the
F.9.18 model premise from the reduced Lie-model list. The remaining model
exclusions and natural-module recognition stay with
qt-e-suitable-component-supports. Original 14.6.18 remains explicit and is
owned by qt-e-14625-source.

Source: Aschbacher--Smith F.9.18(5), printed pp.325--326, A.3.8,
printed pp.45--46, and 14.6.20, printed p.1037.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification.Sieve
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section08.Components.Models Chapter13.Section08.Components.SourceModels
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
include hG hempty hM hunique hmany hcard e hab hsolv

/-- F.9.18(5) on an original nonnormal component, with its actual quotient
and no additional actor, generation or model premise. -/
theorem source_nonnormal_component_f918_models
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : ¬ (K.subgroupOf H).Normal) : NonnormalF918Models (K ⧸ pCore 2 K) := by
  let X := conjugateSpanBy K (T : Subgroup G)
  let J := X ⊔ (T : Subgroup G)
  have hXH : X ≤ H := conjugateSpanBy_le hKH (hH.1.2.trans H.le_normalizer)
  have hJH : J ≤ H := sup_le hXH hH.1.2
  have hXJ : X ≤ J := le_sup_left
  have hKJ : K ≤ J := (le_conjugateSpanBy K _).trans hXJ
  have hTJ : (T : Subgroup G) ≤ J := le_sup_right
  have hJ : J ∈ Chapter1.HOutside G (T : Set G) (M : Set G) :=
    source_component_orbit_outside hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK
  have hHX : H ≤ normalizer (X : Set G) :=
    source_component_orbit_normal hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK
  have hTK : ¬ (T : Subgroup G) ≤ normalizer (K : Set G) := by
    intro ht
    have he : X = K := le_antisymm (conjugateSpanBy_le le_rfl ht) (le_conjugateSpanBy K _)
    exact hn ((normal_subgroupOf_iff_le_normalizer hKH).mpr (he ▸ hHX))
  have hc : (K.subgroupOf J).IsCComponent := hK.subgroupOf_of_le hKJ hJH
  let : Group.IsPerfect (K.subgroupOf H) := hK.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hKH).toMonoidHom) (subgroupOfEquivOfLe hKH).surjective
  let : Group.IsPerfect X := conjugateSpanBy_isPerfect K (T : Subgroup G)
  let : Group.IsPerfect (X.subgroupOf J) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hXJ).symm.toMonoidHom) (subgroupOfEquivOfLe hXJ).symm.surjective
  let : (X.subgroupOf J).Normal := (normal_subgroupOf_iff_le_normalizer hXJ).mpr (hJH.trans hHX)
  have hp : IsPPerfect 2 (X.subgroupOf J) := by
    intro N hN hq
    let : N.Normal := hN
    by_contra hne
    let : Nontrivial ((X.subgroupOf J) ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    let : Group.IsNilpotent ((X.subgroupOf J) ⧸ N) := hq.isNilpotent
    exact Group.IsPerfect.not_isSolvable ((X.subgroupOf J) ⧸ N) inferInstance
  have hr : pResidual 2 J = X.subgroupOf J :=
    pResidual_eq_of_isPPerfect_sup (X.subgroupOf J) ((T : Subgroup G).subgroupOf J)
      hp T.isPGroup'.comap_subtype (by
        rw [←subgroupOf_sup hXJ hTJ]
        change J.subgroupOf J = ⊤
        simp only [subgroupOf_self])
  obtain ⟨hU,a,A,hA,hAE,hAQ,hbound,_,hfaith⟩ :=
    source_rankTwo_bounded_placed_action hG T hempty hM hunique hmany hcard e hab J hJ
  let := hU
  let q := QuotientGroup.mk' (pCore 2 J)
  let D := (K.subgroupOf J).map q
  let S := ((T : Subgroup G).subgroupOf J).map q
  let ec := (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKJ)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hKJ))).symm.trans (cComponentTwoCoreQuotientEquiv hc)
  have hs : IsSQTK KnownSimple.IsKnownSimple (J ⧸ pCore 2 J) := by
    have hsJ := Chapter3.sqtk_of_mem_H hG hJ.1.1
    refine ⟨?_,hsJ.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hsJ.stronglyQuasithin p hp ho)
  let : Group.IsNilpotent (pCore 2 J) := pCore_isPGroup.isNilpotent
  have hmove : ¬ S ≤ normalizer (D : Set (J ⧸ pCore 2 J)) := by
    intro hsn
    have ht := map_le_iff_le_comap.mp hsn
    rw [normalizer_cComponent_quotient hc (pCore 2 J)] at ht
    apply hTK
    intro t htt
    have ht' := ht (show (⟨t,hTJ htt⟩ : J) ∈ (T : Subgroup G).subgroupOf J from htt)
    rwa [←subgroupOf_normalizer_eq hKJ] at ht'
  obtain ⟨hi,hm⟩ : (normalizer (D : Set (J ⧸ pCore 2 J))).index = 2 ∧
      Chapter1.Section02.NonnormalCComponentModel D := by
    rcases ChapterA.Section03.NonnormalOrdinary.index_and_model_knownSimple hs
      (pCore_quotient_pCore_eq_bot 2) D (hc.map_quotient (pCore 2 J)) with hdn | hm
    · let := hdn
      exact (hmove (by rw [normalizer_eq_top]; exact le_top)).elim
    · exact hm
  let : IsSimpleGroup (K ⧸ pCore 2 K) := source_component_quotient_simple
    hG T hempty hM hunique hmany hcard e hab hsolv J hJ K hKJ hc
  let : IsSimpleGroup D := ec.symm.isSimpleGroup
  let : Group.IsPerfect D := (hc.map_quotient (pCore 2 J)).perfect
  have hz : center D = ⊥ := by
    rcases (inferInstance : (center D).Normal).eq_bot_or_eq_top with hz | hz
    · exact hz
    · exact (Group.IsPerfect.not_isMulCommutative D (center_eq_top_iff.mp hz)).elim
  let : IsQuasisimple D := ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩
  have hD : IsComponent (J ⧸ pCore 2 J) D := ⟨(hc.map_quotient (pCore 2 J)).subnormal,inferInstance⟩
  have hAT : A.map q ≤ S := by
    apply map_mono
    have hTI : (T : Subgroup G) ≤ (sourceResidual M Mc ⊔ (T : Subgroup G)) ⊓ J :=
      le_inf le_sup_right hTJ
    have hcore := pCoreIn_le_sylow _ (T.subtype hTI)
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTI] at hcore
    exact hA.trans (subgroupOf_mono J hcore)
  have hX : X.subgroupOf J = conjugateSpanBy (K.subgroupOf J) ((T : Subgroup G).subgroupOf J) := by
    apply map_injective J.subtype_injective
    rw [map_subgroupOf_eq_of_le hXJ,map_conjugateSpanBy,
      map_subgroupOf_eq_of_le hKJ,map_subgroupOf_eq_of_le hTJ]
  have hfaith' : A.map q ⊓ centralizer (componentOrbit D S : Set (J ⧸ pCore 2 J)) = ⊥ := by
    rw [GenerationOne.residual,hr,actorImage_internal,hX,map_conjugateSpanBy,
      conjugateSpanBy_eq_iSup_conj] at hfaith
    exact hfaith
  exact (nonnormal_models_of_quadratic_actor a.representation D S (A.map q) hD hs hm hi
    hmove a.faithful hAT hAE hAQ hbound hfaith').transport ec

/-- The reduced Lie-type catalogue for every original component, with the
F.9.18 input discharged in both normal and exchanged branches. -/
theorem source_component_remaining_lie_models
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent) :
    RemainingLieQuotientModels (K ⧸ pCore 2 K) := by
  by_cases hn : (K.subgroupOf H).Normal
  · exact source_normal_component_remaining_lie_models hG T hempty hM hunique hmany hcard e hab hsolv
      H hH K hKH hK hn
  · have hm := source_nonnormal_component_f918_models hG T hempty hM hunique hmany hcard e hab hsolv
      H hH K hKH hK hn
    rcases hm with ⟨n,hn,hm⟩ | ⟨m,hm,he⟩ | hm
    · exact Or.inl (.linear n hn hm)
    · exact Or.inl (.suzuki m hm he)
    · exact Or.inr (Or.inl ⟨1,le_rfl,by simpa using hm⟩)

/-- At the unchanged terminal H=Mc, each component has an actual remaining
Lie-type quotient model. No normality or model-catalogue premise is retained. -/
theorem terminal_component_remaining_lie_models
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent) :
    RemainingLieQuotientModels (K ⧸ pCore 2 K) :=
  source_component_remaining_lie_models hG T hempty hM hunique hmany hcard e hab hsolv Mc
    (terminal_outside hG T hempty hM hunique hmany hcard e) K hKM hK

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification.Sieve
