module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Classification.Sieve.LinearThree
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.NormalUnitary

/-!
# Excluding terminal unitary components

The natural SU₃ Borel calculation is applied through the faithful image of
each irreducible factor, then through invariant extensions. On the literal
J=KT quotient action it makes the original Borel-fixed generating seed fixed
by the component. Normality propagates this to the entire module, contradicting
faithfulness. The original K/O₂(K) and ambient source hypotheses are retained.

Original 14.6.18 is the allowed input owned by qt-e-14625-source. The remaining
PSL₂ exclusion and support assembly stay with qt-e-suitable-component-supports.
Source: Aschbacher--Smith 14.6.20, printed p.1037, and K.3.3, p.456.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification.Sieve
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.SmallRatio
open Chapter13.Section08.Components.Models
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

/-- No unitary-three quotient occurs on the original relatively normal component. -/
theorem source_normal_component_not_psu_three
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : (K.subgroupOf H).Normal)
    {f : ℕ} (hf : 2 ≤ f) :
    ¬ ClassicalGroup.IsPSU (K ⧸ pCore 2 K) 3 (2 ^ f) := by
  rintro ⟨F,_,_,Jform,hF,hconj,⟨eF⟩⟩
  let J := K ⊔ (T : Subgroup G)
  have hJH : J ≤ H := sup_le hKH hH.1.2
  have hKJ : K ≤ J := le_sup_left
  have hTJ : (T : Subgroup G) ≤ J := le_sup_right
  have hJ : J ∈ Chapter1.HOutside G (T : Set G) (M : Set G) :=
    ⟨Chapter3.mem_HOver_of_sylow_interval T hTJ hJH hH.1,
      fun hj => source_component_not_le hG T hempty hM hunique hmany hcard e hab hsolv
        H hH K hKH hK (hKJ.trans hj)⟩
  have hc : (K.subgroupOf J).IsCComponent := hK.subgroupOf_of_le hKJ hJH
  have hnc : (K.subgroupOf J).Normal := (normal_subgroupOf_iff_le_normalizer hKJ).mpr
    (hJH.trans ((normal_subgroupOf_iff_le_normalizer hKH).mp hn))
  have hgen : K.subgroupOf J ⊔ (T : Subgroup G).subgroupOf J = ⊤ := by
    rw [←subgroupOf_sup hKJ hTJ]
    change J.subgroupOf J = ⊤
    simp only [subgroupOf_self]
  obtain ⟨hU,a,A,hA,hAE,hAQ,hbound,_,_⟩ :=
    source_rankTwo_bounded_placed_action hG T hempty hM hunique hmany hcard e hab J hJ
  let := hU
  let q := QuotientGroup.mk' (pCore 2 J)
  let : Group.IsNilpotent (pCore 2 J) := pCore_isPGroup.isNilpotent
  let D := (K.subgroupOf J).map q
  let ec := (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKJ)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hKJ))).symm.trans (cComponentTwoCoreQuotientEquiv hc)
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
  let : D.Normal := hnc.map q (QuotientGroup.mk'_surjective _)
  have hs : IsSQTK KnownSimple.IsKnownSimple (J ⧸ pCore 2 J) := by
    have hsJ := Chapter3.sqtk_of_mem_H hG hJ.1.1
    refine ⟨?_,hsJ.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hsJ.stronglyQuasithin p hp ho)
  have hAD : A.map q ⊓ centralizer (D : Set (J ⧸ pCore 2 J)) = ⊥ :=
    source_placed_actor_faithful_on_normal_cComponent T hTJ A hA
      (K.subgroupOf J) hc hnc hgen
  obtain ⟨P,hP⟩ := source_component_sylow T J K hTJ hKJ hc
  let qK := ec.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  let Pq := P.mapSurjective (f := qK) (ec.surjective.comp (QuotientGroup.mk'_surjective _))
  let B := normalizer (Pq : Set D)
  have hBM : B ≤ (M.subgroupOf K).map qK :=
    source_component_sylow_normalizer_le_image T M hsolv J hJ.1 K hKJ hc ec P hP
  have hseed := source_overlap_seed_fixed hG T hempty hM hunique hmany hcard e hab J hJ a
  have hcalc := Modules.NormalUnitary.fixedSpace_le_of_quadratic_actor
    a.representation D hz hs (A.map q) hAE hAQ hbound hAD hf
    ⟨F,inferInstance,inferInstance,Jform,hF,hconj,
      ⟨(centerQuotientEquiv hz).trans (ec.symm.trans eF)⟩⟩ B ⟨Pq,rfl⟩
  have hseedD : seedSpace a (localModule T M) ≤ fixedSpace a.representation D := by
    intro v hv k
    apply hcalc ?_ ⟨k,mem_top _⟩
    intro b
    have hb : (b.val : J ⧸ pCore 2 J) ∈ actorImage J (M ⊓ J) := by
      obtain ⟨k,hk,he⟩ := hBM b.property
      refine ⟨⟨k,hKJ k.property⟩,⟨hk,hKJ k.property⟩,?_⟩
      exact congrArg Subtype.val he
    simpa only [MonoidHom.comp_apply,Subgroup.subtype_apply] using hseed hv ⟨b.val,hb⟩
  have hwhole : (⊤ : Submodule (ZMod 2) _) ≤ fixedSpace a.representation D := by
    rw [←seedSpace_iSup_maps_eq_top a]
    apply iSup_le
    intro g v hv
    obtain ⟨w,hw,rfl⟩ := hv
    exact (fixedSpace_stable_of_normal a.representation D (mem_top g) w).2 (hseedD hw)
  have hbot : D = ⊥ := by
    apply bot_unique
    intro d hd
    apply mem_bot.mpr
    apply a.faithful
    apply LinearMap.ext
    intro v
    simpa only [MonoidHom.comp_apply,Subgroup.subtype_apply,map_one,Module.End.one_apply]
      using hwhole Submodule.mem_top ⟨d,hd⟩
  exact hc.map_quotient_ne_bot (pCore 2 J) hbot



/-- The unitary exclusion at the unchanged terminal group Mc. -/
theorem terminal_normal_component_not_psu_three
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (hn : (K.subgroupOf Mc).Normal) {f : ℕ} (hf : 2 ≤ f) :
    ¬ ClassicalGroup.IsPSU (K ⧸ pCore 2 K) 3 (2 ^ f) :=
  source_normal_component_not_psu_three hG T hempty hM hunique hmany hcard e hab hsolv Mc
    (terminal_outside hG T hempty hM hunique hmany hcard e) K hKM hK hn hf

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification.Sieve
