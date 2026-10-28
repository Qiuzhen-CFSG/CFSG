module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.LinearOvergroupSupplement
public import Theory.GroupTheory.QuotientCentralizerRank
public import Theory.Quasithin.PositiveLocalRank
public import CFSG.Quasithin.Chapter3.Section01.LocalGeometry
public import Theory.Representation.NormalElementaryQuotient.BestOffender
public import CFSG.Quasithin.ChapterB.InternalThompsonAction

/-!
# The rank-one centralizer action in the remaining overgroup branch

The original component meets the larger action kernel in its two-core.
The residual-centralizer rank inequality therefore bounds the full preimage
of its quotient centralizer by three-rank one. Cyclic Sylow subgroups pass
that bound to the quotient without discarding any part of the action kernel.

If the larger omega module differs from the original six-space, the checked
maximum replacement maps to a nontrivial best offender in this centralizer.
Its offender-generated action satisfies the literal B.5.3 hypotheses through
its SQTK preimage cover. The final reduction combines this remaining case
with the proved module-equality and overgroup-product branch.

This constructs the input for the rank-one classification step on printed
p.902, not its exclusion. The source residual commutator premise, earlier
Structural1222 and Source1332OneTwo inputs remain explicit. No full 13.4.7
or ambient symplectic recognition theorem is asserted here.
Source: Aschbacher–Smith 13.4.7(2), printed p.902, using B.2.5 and B.5.3.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource NoncentralChiefRefinement
open Representation.BinaryOffender
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}
variable (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent)
    (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)
    (eK : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      Matrix.PSL3Two.PSL)
include h₀ D m h1332 hTA hTB eA eB hne hindexA hindexB hK hres eK

/-- The centralizer of the original linear component in the larger faithful
action quotient has three-rank at most one, with its full kernel retained. -/
theorem original_pair_linear_overgroup_centralizer_rank
    (Y : Subgroup G) (hY : Y ∈ Chapter1.HOver G ((A ⊔ B : Subgroup G) : Set G)) :
    let C := K.map (A ⊔ B).subtype
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) Y).subgroupOf Y
    ∃ hr : IsPReduced 2 U, let := hr.normal
      let q := QuotientGroup.mk' (centralizer (U : Set Y))
      primeRank 3 (centralizer ((C.subgroupOf Y).map q : Set (Y ⧸ centralizer (U : Set Y)))) ≤ 1 := by
  let C := K.map (A ⊔ B).subtype
  let W := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) Y
  let U := W.subgroupOf Y
  let J := C.subgroupOf Y
  have hCY : C ≤ Y := (map_subtype_le K).trans hY.2
  have hTY : (T : Subgroup G) ≤ Y := (hTA.trans le_sup_left).trans hY.2
  have hWY : W ≤ Y := conjugateSpanBy_le
    (fun z hz => hTY ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1) Y.le_normalizer
  obtain ⟨hr,_,hkC⟩ := original_pair_overgroup_component_kernel h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK hres Y hY
  let := hr.normal
  let q := QuotientGroup.mk' (centralizer (U : Set Y))
  let : J.Normal := (normal_subgroupOf_iff_le_normalizer hCY).mpr
    (original_pair_component_overgroup_normal h₀ D m h1332
      hTA hTB eA eB hne hindexA hindexB K hK Y hY)
  let j : J ≃* C := subgroupOfEquivOfLe hCY
  let ej : (J ⧸ pCore 2 J) ≃* Matrix.PSL3Two.PSL :=
    (QuotientGroup.congr (pCore 2 J) (pCore 2 C) j (pCore_map_iso 2 j)).trans eK
  have hker : J ⊓ q.ker = J.pCoreIn 2 := by
    apply map_injective Y.subtype_injective
    rw [QuotientGroup.ker_mk']
    have hh := map_inf_centralizer_of_injective Y.subtype Y.subtype_injective J U
    rw [map_subgroupOf_eq_of_le hCY,map_subgroupOf_eq_of_le hWY] at hh
    rw [←hh,hkC]
    change (pCore 2 C).map C.subtype =
      ((pCore 2 J).map J.subtype).map Y.subtype
    rw [map_map,show Y.subtype.comp J.subtype = C.subtype.comp j.toMonoidHom from rfl,
      ←map_map,pCore_map_iso 2 j]
  have hz : Nat.card (center (J ⧸ pCore 2 J)) = 1 := by
    rw [Nat.card_congr (centerCongr ej).toEquiv,
      Matrix.PSL3Two.Automorphisms.center_psl_eq_bot,card_bot]
  have hcard : 3 ∣ Nat.card J := by
    have hd := (pCore 2 J).index_dvd_card
    rw [index_eq_card,Nat.card_congr ej.toEquiv,Matrix.PSL3Two.card_PSL] at hd
    exact (by decide : 3 ∣ 168).trans hd
  refine ⟨hr,?_⟩
  exact ResidualCentralizerRank.quotient_centralizer_rank_le_one (by decide) J q
    (QuotientGroup.mk'_surjective _) hker (by rw [hz]; decide)
    (Theory.Quasithin.one_le_primeRank_of_dvd_card hcard)
    ((Chapter3.sqtk_of_mem_H h₀.qtke hY.1).stronglyQuasithin 3 (by decide) (by decide))

/-- In the remaining replacement case there is an actual best offender in
the rank-one centralizer, on the faithful action of the larger omega module. -/
theorem original_pair_linear_overgroup_centralizer_offender
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hcomm : let K₂ := (pResidual 2 B).map B.subtype
      ⁅K₂,ChapterB.thompsonJ (T : Subgroup G) 1⁆ = K₂)
    (Y : Subgroup G) (hY : Y ∈ Chapter1.HOver G ((A ⊔ B : Subgroup G) : Set G))
    (hneU : conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) Y ≠
      conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B)) :
    let C := K.map (A ⊔ B).subtype
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) Y).subgroupOf Y
    ∃ hr : IsPReduced 2 U, let := hr.normal
      let := hr.elementary
      let N := centralizer (U : Set Y)
      let q := QuotientGroup.mk' N
      let τ := Representation.NormalElementaryQuotient.representation U q
        (QuotientGroup.mk'_surjective N) (QuotientGroup.ker_mk' N)
      ∃ R : Subgroup G,
        R ∈ elementaryAbelianMaxSubgroups (T : Subgroup G) ∧
        R ≤ (A ⊔ B : Subgroup G).pCoreIn 2 ∧
        IsBestOffender τ ((R.subgroupOf Y).map q) ∧
        (R.subgroupOf Y).map q ≤ centralizer ((C.subgroupOf Y).map q : Set (Y ⧸ N)) ∧
        primeRank 3 (centralizer ((C.subgroupOf Y).map q : Set (Y ⧸ N))) ≤ 1 := by
  let X := A ⊔ B
  let C := K.map X.subtype
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let W := conjugateSpanBy Z X
  let W' := conjugateSpanBy Z Y
  let U := W'.subgroupOf Y
  have hTY : (T : Subgroup G) ≤ Y := (hTA.trans le_sup_left).trans hY.2
  have hCY : C ≤ Y := (map_subtype_le K).trans hY.2
  have hWY : W' ≤ Y := conjugateSpanBy_le
    (fun z hz => hTY ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1) Y.le_normalizer
  obtain ⟨hr,hrank⟩ := original_pair_linear_overgroup_centralizer_rank h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK hres eK Y hY
  let := hr.normal
  let := hr.elementary
  let N := centralizer (U : Set Y)
  let q := QuotientGroup.mk' N
  let τ := Representation.NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective N) (QuotientGroup.ker_mk' N)
  obtain ⟨E,hE,hneE,hCE,hRc,hmax,hcases⟩ :=
    original_pair_linear_overgroup_replacement_dichotomy h₀ D m h1332
      hTA hTB eA eB hne hindexA hindexB K hK hres h structural hout hindexL eK hcomm Y hY
  let R := W ⊔ (E ⊓ centralizer (W : Set G))
  obtain ⟨hneR,hRC⟩ := hcases.resolve_left hneU
  have hRY : R ≤ Y := hmax.1.trans hTY
  let R' := R.subgroupOf Y
  have hmapR : R'.map Y.subtype = R := map_subgroupOf_eq_of_le hRY
  have hmax' : R' ∈ elementaryAbelianMaxSubgroups (T.subtype hTY : Subgroup Y) := by
    apply (maxFamily_map_injective_iff Y.subtype Y.subtype_injective
      (T.subtype hTY : Subgroup Y) R').mp
    rwa [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTY,hmapR]
  have hneR' : R'.map q ≠ ⊥ := by
    intro hz
    have hh : R' ≤ N := by simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff R').mp hz
    apply hneR
    intro r hr u hu
    exact congrArg Subtype.val (hh (show (⟨r,hRY hr⟩ : Y) ∈ R' from hr) ⟨u,hWY hu⟩ hu)
  have hUS : U ≤ (T.subtype hTY : Subgroup Y) :=
    hr.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal (T.subtype hTY))
  have hbest : IsBestOffender τ (R'.map q) :=
    Representation.NormalElementaryQuotient.maxElementary_isBestOffender U q
      (QuotientGroup.mk'_surjective N) (QuotientGroup.ker_mk' N)
      (T.subtype hTY : Subgroup Y) R' hUS hmax' hneR'
  refine ⟨hr,R,hmax,hRc,hbest,?_,hrank⟩
  apply commutator_eq_bot_iff_le_centralizer.mp
  rw [←map_commutator,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
  have hmap : (⁅R',C.subgroupOf Y⁆).map Y.subtype ≤ centralizer (W' : Set G) := by
    rw [map_commutator,hmapR,map_subgroupOf_eq_of_le hCY]
    exact hRC
  intro r hr u hu
  exact Subtype.ext (hmap (mem_map_of_mem Y.subtype hr) u.val hu)


/-- The remaining branch supplies the genuine B.5.3 hypothesis on its
nontrivial, rank-one offender actor, via the literal preimage SQTK cover. -/
theorem original_pair_linear_overgroup_centralizer_FF_hypothesis
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hcomm : let K₂ := (pResidual 2 B).map B.subtype
      ⁅K₂,ChapterB.thompsonJ (T : Subgroup G) 1⁆ = K₂)
    (Y : Subgroup G) (hY : Y ∈ Chapter1.HOver G ((A ⊔ B : Subgroup G) : Set G))
    (hneU : conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) Y ≠
      conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B)) :
    let C := K.map (A ⊔ B).subtype
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) Y).subgroupOf Y
    ∃ hr : IsPReduced 2 U, let := hr.normal
      let := hr.elementary
      let N := centralizer (U : Set Y)
      let q := QuotientGroup.mk' N
      let τ := Representation.NormalElementaryQuotient.representation U q
        (QuotientGroup.mk'_surjective N) (QuotientGroup.ker_mk' N)
      let F := centralizer ((C.subgroupOf Y).map q : Set (Y ⧸ N))
      let σ := τ.comp F.subtype
      offenderSubgroup σ ≠ ⊥ ∧ primeRank 3 (offenderSubgroup σ) ≤ 1 ∧
        ChapterB.SourceInduction.FFHypothesis KnownSimple.IsKnownSimple
          (σ.comp (offenderSubgroup σ).subtype) := by
  let C := K.map (A ⊔ B).subtype
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) Y).subgroupOf Y
  obtain ⟨hr,R,hR,hRc,hbest,hcentral,hrank⟩ :=
    original_pair_linear_overgroup_centralizer_offender h₀ D m h1332
      hTA hTB eA eB hne hindexA hindexB K hK hres eK
      h structural hout hindexL hcomm Y hY hneU
  let := hr.normal
  let := hr.elementary
  let N := centralizer (U : Set Y)
  let q := QuotientGroup.mk' N
  let τ := Representation.NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective N) (QuotientGroup.ker_mk' N)
  let F := centralizer ((C.subgroupOf Y).map q : Set (Y ⧸ N))
  let σ := τ.comp F.subtype
  have hbest' : IsBestOffender σ (((R.subgroupOf Y).map q).subgroupOf F) :=
    hbest.subgroupOf τ hcentral
  have hneOff : offenderSubgroup σ ≠ ⊥ := by
    intro hz
    exact hbest'.1.1 (le_bot_iff.mp ((hbest'.le_offenderSubgroup σ).trans_eq hz))
  have hCY : C ≤ Y := (map_subtype_le K).trans hY.2
  let : (C.subgroupOf Y).Normal := (normal_subgroupOf_iff_le_normalizer hCY).mpr
    (original_pair_component_overgroup_normal h₀ D m h1332
      hTA hTB eA eB hne hindexA hindexB K hK Y hY)
  let : ((C.subgroupOf Y).map q).Normal :=
    (inferInstance : (C.subgroupOf Y).Normal).map q (QuotientGroup.mk'_surjective N)
  let : F.Normal := inferInstance
  have hcore : pCore 2 F = ⊥ := by
    apply ((pCore 2 F).map_eq_bot_iff_of_injective F.subtype_injective).mp
    apply le_bot_iff.mp
    have hl : (pCore 2 F).map F.subtype ≤ pCore 2 (Y ⧸ N) :=
      le_sSup ⟨inferInstance,pCore_isPGroup.map F.subtype⟩
    exact hl.trans_eq hr.quotient_pCore_eq_bot
  have hf : Function.Injective σ :=
    (Representation.NormalElementaryQuotient.representation_injective U q
      (QuotientGroup.mk'_surjective N) (QuotientGroup.ker_mk' N)).comp F.subtype_injective
  refine ⟨hr,hneOff,(primeRank_subgroup_le 3 _).trans hrank,?_⟩
  exact ChapterB.InternalThompsonAction.offender_hypothesis σ
    (q.subgroupComap F) (q.subgroupComap_surjective_of_surjective F (QuotientGroup.mk'_surjective N))
    ((Chapter3.sqtk_of_mem_H h₀.qtke hY.1).subgroup (F.comap q)) hf hcore


/-- The original overgroup problem reduces to a genuine nontrivial rank-one
FF action, with the full source product proved in the other branch. -/
theorem original_pair_linear_overgroup_reduction
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hcomm : let K₂ := (pResidual 2 B).map B.subtype
      ⁅K₂,ChapterB.thompsonJ (T : Subgroup G) 1⁆ = K₂)
    (Y : Subgroup G) (hY : Y ∈ Chapter1.HOver G ((A ⊔ B : Subgroup G) : Set G)) :
    let X := A ⊔ B
    let C := K.map X.subtype
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    let W := conjugateSpanBy Z X
    let U := (conjugateSpanBy Z Y).subgroupOf Y
    (conjugateSpanBy Z Y = W ∧
      (Y : Set G) = (X : Set G) * (Y ⊓ centralizer (W : Set G) : Subgroup G)) ∨
    (∃ hr : IsPReduced 2 U, let := hr.normal
      let := hr.elementary
      let N := centralizer (U : Set Y)
      let q := QuotientGroup.mk' N
      let τ := Representation.NormalElementaryQuotient.representation U q
        (QuotientGroup.mk'_surjective N) (QuotientGroup.ker_mk' N)
      let F := centralizer ((C.subgroupOf Y).map q : Set (Y ⧸ N))
      let σ := τ.comp F.subtype
      offenderSubgroup σ ≠ ⊥ ∧ primeRank 3 (offenderSubgroup σ) ≤ 1 ∧
        ChapterB.SourceInduction.FFHypothesis KnownSimple.IsKnownSimple
          (σ.comp (offenderSubgroup σ).subtype)) := by
  by_cases he : conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) Y =
      conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B)
  · exact Or.inl ⟨he,original_pair_linear_overgroup_supplement_of_omega_eq h₀ D m h1332
      hTA hTB eA eB hne hindexA hindexB K hK hres h structural hout hindexL eK Y hY he⟩
  · exact Or.inr (original_pair_linear_overgroup_centralizer_FF_hypothesis h₀ D m h1332
      hTA hTB eA eB hne hindexA hindexB K hK hres eK
      h structural hout hindexL hcomm Y hY he)

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
