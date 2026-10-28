module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof.SporadicPoints
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.SylowOvergroups.PrimeActors
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.IntrinsicStructure
public import Theory.GroupTheory.TwoThreeSolvable
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.FiveRank
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof.PointAlternatives

/-!
# Hall--Janko and small Janko point comparisons in 11.4.2

A proper local C-component in the actual J₂ carrier lies, together with
its full Sylow, in one of the two certified local overgroups. The second
has only the primes two and three and is solvable. In the first, the
literal two-core quotient is A₅, so every nonsolvable subgroup has the
same two-core quotient. Applied to the original point image, this would
force the seed and point components to coincide. Thus J₂ cannot be a
proper containing component, including in the quasisimple-point branch.

Exhausting the complete 11.1.1 containing catalogue now leaves seven
sporadic rows for a quasisimple point quotient. The original point cannot
be J₁ or J₂ in those rows: orders exclude J₁ and six J₂ cases, while the
proper Rudvalis full-Sylow rank bound excludes the five-rank-two J₂ case.
Both comparisons retain the original quotient images and intrinsic cores.
The chosen-module consumer is in Comparison.Overcomponent.

The seven remaining containing comparisons, inner radical placement,
strict omega-center containment and final equality remain with
qt-d-1222-shadow-component-comparison. The independent positive
normalized-module implication remains with qt-d-1222-normalized-nonff;
earlier source geometry retains final discharge by
qt-d-1222-shadow-components. This does not establish full 11.4.2.
Source: Aschbacher--Smith A.3.12 and 11.4.2, printed pp.47--48,776--777.
Imported J₂ and Rudvalis carrier calculations retain LICENSES/ATLAS.txt
and LICENSES/ATLAS-CITATION.cff.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof
open Chapter1.Section02 ChapterA.Section03 ChapterA.Section03.SourceEmbeddings

private theorem nonsolvable_subgroup_five_quotient
    {A : Type*} [Group A] [Finite A] (B : Subgroup A)
    (hB : ¬ Group.IsSolvable B)
    (e : (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 5)) :
    Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) := by
  let f := (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))).comp B.subtype
  have hk : IsPGroup 2 f.ker := by
    have he : f.ker = (pCore 2 A).comap B.subtype := by
      ext x
      change e (QuotientGroup.mk' (pCore 2 A) x.val) = 1 ↔ x.val ∈ pCore 2 A
      rw [←e.map_one,e.injective.eq_iff]
      exact QuotientGroup.eq_one_iff _
    rw [he]
    exact pCore_isPGroup.comap_subtype
  let : Group.IsNilpotent f.ker := hk.isNilpotent
  have hf : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    by_contra hne
    let := alternatingGroup.isSolvable_subgroup_five_of_ne_top f.range hne
    exact hB (Group.isSolvable_of_ker_le_range f.ker.subtype f.rangeRestrict (by simp))
  let a := f.quotientPCoreEquivOfSurjective hf hk
  have ho : pCore 2 (alternatingGroup (Fin 5)) = ⊥ := by
    let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    rcases (inferInstance : (pCore 2 (alternatingGroup (Fin 5))).Normal).eq_bot_or_eq_top with hh | hh
    · exact hh
    · have hp := (hh ▸ pCore_isPGroup (p := 2) (G := alternatingGroup (Fin 5))).of_equiv topEquiv
      obtain ⟨n,hn⟩ := hp.exists_card_eq
      have hc := (by decide : Nat.Coprime 2 3).pow_left n
      rw [←hn,nat_card_alternatingGroup] at hc
      norm_num [Nat.factorial] at hc
  exact ⟨a.trans ((QuotientGroup.quotientMulEquivOfEq ho).trans QuotientGroup.quotientBot)⟩

/-- Every proper local C-component of the actual J₂ carrier has A₅
as its intrinsic two-core quotient. -/
theorem jankoTwo_local_quotient_five
    (S : Sylow 2 Sporadic.LeechRelated.J2.Carrier)
    (C : Subgroup Sporadic.LeechRelated.J2.Carrier)
    (hC : C ∈ localCComponents S) (hne : C ≠ ⊤)
    (htop : (⊤ : Subgroup Sporadic.LeechRelated.J2.Carrier).IsCComponent) :
    Nonempty ((C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 5)) := by
  open Sporadic.LeechRelated.J2 in
  open ExceptionalParabolics in
  have hjoin := local_sup_ne_top_of_ne_top htop S C hC hne
  let S₀ := SecondParabolic.sylow FirstParabolic.card_l₁
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Carrier S S₀
  let a := MulAut.conj g
  have hS : (S : Subgroup Carrier).map a.toMonoidHom = Seed.s :=
    congrArg Sylow.toSubgroup hg
  let B := C.map a.toMonoidHom
  let P := S.mapSurjective (f := a.toMonoidHom) a.surjective
  have hl : B ∈ localCComponents (P : Subgroup Carrier) := by
    let : Group.IsSolvable a.toMonoidHom.ker := by
      rw [a.toMonoidHom.ker_eq_bot a.injective]
      infer_instance
    exact localCComponents_map_of_solvable_ker hC a.toMonoidHom
  have hns : ¬ Group.IsSolvable B := by
    intro hs
    let := hs
    let b := subgroupOfEquivOfLe (show B ≤ B ⊔ (P : Subgroup Carrier) from le_sup_left)
    exact hl.not_isSolvable (Group.isSolvable_of_isSolvable_injective
      (f := b.toMonoidHom) b.injective)
  have hp : B ⊔ Seed.s ≠ ⊤ := by
    intro he
    apply hjoin
    apply a.mapSubgroup.injective
    change (C ⊔ (S : Subgroup Carrier)).map a.toMonoidHom =
      (⊤ : Subgroup Carrier).map a.toMonoidHom
    rwa [Subgroup.map_sup,hS,map_top_of_surjective _ a.surjective]
  have hm : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) := by
    rcases SylowOvergroups.proper_overgroup_le (B ⊔ Seed.s) le_sup_right hp with h | h
    · have hb := le_sup_left.trans h
      let b := subgroupOfEquivOfLe hb
      have hns' : ¬ Group.IsSolvable (B.subgroupOf Seed.l₁) := by
        intro hs
        let := hs
        exact hns (Group.isSolvable_of_surjective (f := b.toMonoidHom) b.surjective)
      obtain ⟨e⟩ := nonsolvable_subgroup_five_quotient (B.subgroupOf Seed.l₁)
        hns' FirstParabolic.l₁_quotient.some
      exact ⟨(QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).symm.trans e⟩
    · have hd : Nat.card B ∣ 1152 := PairNormalizer.card_p₂ ▸
        card_dvd_of_le (le_sup_left.trans h)
      apply (hns (isSolvable_of_prime_dvd_card_eq_two_or_three B ?_)).elim
      intro p hp hpB
      have hpN := hpB.trans hd
      rw [show 1152 = 2^7 * 3^2 by decide] at hpN
      rcases hp.dvd_mul.mp hpN with hh | hh
      · exact .inl (Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_two hh)
      · exact .inr (Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_three hh)
  let b := a.subgroupMap C
  exact ⟨(QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans hm.some⟩

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
    {L V : Subgroup G} {D : Chapter12.Section02.ChosenModule T L V}
    {E : Closure.Geometry D}

/-- The J₂ quotient forces the original point quotient to be A₅,
through the same containing projection and intrinsic two-cores. -/
theorem point_quotient_five_in_jankoTwo
    (h : EarlierGeometry E) {J : Subgroup G}
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hlt : E.Kz < J)
    (e : (J ⧸ pCore 2 J) ≃* Sporadic.LeechRelated.J2.Carrier) :
    Nonempty ((E.Kz ⧸ pCore 2 E.Kz) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨P,C,hC,hproper,_,⟨a⟩,htop⟩ := proper_local_model_image h.point_mem_local_family hJ
    (sylow_normalizes_overcomponent h hJ hlt.le) (sylow_normalizes_point h) hlt e
  exact ⟨a.trans (jankoTwo_local_quotient_five P C hC hproper htop).some⟩

/-- A J₂ containing quotient is incompatible with the strict seed--point
chain. This removes its whole source row, including quasisimple points. -/
theorem ofFlag_not_jankoTwo_overcomponent
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ A, Hypothesis1131At D S (c.binarySubspace (f.space 0)) A →
      Proposition1132At D S (c.binarySubspace (f.space 0)) A)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier)
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hlt : (ofFlag S f X z H).Kz < J) :
    ¬ Nonempty ((J ⧸ pCore 2 J) ≃* Sporadic.LeechRelated.J2.Carrier) := by
  rintro ⟨a⟩
  obtain ⟨b⟩ := point_quotient_five_in_jankoTwo h hJ hlt a
  have hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree) :=
    ⟨S.field.Carrier,inferInstance,inferInstance,S.field.card_eq,⟨e⟩⟩
  have he := local_eq_of_quotient_sylow_solvable
    (LocalGeometry.Components.flag_mem_local_of_model D S f 0 hm) h.point_mem_local_family
    (sylow_normalizes_point h) (le_conjugateSpanBy _ _)
    (SolvableSylowOvergroups.of_equiv b (fun _ P _ hP =>
      alternatingGroup.isSolvable_subgroup_five_of_ne_top P hP))
  exact (h.strict_comparison (fixed_and_transitive D S _ hlinear h1132).1 hne).2.1.ne he

/-- The remaining literal containing models in the quasisimple-point branch.
This is a proved output list below, not an additional input hypothesis. -/
@[expose] def QuasisimplePointContainer (A : Type*) [Group A] : Prop :=
  Nonempty (A ≃* Sporadic.Mathieu.M22) ∨ Chapter1.Section02.LocalModels.IsM22Cover A ∨
  Nonempty (A ≃* Sporadic.Mathieu.M23) ∨ Nonempty (A ≃* Janko1.Model) ∨
  Nonempty (A ≃* Janko4.Model) ∨ Nonempty (A ≃* Sporadic.LeechRelated.HS.Carrier) ∨
  Nonempty (A ≃* Rudvalis.Model)

/-- The full containing catalogue for quasisimple points reduces to seven
sporadic rows. In particular the complete J₂ row is now excluded. -/
theorem ofFlag_quasisimple_point_containers
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hqs : IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ A, Hypothesis1131At D S (c.binarySubspace (f.space 0)) A →
      Proposition1132At D S (c.binarySubspace (f.space 0)) A)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    {J : Subgroup G} (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hlt : (ofFlag S f X z H).Kz < J) :
    S.field.degree = 2 ∧ QuasisimplePointContainer (J ⧸ pCore 2 J) := by
  obtain ⟨hd,hrows⟩ := ofFlag_proper_overcomponent_fieldFour S f X z H h hne hlinear h1132 e hJ.1 hlt
  refine ⟨hd,?_⟩
  have hrank := ofFlag_rankOne_exclusions S f X z H h hne hlinear h1132 e hJ.1 hlt
  let := ofFlag_proper_overcomponent_quasisimple S f X z H h hne hlinear h1132 e hcent hJ hlt
  cases hrows with
  | alternating hm => exact (ofFlag_not_alternating_seven_overcomponent S f X z H h hne
      hlinear h1132 e hJ.1 hlt (.inl hm)).elim
  | alternatingCover hm => exact (ofFlag_not_alternating_seven_overcomponent S f X z H h hne
      hlinear h1132 e hJ.1 hlt (.inr hm)).elim
  | primeLinear p hp hm =>
    have ho : Odd p := hp.1.odd_of_ne_two (by have := hp.2.1; omega)
    exact ((hrank.2.2 p hp.1 ho).1 hm).elim
  | linearTwentyFive hm => exact ((hrank.2.2 5 (by decide) (by decide)).2 hm).elim
  | three u hm =>
    exact (ofFlag_not_quasisimple_point_in_odd_ternary S f X z H h hne
      hlinear h1132 e hJ.1 hlt (by decide : Nat.Prime 5) (by decide : Odd 5) u hm hqs).elim
  | m22 hm => exact .inl hm
  | m22Cover hm => exact .inr (.inl hm)
  | m23 hm => exact .inr (.inr (.inl hm))
  | j1 hm => exact .inr (.inr (.inr (.inl hm)))
  | j2 hm => exact (ofFlag_not_jankoTwo_overcomponent S f X z H h hne
      hlinear h1132 e hJ.1 hlt hm).elim
  | j4 hm => exact .inr (.inr (.inr (.inr (.inl hm))))
  | hs hm => exact .inr (.inr (.inr (.inr (.inr (.inl hm)))))
  | ru hm => exact .inr (.inr (.inr (.inr (.inr (.inr hm)))))
  | nilpotentExtension hm =>
    exact (Quasisimple.Classification.not_odd_sl2_extension
      (pCore_quotient_pCore_eq_bot 2) _ (by decide : Odd 5) hm).elim
  | elementaryExtension p hp hm =>
    exact (Quasisimple.Classification.not_odd_sl2_extension
      (pCore_quotient_pCore_eq_bot 2) _ (hp.1.odd_of_ne_two (by have := hp.2.1; omega)) hm).elim

private theorem m22_cover_card {A : Type*} [Group A]
    (hm : Chapter1.Section02.LocalModels.IsM22Cover A) : Nat.card A = 1330560 := by
  have hz : Nat.card (center A) = 3 := by
    rw [Nat.card_congr hm.2.1.some.toEquiv]
    exact Nat.card_zmod 3
  rw [←(center A).card_mul_index,index_eq_card,hz,
    Nat.card_congr hm.2.2.some.toEquiv,Sporadic.Mathieu.m22_order]

/-- In the remaining containing rows, the original point quotient cannot
be J₁. Its factor nineteen excludes every other row; equal quotient orders
in the J₁ row would make the literal proper point image the whole carrier. -/
theorem point_not_jankoOne_in_containers
    (h : EarlierGeometry E) {J : Subgroup G}
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hlt : E.Kz < J)
    (hm : QuasisimplePointContainer (J ⧸ pCore 2 J)) :
    ¬ Nonempty ((E.Kz ⧸ pCore 2 E.Kz) ≃* Janko1.Model) := by
  rintro ⟨b⟩
  obtain ⟨P,C,hC,hproper,_,⟨a⟩,_⟩ := proper_local_model_image h.point_mem_local_family hJ
    (sylow_normalizes_overcomponent h hJ hlt.le) (sylow_normalizes_point h) hlt
    (MulEquiv.refl (J ⧸ pCore 2 J))
  have hcard : Nat.card (C ⧸ pCore 2 C) = 175560 := by
    rw [Nat.card_congr (a.symm.trans b).toEquiv,Janko1.card_model]
  have hd : 175560 ∣ Nat.card (J ⧸ pCore 2 J) := hcard ▸
    (card_quotient_dvd_card (pCore 2 C)).trans C.card_subgroup_dvd_card
  rcases hm with hm | hm | hm | hm | hm | hm | hm
  · rw [Nat.card_congr hm.some.toEquiv,Sporadic.Mathieu.m22_order] at hd
    norm_num at hd
  · rw [m22_cover_card hm] at hd
    norm_num at hd
  · rw [Nat.card_congr hm.some.toEquiv,Sporadic.Mathieu.m23_order] at hd
    norm_num at hd
  · apply hproper
    apply C.eq_top_of_card_eq
    apply le_antisymm (Nat.card_le_card_of_injective C.subtype C.subtype_injective)
    rw [Nat.card_congr hm.some.toEquiv,Janko1.card_model,←hcard]
    exact Nat.card_le_card_of_surjective (QuotientGroup.mk' (pCore 2 C))
      (QuotientGroup.mk'_surjective _)
  · rw [Nat.card_congr hm.some.toEquiv,Janko4.Cardinality.model_card] at hd
    norm_num at hd
  · rw [Nat.card_congr hm.some.toEquiv,Sporadic.LeechRelated.HS.NormalizerIndex.card_carrier] at hd
    norm_num at hd
  · rw [Nat.card_congr hm.some.toEquiv,Rudvalis.model_card] at hd
    norm_num at hd

/-- The same remaining catalogue excludes J₂ point quotients. Order
comparison handles six rows; the literal Rudvalis full-Sylow rank bound
excludes the five-rank-two Hall--Janko quotient in the seventh. -/
theorem point_not_jankoTwo_in_containers
    (h : EarlierGeometry E) {J : Subgroup G}
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hlt : E.Kz < J)
    (hm : QuasisimplePointContainer (J ⧸ pCore 2 J)) :
    ¬ Nonempty ((E.Kz ⧸ pCore 2 E.Kz) ≃* Sporadic.LeechRelated.J2.Carrier) := by
  rintro ⟨b⟩
  obtain ⟨P,C,hC,hproper,_,⟨a⟩,_⟩ := proper_local_model_image h.point_mem_local_family hJ
    (sylow_normalizes_overcomponent h hJ hlt.le) (sylow_normalizes_point h) hlt
    (MulEquiv.refl (J ⧸ pCore 2 J))
  have hcard : Nat.card (C ⧸ pCore 2 C) = 604800 := by
    rw [Nat.card_congr (a.symm.trans b).toEquiv,
      Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier]
  have hd : 604800 ∣ Nat.card (J ⧸ pCore 2 J) := hcard ▸
    (card_quotient_dvd_card (pCore 2 C)).trans C.card_subgroup_dvd_card
  rcases hm with hm | hm | hm | hm | hm | hm | hm
  · rw [Nat.card_congr hm.some.toEquiv,Sporadic.Mathieu.m22_order] at hd
    norm_num at hd
  · rw [m22_cover_card hm] at hd
    norm_num at hd
  · rw [Nat.card_congr hm.some.toEquiv,Sporadic.Mathieu.m23_order] at hd
    norm_num at hd
  · rw [Nat.card_congr hm.some.toEquiv,Janko1.card_model] at hd
    norm_num at hd
  · rw [Nat.card_congr hm.some.toEquiv,Janko4.Cardinality.model_card] at hd
    norm_num at hd
  · rw [Nat.card_congr hm.some.toEquiv,Sporadic.LeechRelated.HS.NormalizerIndex.card_carrier] at hd
    norm_num at hd
  · let e := hm.some
    have hO : pCore 2 Rudvalis.Model = ⊥ := by
      rw [←pCore_map_iso 2 e,pCore_quotient_pCore_eq_bot 2,Subgroup.map_bot]
    obtain ⟨P,C,hC,hproper,_,⟨a⟩,htop⟩ := proper_local_model_image h.point_mem_local_family hJ
      (sylow_normalizes_overcomponent h hJ hlt.le) (sylow_normalizes_point h) hlt e
    have hj := local_sup_ne_top_of_ne_top htop P C hC hproper
    have hb := rudvalis_proper_overgroup_primeRank_le_one hO P
      (C ⊔ (P : Subgroup Rudvalis.Model)) le_sup_right hj (by decide : 3 < 5)
    have hr : 2 ≤ primeRank 5 (C ⧸ pCore 2 C) := by
      rw [primeRank_equiv 5 (a.symm.trans b)]
      exact Sporadic.LeechRelated.J2.five_rank_ge_two
    have hh := hr.trans ((primeRank_quotient_le_of_isTwoGroup 5 (by decide) _ pCore_isPGroup).trans
      (primeRank_mono 5 (show C ≤ C ⊔ (P : Subgroup Rudvalis.Model) from le_sup_left)))
    omega

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof
