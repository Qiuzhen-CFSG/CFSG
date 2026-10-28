module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Classification.Sieve.HigherLinear
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Classification.Sieve.ComponentPlacement
public import CFSG.Quasithin.Chapter14.Section06.SourceMovedModule
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.OriginalModule.Normal.QuadraticModules
public import Theory.GroupTheory.PerfectSylowPreservingAction

/-!
# Odd-exponent exclusions from the actual component Borel

Every finite Sylow two-normalizer is solvable. The original 14.6.18
placement therefore puts the marked component Borel in the image of
M intersect K, including when T exchanges components. Also M intersect H
fixes the original seed modulo Z, since that quotient has order two.

For a normal component, restrict to J=KT and use its faithful original
span action. The placed quadratic actor is faithful on the component image.
The proved B.4 constituent and Borel calculation at odd defining exponent
greater than one makes Borel-fixed vectors component-fixed. Normality then
extends fixation of the seed to its whole span, contradicting faithfulness.
This excludes the normal Suzuki row and the odd nonbinary exponents in
PSL₂, PSU₃, PSL₃, and the native derived Sp₄ models.

The final consumers apply this to the instantiated F.9.18 catalogue on the
original group and at H=Mc. The remaining even exponents, G₂ models,
exchanged-component exclusions, and natural-support construction remain
with qt-e-suitable-component-supports. Only original 14.6.18 is retained
as an earlier source input, owned by qt-e-14625-source. Restriction to KT
is used for exclusion and does not identify its span with the whole Mc-span.

Source: Aschbacher--Smith 14.6.20, printed p.1037; the Borel calculation
uses B.4.2--5 and the odd-exponent module argument of 15.3.65, p.1152.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification.Sieve
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.SmallRatio

variable {G : Type*} [Group G] [Finite G]

/-- The literal component Borel lies in the marked image of M intersect K. -/
theorem source_component_sylow_normalizer_le_image
    {D : Type*} [Group D] [Finite D]
    (T : Sylow 2 G) (M : Subgroup G)
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
    (H : Subgroup G) (hH : H ∈ Chapter1.HOver G (T : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (eK : (K ⧸ pCore 2 K) ≃* D)
    (P : Sylow 2 K) (hP : (P : Subgroup K) = (T : Subgroup G).subgroupOf K) :
    normalizer (((P : Subgroup K).map
      (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))) : Set D) ≤
      (M.subgroupOf K).map (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))) := by
  let q := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  let Pq := P.mapSurjective (f := q) (eK.surjective.comp (QuotientGroup.mk'_surjective _))
  let : Group.IsSolvable (normalizer (Pq : Set D)) := Pq.normalizer_isSolvable_two
  apply source_component_solvable_le_image T M hsolv H hH K hKH hK eK
    (normalizer (Pq : Set D))
  intro s
  let α := Subgroup.NormalSylowQuotientAction.markedCoreAction 2 K eK ⟨s,s.property.2⟩
  have hp : (Pq : Subgroup D).map α.toMonoidHom = Pq :=
    Subgroup.NormalSylowQuotientAction.markedCoreAction_preserves_component_sylow
      2 T K eK P hP s
  exact ((Pq : Subgroup D).map_equiv_normalizer_eq α).trans
    (congrArg (fun R : Subgroup D => normalizer (R : Set D)) hp)

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

omit hsolv in
/-- The original overlap fixes the one-dimensional seed quotient. -/
theorem source_overlap_seed_fixed
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T)) :
    seedSpace a (localModule T M) ≤ fixedSpace a.representation (actorImage H (M ⊓ H)) := by
  have h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  apply (RepresentationReduction.seedSpace_le_actorImage_iff a
    (le_conjugateSpanBy _ _) inf_le_right).mpr
  have hi : (centralInvolutions T).relIndex (localModule T M) = 2 := by
    have hc := ((centralInvolutions T).subgroupOf (localModule T M)).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe h.point_lt.le).toEquiv] at hc
    change Nat.card (centralInvolutions T) *
      (centralInvolutions T).relIndex (localModule T M) = Nat.card (localModule T M) at hc
    rw [h.point_card,hcard] at hc
    omega
  exact commutator_le_of_normalized_index_two _ _ _ h.point_lt.le hi
    (inf_le_left.trans (show M ≤ normalizer (localModule T M : Set G) from
      le_normalizer_conjugateSpanBy _ _))
    (inf_le_right.trans (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)))

/-- Odd defining exponents greater than one are impossible for a normal
source component. The Borel marking and quadratic action are constructed. -/
theorem source_normal_component_odd_field_false
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : (K.subgroupOf H).Normal)
    {f : ℕ} (hf : 1 < f) (ho : Odd f) (hm : SourceModel (K ⧸ pCore 2 K) f) : False := by
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
  have hcalc := OriginalModule.Normal.fixedSpace_le_of_quadratic_actor
    a.representation D (A.map q) hz hs hAE hAQ hbound hAD
    (hm.transport ((centerQuotientEquiv hz).trans ec.symm)) hf ho B ⟨Pq,rfl⟩
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

/-- The field-independent PSL₂ row at odd nonbinary exponent is excluded
on the original relative normal component. -/
theorem source_normal_component_not_odd_psl_two
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : (K.subgroupOf H).Normal) {f : ℕ} (hf : 1 < f) (ho : Odd f) :
    ¬ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f) := by
  rintro ⟨F,_,_,hF,⟨eF⟩⟩
  exact source_normal_component_odd_field_false hG T hempty hM hunique hmany hcard e hab hsolv
    H hH K hKH hK hn hf ho (.linearTwo F hF eF)

/-- The same source contradiction excludes the PSL₃ row at odd nonbinary
exponent, preserving its actual field and quotient isomorphism. -/
theorem source_normal_component_not_odd_psl_three
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : (K.subgroupOf H).Normal) {f : ℕ} (hf : 1 < f) (ho : Odd f) :
    ¬ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 (2 ^ f) := by
  rintro ⟨F,_,_,hF,⟨eF⟩⟩
  exact source_normal_component_odd_field_false hG T hempty hM hunique hmany hcard e hab hsolv
    H hH K hKH hK hn hf ho (.linearThree F hF eF)

/-- The unitary matrix-field convention is retained: f is the exponent
of the fixed field, and the matrix field has order (2^f)^2. -/
theorem source_normal_component_not_odd_psu_three
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : (K.subgroupOf H).Normal) {f : ℕ} (hf : 1 < f) (ho : Odd f) :
    ¬ ClassicalGroup.IsPSU (K ⧸ pCore 2 K) 3 (2 ^ f) := by
  rintro ⟨F,_,_,J,hF,hconj,⟨eF⟩⟩
  exact source_normal_component_odd_field_false hG T hempty hM hunique hmany hcard e hab hsolv
    H hH K hKH hK hn hf ho (.unitary F J hF hconj eF)

/-- The native derived symplectic carrier has no odd nonbinary defining
exponent on a normal source component. -/
theorem source_normal_component_not_odd_sp_four
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : (K.subgroupOf H).Normal) {f : ℕ} (hf : 1 < f) (ho : Odd f) :
    ¬ Chapter13.Section08.Components.Models.IsSp4DerivedAt (K ⧸ pCore 2 K) (2 ^ f) := by
  rintro ⟨F,_,_,hF,⟨eF⟩⟩
  exact source_normal_component_odd_field_false hG T hempty hM hunique hmany hcard e hab hsolv
    H hH K hKH hK hn hf ho (.symplecticFour F hF eF)

/-- Every nonabelian Suzuki model has odd defining exponent greater than
one, so the entire normal Suzuki branch is excluded. -/
theorem source_normal_component_not_suzuki
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : (K.subgroupOf H).Normal) {m : ℕ} (hm : 0 < m)
    (eK : (K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) : False :=
  source_normal_component_odd_field_false hG T hempty hM hunique hmany hcard e hab hsolv
    H hH K hKH hK hn (by omega : 1 < 2 * m + 1) ⟨m,rfl⟩ (.suzuki m hm rfl eK)

/-- The normal-component list after the actual Borel fixed-space argument.
The remaining even exponents and G₂ rows are separate source obligations. -/
@[expose] def NormalEvenLieQuotientModels (D : Type*) [Group D] : Prop :=
  (∃ f : ℕ, 2 ≤ f ∧ Even f ∧ ClassicalGroup.IsPSL D 2 (2 ^ f)) ∨
  (∃ f : ℕ, 2 ≤ f ∧ Even f ∧ ClassicalGroup.IsPSU D 3 (2 ^ f)) ∨
  (∃ f : ℕ, 1 ≤ f ∧ (f = 1 ∨ Even f) ∧ ClassicalGroup.IsPSL D 3 (2 ^ f)) ∨
  (∃ f : ℕ, 1 ≤ f ∧ (f = 1 ∨ Even f) ∧
    Chapter13.Section08.Components.Models.IsSp4DerivedAt D (2 ^ f)) ∨
  (∃ f : ℕ, 2 ≤ f ∧ Chapter13.Section08.Components.Models.IsG2DerivedAt D (2 ^ f))

/-- The model catalogue and all Borel inputs are discharged on the original
normal component; no natural-module or fixation callback remains. -/
theorem source_normal_component_even_lie_models
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : (K.subgroupOf H).Normal) : NormalEvenLieQuotientModels (K ⧸ pCore 2 K) := by
  have hm := source_component_low_rank_lie_models hG T hempty hM hunique hmany hcard e hsolv hab
    H hH K hKH hK
  rcases hm with hb | ⟨f,hf,hfM⟩ | ⟨f,hf,hfM⟩ | hg
  · cases hb with
    | linear f hf hfM =>
      refine Or.inl ⟨f,hf,?_,hfM⟩
      exact (Nat.even_or_odd f).resolve_right fun ho =>
        source_normal_component_not_odd_psl_two hG T hempty hM hunique hmany hcard e hab hsolv
          H hH K hKH hK hn (by omega) ho hfM
    | unitary f hf hfM =>
      refine Or.inr (Or.inl ⟨f,hf,?_,hfM⟩)
      exact (Nat.even_or_odd f).resolve_right fun ho =>
        source_normal_component_not_odd_psu_three hG T hempty hM hunique hmany hcard e hab hsolv
          H hH K hKH hK hn (by omega) ho hfM
    | suzuki m hm he =>
      exact (source_normal_component_not_suzuki hG T hempty hM hunique hmany hcard e hab hsolv
        H hH K hKH hK hn (by omega) he.some).elim
  · refine Or.inr (Or.inr (Or.inl ⟨f,hf,?_,hfM⟩))
    by_cases he : f = 1
    · exact Or.inl he
    · exact Or.inr ((Nat.even_or_odd f).resolve_right fun ho =>
        source_normal_component_not_odd_psl_three hG T hempty hM hunique hmany hcard e hab hsolv
          H hH K hKH hK hn (by omega) ho hfM)
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨f,hf,?_,hfM⟩)))
    by_cases he : f = 1
    · exact Or.inl he
    · exact Or.inr ((Nat.even_or_odd f).resolve_right fun ho =>
        source_normal_component_not_odd_sp_four hG T hempty hM hunique hmany hcard e hab hsolv
          H hH K hKH hK hn (by omega) ho hfM)
  · exact Or.inr (Or.inr (Or.inr (Or.inr hg)))

/-- Instantiate the refined normal catalogue at the unchanged terminal Mc. -/
theorem terminal_normal_component_even_lie_models
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (hn : (K.subgroupOf Mc).Normal) : NormalEvenLieQuotientModels (K ⧸ pCore 2 K) :=
  source_normal_component_even_lie_models hG T hempty hM hunique hmany hcard e hab hsolv Mc
    (terminal_outside hG T hempty hM hunique hmany hcard e) K hKM hK hn

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification.Sieve
