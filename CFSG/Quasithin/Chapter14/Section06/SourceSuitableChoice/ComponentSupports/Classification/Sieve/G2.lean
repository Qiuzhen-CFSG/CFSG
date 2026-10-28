module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Classification.Sieve.Exchanged
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.NormalG2

/-!
# The complete terminal G₂ exclusion

The original component has three-rank at least two, which forces relative
normality. Restrict to the literal J=KT and its original span action. The
proved natural recognition and Borel fixed-space theorem fix the generating
seed under the component; normality extends this to the whole span, contrary
to faithful action. The binary and even-degree exclusions already proved in
the sieve reduce the derived-model row to this nonbinary argument.

The actual source application retains K/O₂(K), the placed quadratic actor,
and the terminal H=Mc. Its remaining catalogue has only the even linear and
unitary rows, binary PSL₃, and A₆. Their remaining exclusions and the natural
support assembly stay with qt-e-suitable-component-supports. Original 14.6.18
remains the allowed input owned by qt-e-14625-source.

Source: Aschbacher--Smith 14.6.20, printed p.1037, using B.4.2(4), p.86.
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

/-- The actual nonbinary G₂ component fixes the whole original span, a contradiction. -/
theorem source_normal_component_g2_false
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : (K.subgroupOf H).Normal)
    (F : ChapterB.QuasisimpleSource.BinaryField) (hf : 1 < F.degree)
    (eF : (K ⧸ pCore 2 K) ≃* Atlas.G2.Model F.Carrier) : False := by
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
  have hcalc := Modules.NormalG2.fixedSpace_le_of_quadratic_actor
    a.representation D hz hs (A.map q) hAE hAQ hbound hAD F hf
    ((centerQuotientEquiv hz).trans (ec.symm.trans eF)) B ⟨Pq,rfl⟩
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


/-- The actual derived G₂ model has cubic rank at least two, so its component is normal. -/
theorem source_component_g2_normal
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    {f : ℕ} (hm : IsG2DerivedAt (K ⧸ pCore 2 K) (2 ^ f)) :
    (K.subgroupOf H).Normal := by
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  have hr : 2 ≤ primeRank 3 (K ⧸ pCore 2 K) := by
    rw [primeRank_equiv 3 eF]
    exact Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.g2
  exact (normal_subgroupOf_iff_le_normalizer hKH).mpr
    (source_component_normal_of_quotient_threeRank hG T hempty hM hunique hmany hcard e hab hsolv
      H hH K hKH hK hr)

/-- The entire G₂ row is excluded on the original component quotient. -/
theorem source_component_not_g2
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    {f : ℕ} (hf : 1 ≤ f) : ¬ IsG2DerivedAt (K ⧸ pCore 2 K) (2 ^ f) := by
  intro hm
  have hn := source_component_g2_normal hG T hempty hM hunique hmany hcard e hab hsolv
    H hH K hKH hK hm
  have hf3 := (source_component_g2_odd_degree hG T hempty hM hunique hmany hcard e hab hsolv
    H hH K hKH hK hf hm).1
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let F' : ChapterB.QuasisimpleSource.BinaryField :=
    { Carrier := F, degree := f, degree_pos := by omega, card_eq := hF }
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact (by norm_num : 2 = 2 ^ 1) ▸ Nat.pow_lt_pow_right (by decide) (by omega)
  let : Group.IsPerfect (Atlas.G2.Model F) := Atlas.G2.isPerfect hlarge
  let ed : commutator (Atlas.G2.Model F) ≃* Atlas.G2.Model F :=
    (MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top).trans Subgroup.topEquiv
  exact source_normal_component_g2_false hG T hempty hM hunique hmany hcard e hab hsolv
    H hH K hKH hK hn F' (by change 1 < f; omega) (eF.trans ed)

/-- After the G₂ exclusion, only the even linear/unitary rows and the two
terminal binary models remain in the relatively normal branch. -/
@[expose] def NormalLinearUnitaryQuotientModels (D : Type*) [Group D] : Prop :=
  (∃ f : ℕ, 2 ≤ f ∧ Even f ∧ ClassicalGroup.IsPSL D 2 (2 ^ f)) ∨
  (∃ f : ℕ, 2 ≤ f ∧ Even f ∧ ClassicalGroup.IsPSU D 3 (2 ^ f)) ∨
  (∃ f : ℕ, 1 ≤ f ∧ (f = 1 ∨ Even f) ∧ ClassicalGroup.IsPSL D 3 (2 ^ f)) ∨
  Nonempty (D ≃* alternatingGroup (Fin 6))

/-- The narrowed catalogue is derived from the original source hypotheses. -/
theorem source_normal_component_linear_unitary_models
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : (K.subgroupOf H).Normal) : NormalLinearUnitaryQuotientModels (K ⧸ pCore 2 K) := by
  have hm := source_normal_component_remaining_models hG T hempty hM hunique hmany hcard e hab hsolv
    H hH K hKH hK hn
  rcases hm with h2 | hu | h3 | ha | ⟨f,hf,_,hg⟩
  · exact Or.inl h2
  · exact Or.inr (Or.inl hu)
  · exact Or.inr (Or.inr (Or.inl h3))
  · exact Or.inr (Or.inr (Or.inr ha))
  · exact (source_component_not_g2 hG T hempty hM hunique hmany hcard e hab hsolv
      H hH K hKH hK (by omega) hg).elim

/-- The terminal H=Mc has the normal remainder or an actual exchanged PSL₃(2)
marking with the genuine original Sylow diagram action. -/
theorem terminal_component_normal_linear_unitary_or_exchanged
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent) :
    ((K.subgroupOf Mc).Normal ∧ NormalLinearUnitaryQuotientModels (K ⧸ pCore 2 K)) ∨
    (¬ (K.subgroupOf Mc).Normal ∧
      ∃ a : (K ⧸ pCore 2 K) ≃* Matrix.PSL3Two.PSL, ComponentParabolicSwap T K a) := by
  by_cases hn : (K.subgroupOf Mc).Normal
  · exact Or.inl ⟨hn,source_normal_component_linear_unitary_models
      hG T hempty hM hunique hmany hcard e hab hsolv Mc
        (terminal_outside hG T hempty hM hunique hmany hcard e) K hKM hK hn⟩
  · exact Or.inr ⟨hn,terminal_nonnormal_component_linear_three_diagram
      hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hn⟩

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification.Sieve
