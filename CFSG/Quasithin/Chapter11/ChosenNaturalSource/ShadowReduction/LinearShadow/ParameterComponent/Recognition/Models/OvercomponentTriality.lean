module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.OvercomponentG2
public import Theory.SpecificGroups.Triality.OddSupplement
public import Theory.SpecificGroups.Triality.FullParabolicActions.CyclicQuotient
public import Theory.SpecificGroups.Triality.ElementaryNine

/-!
# Triality overcomponents of the original source component

A proper full-Sylow local component in the genuine binary triality carrier
lies in a root parabolic. Perfectness puts it in the actual local factor,
and the full Sylow lies there too. Projection through the factor's literal
two-core preserves the smaller component's own two-core quotient. Rank-one
Sylow rigidity identifies that quotient as PSL₂(2^f) or PSL₂(2^(3f)).
The first alternative requires f ≥ 2: at f = 1 its root quotient is solvable.
Thus the argument includes ³D₄(2), without assuming perfectness of its local
factors or confusing the two root fields.

The original seed itself has no triality quotient. Cubic rank excludes
the paired branch; in the normal branch, its actual image in H/O₂(H)
contradicts minimal parabolicity. Hence a triality containing quotient
forces proper containment and the two literal PSL₂ alternatives above.
Suzuki seeds and all higher-rank star images exclude such containers.
The final theorem connects this calculation to the original seed catalogue,
retaining its quotient maps and its independent generation-parameter bound.

The elementary full-root lift, recognition at the actual generation minimum,
remaining containing-model and FF exclusions, and paired/doubled assembly
remain required for 11.3.5–6. No unconditional source conclusion is asserted.

Source: Aschbacher–Smith A.3.12, printed pp.47–48, and 11.3.5(1),
pp.771–772 (refs/quasithin.pdf). The imported root calculations use the genuine
Geck D₄ graph-field carrier and retain their existing source attribution.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Models
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics

private theorem perfect_le_triality_local (P : Parameters) (hp : P.prime = 2)
    (a : Node) (B : Subgroup (Carrier P)) [Group.IsPerfect B]
    (hB : B ≤ parabolic P a) : B ≤ localFactor P a := by
  let X := B.subgroupOf (parabolic P a)
  let : Group.IsPerfect X := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hB).symm.toMonoidHom) (subgroupOfEquivOfLe hB).symm.surjective
  let : IsCyclic (parabolic P a ⧸ (localFactor P a).subgroupOf (parabolic P a)) :=
    parabolic_quotient_isCyclic P hp a
  let : CommGroup (parabolic P a ⧸ (localFactor P a).subgroupOf (parabolic P a)) :=
    IsCyclic.commGroup
  have h := le_of_isPerfect_of_solvable_quotient X
    ((localFactor P a).subgroupOf (parabolic P a))
  intro x hx
  exact h (show (⟨x,hB hx⟩ : parabolic P a) ∈ X from hx)

private theorem triality_local_containment {f : ℕ} (hf : 1 ≤ f)
    (S : Sylow 2 (BinaryCarrier f (by omega)))
    (B : Subgroup (BinaryCarrier f (by omega)))
    (hB : B ∈ localCComponents S) (hp : B ≠ ⊤) :
    ∃ (g : BinaryCarrier f (by omega)) (a : Node),
      B.map (MulAut.conj g).toMonoidHom ≤ localFactor (binaryParameters f (by omega)) a ∧
      (S : Subgroup (BinaryCarrier f (by omega))).map (MulAut.conj g).toMonoidHom ≤
        localFactor (binaryParameters f (by omega)) a := by
  let P := binaryParameters f (by omega)
  have hproper : B ⊔ (S : Subgroup (Carrier P)) ≠ ⊤ := by
    intro he
    change (B.subgroupOf (B ⊔ (S : Subgroup (Carrier P)))).IsCComponent at hB
    rw [he] at hB
    have hb : B.IsCComponent := by
      simpa only [map_subgroupOf_eq_of_le le_top] using hB.map_subtype (.top)
    exact hp ((hb.subnormal.eq_bot_or_top_of_isSimpleGroup inferInstance).resolve_left hb.ne_bot)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Carrier P) S (unipotentSylow P rfl)
  let c := MulAut.conj g
  let S' := S.mapSurjective (f := c.toMonoidHom) c.surjective
  let B' := B.map c.toMonoidHom
  have hS : (S : Subgroup (Carrier P)).map c.toMonoidHom = unipotent P :=
    congrArg Sylow.toSubgroup hg
  have hmap : (B ⊔ (S : Subgroup (Carrier P))).map c.toMonoidHom ≠ ⊤ := by
    intro he
    apply hproper
    apply map_injective (f := c.toMonoidHom) c.injective
    rw [he,map_top_of_surjective _ c.surjective]
  obtain ⟨a,ha⟩ := _root_.Triality.Standard.OddSupplement.le_parabolic f (by omega) _
    (hS ▸ map_mono le_sup_right) hmap
  let : Group.IsSolvable c.toMonoidHom.ker := by
    rw [c.toMonoidHom.ker_eq_bot_iff.mpr c.injective]
    infer_instance
  have hb : B' ∈ localCComponents S' :=
    Chapter1.Section02.localCComponents_map_of_solvable_ker hB c.toMonoidHom
  let e := subgroupOfEquivOfLe (show B' ≤ B' ⊔ (S' : Subgroup (Carrier P)) from le_sup_left)
  let := hb.perfect
  let : Group.IsPerfect B' := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hBP : B' ≤ parabolic P a := (map_mono le_sup_left).trans ha
  have hSP : (S' : Subgroup (Carrier P)) ≤ parabolic P a := (map_mono le_sup_right).trans ha
  have hBK := perfect_le_triality_local P rfl a B' hBP
  have hSK := sylow_le_localFactor P a S' hSP
  exact ⟨g,a,hBK,hSK⟩

private theorem root_quotient_image {X Y : Type*}
    [Group X] [Finite X] [Group Y] [Finite Y]
    (S : Sylow 2 X) (B K : Subgroup X) (hB : B ∈ localCComponents S)
    (hBK : B ≤ K) (hSK : (S : Subgroup X) ≤ K)
    (e : (K ⧸ pCore 2 K) ≃* Y) :
    ∃ (P : Sylow 2 Y) (C : Subgroup Y), C ∈ localCComponents P ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* (C ⧸ pCore 2 C)) := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let : Group.IsNilpotent f.ker := (hk ▸ (pCore_isPGroup (p := 2) (G := K))).isNilpotent
  let D := B.subgroupOf K
  let P := (S.subtype hSK).mapSurjective (f := f) hf
  let C := D.map f
  have hl : D ∈ localCComponents (S.subtype hSK) := local_restrict hB hBK
  have hc : C ∈ localCComponents P :=
    Chapter1.Section02.localCComponents_map_of_solvable_ker hl f
  let d := subgroupOfEquivOfLe hBK
  let dq := QuotientGroup.congr _ _ d (pCore_map_iso 2 d)
  have hker : IsPGroup 2 (f.subgroupMap D).ker := by
    rw [ker_subgroupMap,hk]
    exact pCore_isPGroup.comap_subtype
  exact ⟨P,C,hc,⟨dq.symm.trans ((f.subgroupMap D).quotientPCoreEquivOfSurjective
    (f.subgroupMap_surjective D) hker)⟩⟩

private theorem binary_rank_one_local_quotient {F : Type}
    [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hf : 1 ≤ f) (hF : Nat.card F = 2 ^ f)
    (P : Sylow 2 PSL(2,F)) (C : Subgroup PSL(2,F))
    (hc : C ∈ localCComponents P) :
    2 ≤ f ∧ Nonempty ((C ⧸ pCore 2 C) ≃* PSL(2,F)) := by
  have hf2 : 2 ≤ f := by
    by_contra hn
    have hf1 : f = 1 := by omega
    let : Group.IsSolvable PSL(2,F) :=
      Theory.PSL2.OuterSolvable.isSolvable_of_card_two (by simpa [hf1] using hF)
    exact hc.not_isSolvable inferInstance
  have hcard : 4 ≤ Nat.card F := by
    rw [hF]
    exact (show 2 ^ 2 ≤ 2 ^ f from Nat.pow_le_pow_right (by decide) hf2)
  let : IsSimpleGroup PSL(2,F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hcard
  let : Group.IsPerfect PSL(2,F) := GorensteinWalter.psl2_isPerfect_of_card_gt_three F (by omega)
  let : IsSimpleGroup (⊤ : Subgroup PSL(2,F)) := topEquiv.isSimpleGroup
  let : Group.IsPerfect (⊤ : Subgroup PSL(2,F)) := Group.IsPerfect.ofSurjective
    (f := (topEquiv : (⊤ : Subgroup PSL(2,F)) ≃* PSL(2,F)).symm.toMonoidHom)
    topEquiv.symm.surjective
  have ht : (⊤ : Subgroup PSL(2,F)).IsCComponent :=
    Subgroup.isCComponent_of_isSimpleGroup_of_isPerfect .top
  have hm : ClassicalGroup.IsPSL PSL(2,F) 2 (2 ^ f) :=
    ⟨F,inferInstance,inferInstance,hF,⟨MulEquiv.refl _⟩⟩
  have he : C = ⊤ := eq_of_bender_containing_component P hc ht le_top
    (.linear f hf2 (hm.of_mulEquiv topEquiv))
  let a : C ≃* PSL(2,F) := (MulEquiv.subgroupCongr he).trans topEquiv
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  have hz : pCore 2 PSL(2,F) = ⊥ := by
    rcases (inferInstance : (pCore 2 PSL(2,F)).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · let : Group.IsNilpotent (⊤ : Subgroup PSL(2,F)) := ht ▸ pCore_isNilpotent (p := 2)
      let : Group.IsSolvable PSL(2,F) := Group.isSolvable_of_surjective
        (f := (topEquiv : (⊤ : Subgroup PSL(2,F)) ≃* PSL(2,F)).toMonoidHom)
        topEquiv.surjective
      exact (Group.IsPerfect.not_isSolvable PSL(2,F) inferInstance).elim
  exact ⟨hf2,⟨aq.trans ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot)⟩⟩

/-- A proper local component in genuine binary triality has the quotient
of one of the two root nodes. The central node is excluded at field two. -/
theorem triality_proper_local_models {f : ℕ} (hf : 1 ≤ f)
    (P : Sylow 2 (BinaryCarrier f (by omega)))
    (B : Subgroup (BinaryCarrier f (by omega)))
    (hB : B ∈ localCComponents P) (hp : B ≠ ⊤) :
    (2 ≤ f ∧ ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2 ^ f)) ∨
      ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2 ^ (3 * f)) := by
  obtain ⟨g,a,hBK,hPK⟩ := triality_local_containment hf P B hB hp
  let c := MulAut.conj g
  let : Group.IsSolvable c.toMonoidHom.ker := by
    rw [c.toMonoidHom.ker_eq_bot_iff.mpr c.injective]
    infer_instance
  let P' := P.mapSurjective (f := c.toMonoidHom) c.surjective
  let B' := B.map c.toMonoidHom
  have hb : B' ∈ localCComponents P' :=
    Chapter1.Section02.localCComponents_map_of_solvable_ker hB c.toMonoidHom
  let d := c.subgroupMap B
  let dq := QuotientGroup.congr _ _ d (pCore_map_iso 2 d)
  cases a with
  | arms =>
    obtain ⟨S,C,hC,⟨e⟩⟩ := root_quotient_image P' B' _ hb hBK hPK
      (localFactorArmsQuotientEquivPSL2 (binaryParameters f (by omega)) rfl)
    have hF : Nat.card (ExtensionField (binaryParameters f (by omega))) = 2 ^ (3 * f) := by
      rw [card_extensionField]
      change (2 ^ f) ^ 3 = 2 ^ (3 * f)
      rw [← pow_mul,Nat.mul_comm f 3]
    obtain ⟨_,⟨b⟩⟩ := binary_rank_one_local_quotient (by omega) hF S C hC
    exact .inr ⟨_,inferInstance,inferInstance,hF,⟨(dq.trans e).trans b⟩⟩
  | central =>
    obtain ⟨S,C,hC,⟨e⟩⟩ := root_quotient_image P' B' _ hb hBK hPK
      (localFactorCentralQuotientEquivPSL2 (binaryParameters f (by omega)) rfl)
    have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
    obtain ⟨hf2,⟨b⟩⟩ := binary_rank_one_local_quotient hf hF S C hC
    exact .inl ⟨hf2,_,inferInstance,inferInstance,hF,⟨(dq.trans e).trans b⟩⟩
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Models

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H K J : Subgroup G}

/-- The original component has no binary triality quotient, including the
field of order two. Both relative-normality branches are discharged. -/
theorem ComponentSeed.not_triality_model (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    {f : ℕ} (hf : 1 ≤ f) :
    ¬ Triality.Standard.IsTrialityGroupAt (2 ^ f) (K ⧸ pCore 2 K) := by
  intro hm
  obtain ⟨a⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff _ f hf).mp hm
  have hn : (K.subgroupOf H).Normal := by
    by_contra hn
    have hu : primeRank 3 (K ⧸ pCore 2 K) ≤ 1 := by
      rcases s.paired_binary_models h pr hc hs hn with ⟨d,hd,_,hlin⟩ | ⟨m,hm,_,⟨e⟩⟩
      · exact Models.odd_rank_of_binary_linear (by omega) hlin 3 (by decide) (by decide)
      · exact Models.odd_rank_of_suzuki (by omega) e 3 (by decide) (by decide)
    have hl : 2 ≤ primeRank 3 (Triality.Standard.BinaryCarrier f hf) := by
      let E := Triality.Standard.ElementaryNine.subgroup (Triality.Standard.binaryParameters f hf) rfl
      let : IsElementaryAbelian 3 E := Triality.Standard.ElementaryNine.subgroup_elementary _ _
      exact IsElementaryAbelian.primeRank_ge_of_card E
        (Triality.Standard.ElementaryNine.card_subgroup _ _)
    rw [primeRank_equiv 3 a] at hu
    omega
  let P := T.subtype h.outside.1.1.2
  let q := QuotientGroup.mk' (pCore 2 H)
  let B := K.subgroupOf H
  let I := B.map q
  let := s.quasisimple
  let : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv s.intrinsicQuotientEquiv
  let : B.Normal := hn
  let : I.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let e := s.intrinsicQuotientEquiv.trans (cComponentTwoCoreQuotientEquiv s.component.2)
  have hgen : I ⊔ (P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H)) :
      Subgroup (H ⧸ pCore 2 H)) = ⊤ := by
    change B.map q ⊔ (P : Subgroup H).map q = ⊤
    rw [← Subgroup.map_sup,s.intrinsic_supplement h.outside.1.1.2,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hmin := ChapterB.minimalParabolic_surjective P
    (outside_minimalParabolic h (weakClosure_not_le_core_of_counterexample h pr hc))
    q (QuotientGroup.mk'_surjective _) (by
      rw [QuotientGroup.ker_mk']
      exact pCore_isPGroup.le_sylow_of_normal P)
  exact ChapterE.BinaryExclusions.not_triality_binary
    (P.mapSurjective (QuotientGroup.mk'_surjective _)) I hgen hmin f hf
    ((Triality.Standard.isTrialityGroupAt_binary_iff _ f hf).mpr ⟨e.symm.trans a⟩)

/-- A binary triality overcomponent forces a proper seed with a literal
PSL₂ quotient. The central and arms nodes retain degrees f and 3f. -/
theorem ComponentSeed.linear_models_of_triality_overcomponent (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hKJ : K ≤ J)
    {f : ℕ} (hf : 1 ≤ f)
    (hm : Triality.Standard.IsTrialityGroupAt (2 ^ f) (J ⧸ pCore 2 J)) :
    K < J ∧ ((2 ≤ f ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f)) ∨
      ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ (3 * f))) := by
  have hp : K < J := lt_of_le_of_ne hKJ (by
    intro he
    subst J
    exact s.not_triality_model h pr hc hs (by omega) hm)
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff _ f (by omega)).mp hm
  obtain ⟨P,C,hC,hproper,⟨a⟩⟩ := Models.proper_local_quotient_image
    T (s.mem_local_family h).1 hJ.1 hp e
  refine ⟨hp,?_⟩
  rcases Models.triality_proper_local_models hf P C hC hproper with ⟨hf2,hcentral⟩ | harms
  · exact .inl ⟨hf2,hcentral.of_mulEquiv a⟩
  · exact .inr (harms.of_mulEquiv a)

/-- Suzuki seeds have no binary triality overcomponent. -/
theorem ComponentSeed.not_triality_overcomponent_of_suzuki
    (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hKJ : K ≤ J)
    {m : ℕ} (hm : 1 ≤ m)
    (he : Nonempty ((K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))
    {f : ℕ} (hf : 1 ≤ f) :
    ¬ Triality.Standard.IsTrialityGroupAt (2 ^ f) (J ⧸ pCore 2 J) := by
  intro htriality
  rcases (s.linear_models_of_triality_overcomponent h pr hc hs hJ hKJ hf htriality).2 with
    ⟨hf2,hcentral⟩ | harms
  · exact s.not_linear_overcomponent_of_suzuki h (s.mem_local_family h) le_rfl hm he f hf2 hcentral
  · exact s.not_linear_overcomponent_of_suzuki h (s.mem_local_family h) le_rfl hm he
      (3 * f) (by omega) harms

/-- Every higher-rank star image excludes binary triality containers.
The actual central star map is retained; it is not identified with K/O₂(K). -/
theorem ComponentSeed.not_triality_overcomponent_of_higher_rank_image
    (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hKJ : K ≤ J)
    (R : Subgroup H) [R.Normal] (hR : pCore 2 H ≤ R)
    [Nontrivial ((K.subgroupOf H).map (QuotientGroup.mk' R))]
    {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSU ((K.subgroupOf H).map (QuotientGroup.mk' R)) 3 (2 ^ n) ∨
      ClassicalGroup.IsPSL ((K.subgroupOf H).map (QuotientGroup.mk' R)) 3 (2 ^ n) ∨
      ClassicalGroup.IsPSp ((K.subgroupOf H).map (QuotientGroup.mk' R)) 2 (2 ^ n))
    {f : ℕ} (hf : 1 ≤ f) :
    ¬ Triality.Standard.IsTrialityGroupAt (2 ^ f) (J ⧸ pCore 2 J) := by
  intro htriality
  rcases (s.linear_models_of_triality_overcomponent h pr hc hs hJ hKJ hf htriality).2 with
    ⟨hf2,hcentral⟩ | harms
  · exact s.not_linear_overcomponent_of_higher_rank_image h (s.mem_local_family h) le_rfl
      R hR hn hm f hf2 hcentral
  · exact s.not_linear_overcomponent_of_higher_rank_image h (s.mem_local_family h) le_rfl
      R hR hn hm (3 * f) (by omega) harms

/-- The original seed catalogue now has a literal triality containing-row
recognition, alongside the previously excluded binary and G₂ rows. -/
theorem exists_componentSeed_with_triality_containing_sieve
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary) :
    let P := T.subtype h.outside.1.1.2
    let hP := outside_minimalParabolic h (weakClosure_not_le_core_of_counterexample h pr hc)
    ∃ K J : Subgroup G, ComponentSeed T H K ∧ K ≤ J ∧
      J ∈ Chapter1.LStar G (T : Subgroup G) ∧
      J ∈ MainForward.faithfulLocalComponents T ∧
      ¬ J ≤ normalizer (L : Set G) ∧ ⁅sourceZ T,J⁆ ≠ ⊥ ∧
      (∀ d : ℕ, (d = 3 ∨ d = 4 ∨ d = 5) →
        ¬ ClassicalGroup.IsPSL (J ⧸ pCore 2 J) d 2) ∧
      (∀ f : ℕ, 2 ≤ f → ClassificationModels.IsG2At (J ⧸ pCore 2 J) (2 ^ f) →
        K < J ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f)) ∧
      (∀ f : ℕ, 1 ≤ f → Triality.Standard.IsTrialityGroupAt (2 ^ f) (J ⧸ pCore 2 J) →
        K < J ∧ ((2 ≤ f ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f)) ∨
          ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ (3 * f)))) ∧
      (((∃ f : ℕ, 2 ≤ f ∧ ChapterE.generationParameter H ≤ f ∧
          ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f)) ∨
        (∃ m : ℕ, 1 ≤ m ∧ ChapterE.generationParameter H ≤ 2 * m + 1 ∧
          Nonempty ((K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))) ∧
          solvableRadical H = pCore 2 H ∨
        (K.subgroupOf H).Normal ∧
          (let I := (K.subgroupOf H).map (QuotientGroup.mk' (ChapterB.minimalParabolicCore P hP))
           ∃ f : ℕ, 2 ≤ f ∧ ChapterE.generationParameter H ≤ f ∧
             (ClassicalGroup.IsPSU I 3 (2 ^ f) ∨ ClassicalGroup.IsPSL I 3 (2 ^ f) ∨
               ClassicalGroup.IsPSp I 2 (2 ^ f)))) := by
  obtain ⟨K,J,s,hKJ,hJ,hfaith,ho,hm,hbin,hg2,hcases⟩ :=
    exists_componentSeed_with_binary_and_g2_containing_sieve h pr hc hs
  exact ⟨K,J,s,hKJ,hJ,hfaith,ho,hm,hbin,hg2,
    fun _ hf ht => s.linear_models_of_triality_overcomponent h pr hc hs hJ.1 hKJ hf ht,hcases⟩
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
