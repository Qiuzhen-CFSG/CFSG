module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.HomogeneousChief

/-!
# Single natural chief factors in all B.5.1 source families

At half ratio, full B.4.2 places the same minimal offender inside the SL3
component. Each faithful irreducible component submodule has ratio at least
one half on that component. Two distinct such submodules are disjoint, so
their actual product has ratio at least one, contradicting the common actor's
half-ratio bound. A.1.42 then gives a single irreducible natural chief factor.

Combining this with the proved binary branch yields one actual LA-chief flag
from the original reducible B.5.1 hypotheses, every noncentral factor faithful
and a single natural component module. No constituent homogeneity, marking
alignment, or B.5.1 classifier is assumed. The remaining source work is the
socle/maximal-submodule induction, central factors, and G = L.

Source: Aschbacher--Smith B.5.1, pp.100–101, (+) through the assertion that
all U_i are irreducible natural L-modules; A.1.42, p.32.
-/

@[expose] public noncomputable section
open Representation Representation.BinaryOffender Subgroup Theory.GroupTheory
open scoped ENNReal MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
universe u v

theorem generated_of_half {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) {L H : Subgroup G}
    (h : SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L H)
    (hq : quadraticRatio ρ ≤ 1 / 2) : H = L := by
  cases h with
  | linearThree _ hg _ _ => exact hg
  | binaryLinear _ _ hg _ _ => exact hg
  | linearTwo _ _ _ _ he => rw [he] at hq; norm_num at hq
  | symplectic _ _ _ _ he =>
    have hr := ENNReal.toReal_mono (by norm_num) hq
    rw [he] at hr
    norm_num [ENNReal.toReal_div] at hr
  | symplecticTwo _ he =>
    have hr := ENNReal.toReal_mono (by norm_num) hq
    rw [he] at hr
    norm_num [ENNReal.toReal_div] at hr
  | g2 _ _ _ _ _ he => rw [he] at hq; norm_num at hq
  | g2Two _ _ he => rw [he] at hq; norm_num at hq
  | symmetric _ _ _ _ he => rw [he] at hq; norm_num at hq
  | alternatingSix _ _ _ he => rw [he] at hq; norm_num at hq
  | alternatingSeven _ _ _ _ _ he => rw [he] at hq; norm_num at hq
  | tripleSix _ _ he => rw [he] at hq; norm_num at hq
  | orthogonalSix _ _ _ _ he => rw [he] at hq; norm_num at hq
  | symmetricEight _ _ he =>
    have hr := ENNReal.toReal_mono (by norm_num) hq
    rw [he] at hr
    norm_num [ENNReal.toReal_div] at hr
  | exteriorFive _ _ _ _ _ he => rw [he] at hq; norm_num at hq

private theorem one_le_ratio_prod {G X Y : Type*} [Group G]
    [AddCommGroup X] [Module (ZMod 2) X] [AddCommGroup Y] [Module (ZMod 2) Y]
    [FiniteDimensional (ZMod 2) X] [FiniteDimensional (ZMod 2) Y]
    (ρ : Representation (ZMod 2) G X) (σ : Representation (ZMod 2) G Y)
    (hρ : 1 / 2 ≤ quadraticRatio ρ) (hσ : 1 / 2 ≤ quadraticRatio σ) :
    1 ≤ quadraticRatio (ρ.prod σ) := by
  apply le_iInf
  intro A
  apply le_iInf
  rintro ⟨hA, hq⟩
  obtain ⟨hqρ, hqσ⟩ := (quadratic_prod_iff ρ σ A).mp hq
  have hρA : (1 / 2 : ℝ≥0∞) ≤ actionRatio ρ A :=
    hρ.trans (iInf_le_of_le A (iInf_le_of_le ⟨hA,hqρ⟩ le_rfl))
  have hσA : (1 / 2 : ℝ≥0∞) ≤ actionRatio σ A :=
    hσ.trans (iInf_le_of_le A (iInf_le_of_le ⟨hA,hqσ⟩ le_rfl))
  have hadd : actionRatio (ρ.prod σ) A = actionRatio ρ A + actionRatio σ A := by
    simp only [actionRatio, fixedCodim_prod, Nat.cast_add, ENNReal.add_div]
  rw [hadd]
  have he : (1 / 2 : ℝ≥0∞) + 1 / 2 = 1 := by
    rw [← ENNReal.add_div]
    norm_num only [one_add_one_eq_two]
    exact ENNReal.div_self (by norm_num) (by norm_num)
  exact he ▸ add_le_add hρA hσA

/-- At half ratio the same offender is inside C and every faithful irreducible
C-submodule has ratio at least one half for C itself. -/
theorem linearThree_common_offender {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    [Nontrivial V] (ρ : Representation (ZMod 2) G V)
    {K : GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    (C : Subgroup G) [IsQuasisimple C] (hC : IsSQTK K C)
    (hfit : generalizedFitting G = C) (hcore : pCore 2 G = ⊥)
    (hfaith : Function.Injective ρ) (hdec : FaithfulConstituentDecomposition ρ C)
    (F : BinaryField) (mark : C ≃* SL(3,F.Carrier)) (hq : quadraticRatio ρ ≤ 1 / 2) :
    ∃ B, IsMinimalBestOffender ρ B ∧ B ≤ C ∧ actionRatio ρ B ≤ 1 / 2 ∧
      ∀ W : Subrepresentation (ρ.comp C.subtype), IsIrreducible W.toRepresentation →
        Function.Injective W.toRepresentation → 1 / 2 ≤ quadraticRatio W.toRepresentation := by
  obtain ⟨B, hB, hb⟩ := exists_minimal_ratio ρ (by norm_num : (1 / 2 : ℝ≥0∞) ≤ 1) hq
  obtain ⟨W, hi, hf⟩ := hdec.exists_constituent ρ
  obtain ⟨hs, hc⟩ := constituent_classification ρ hK earlier C hC hfit hcore hfaith hB W hi hf
  have hratio := (constituent_ratio_le ρ hB W hs).trans hb
  have hgen := generated_of_half _ hc hratio
  have hBC := constituent_generation_contains_offender ρ C hfit hcore hB.1 W hs hgen
  refine ⟨B, hB, hBC, hb, ?_⟩
  intro U hiU hfU
  have hfitC : generalizedFitting C = ⊤ := generalizedFitting_eq_top_of_quasisimple
  let : IsQuasisimple (generalizedFitting C) := hfitC.symm ▸
    IsQuasisimple.of_mulEquiv (topEquiv : (⊤ : Subgroup C) ≃* C).symm
  have hiTop : IsIrreducible (U.toRepresentation.comp (⊤ : Subgroup C).subtype) :=
    (irreducible_comp_surjective_iff (topEquiv : (⊤ : Subgroup C) ≃* C).toMonoidHom
      topEquiv.surjective U.toRepresentation).mpr hiU
  have hiF : IsIrreducible (U.toRepresentation.comp (generalizedFitting C).subtype) := by
    rwa [hfitC]
  have hbest := bestOffender_on_subrepresentation (ρ.comp C.subtype) U (hB.1.subgroupOf ρ hBC)
  have hcase := earlier C U.toSubmodule U.toRepresentation hC inferInstance hfU hiF
    ⟨B.subgroupOf C,hbest⟩
  exact linearThree_half_le_ratio U.toRepresentation hcase F
    ((MulEquiv.subgroupCongr hfitC).trans ((topEquiv : (⊤ : Subgroup C) ≃* C).trans mark))

/-- In the SL3 branch two distinct irreducible component submodules already
cost ratio at least one. The actual half-ratio offender therefore forces
component homogeneity without any field-automorphism classification. -/
theorem linearThree_chief_homogeneous {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hi : IsIrreducible ρ)
    {K : GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (h36 : Chapter1.Section02.A36Input K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    (C : Subgroup G) [IsQuasisimple C] (hC : IsSQTK K C)
    (hfit : generalizedFitting G = C) (hcore : pCore 2 G = ⊥)
    (hfaith : Function.Injective ρ)
    (F : BinaryField) (mark : C ≃* SL(3,F.Carrier)) (hq : quadraticRatio ρ ≤ 1 / 2) :
    ∀ U W : Subrepresentation (ρ.comp C.subtype),
      IsIrreducible U.toRepresentation → IsIrreducible W.toRepresentation → U = W := by
  let : C.Normal := hfit ▸ generalizedFitting_normal (G := G)
  let := hi
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  have hc : Nat.card (center C) = 1 ∨ Nat.card (center C) = 3 := by
    apply center_order_of_a36 h36 hC
    apply (Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).mp
    apply bot_unique
    have hm : (pCore 2 C).map C.subtype ≤ pCore 2 G :=
      le_sSup ⟨ConjAct.normal_of_characteristic_of_normal, pCore_isPGroup.map C.subtype⟩
    exact hm.trans_eq hcore
  have hdec := faithful_constituent_decomposition ρ hfaith hi C hc
  obtain ⟨B, hB, hBC, hr, hl⟩ := linearThree_common_offender ρ hK earlier C hC hfit hcore hfaith
    hdec F mark hq
  have hbC : IsElementaryTwo (B.subgroupOf C) := (hB.1.subgroupOf ρ hBC).1
  have hqC : IsQuadratic (ρ.comp C.subtype) (B.subgroupOf C) := by
    intro a ha b hb v
    exact hB.isQuadratic ρ a.val ha b.val hb v
  have hrC : actionRatio (ρ.comp C.subtype) (B.subgroupOf C) ≤ 1 / 2 := by
    simpa only [actionRatio, fixedCodim_subgroupOf ρ hBC, rank_subgroupOf hBC] using hr
  intro U W hiU hiW
  by_contra heq
  have hU := (Subrepresentation.irreducible_iff_isAtom U).mp hiU
  have hW := (Subrepresentation.irreducible_iff_isAtom W).mp hiW
  have hfU := constituent_faithful ρ hfaith hi C hc U hU.ne_bot
  have hfW := constituent_faithful ρ hfaith hi C hc W hW.ne_bot
  have hdUW := hU.disjoint_of_ne hW heq
  have hdis : Disjoint U.toSubmodule W.toSubmodule := by
    apply Submodule.disjoint_def.mpr
    intro v hvU hvW
    have hm : v ∈ U ⊓ W := ⟨hvU, hvW⟩
    rw [hdUW.eq_bot] at hm
    exact hm
  have hp := (pair_ratio_le_actionRatio (ρ.comp C.subtype) U W hdis hbC hqC).trans hrC
  have hlo := one_le_ratio_prod U.toRepresentation W.toRepresentation (hl U hiU hfU) (hl W hiW hfW)
  have hbad := hlo.trans hp
  norm_num at hbad

/-- A faithful SL3 chief action at half ratio is itself a natural module.
The unique-constituent argument and A.1.42 are discharged here. -/
theorem linearThree_chief_natural {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hi : IsIrreducible ρ)
    {K : GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (h36 : Chapter1.Section02.A36Input K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    (C : Subgroup G) [IsQuasisimple C] (hC : IsSQTK K C)
    (hfit : generalizedFitting G = C) (hcore : pCore 2 G = ⊥)
    (hfaith : Function.Injective ρ)
    (F : BinaryField) (mark : C ≃* SL(3,F.Carrier))
    (A : Subgroup G) (hA : IsPGroup 2 A) (hgen : C ⊔ A = ⊤)
    (hq : quadraticRatio ρ ≤ 1 / 2) :
    IsIrreducible (ρ.comp C.subtype) ∧ ∃ E : BinaryField, IsLinearNatural (ρ.comp C.subtype) E 3 := by
  let : C.Normal := hfit ▸ generalizedFitting_normal (G := G)
  let : IsSimpleGroup (C ⧸ center C) := IsQuasisimple.simple
  let : Nontrivial C := (QuotientGroup.mk'_surjective (center C)).nontrivial
  have hirr := irreducible_component_of_homogeneous ρ hi hfaith C A
    ((Subgroup.nontrivial_iff_ne_bot C).mp inferInstance) hA hgen (by
      intro U W hiU hiW
      have he := linearThree_chief_homogeneous ρ hi hK h36 earlier C hC hfit hcore hfaith F mark hq
        U W hiU hiW
      subst W
      exact ⟨Representation.Equiv.refl _⟩)
  refine ⟨hirr, ?_⟩
  have hsq : IsSQTK K G := (IsSQTK.equiv
    ((MulEquiv.subgroupCongr hgen).trans (topEquiv : (⊤ : Subgroup G) ≃* G))).mp
      (IrreducibleBranch.local_sqtk hK C A hC hA)
  let : IsQuasisimple (generalizedFitting G) := hfit.symm ▸ inferInstance
  have hiF : IsIrreducible (ρ.comp (generalizedFitting G).subtype) := by rwa [hfit]
  obtain ⟨B, hB⟩ := isFFModule_of_quadraticRatio_le_one ρ (hq.trans (by norm_num))
  obtain ⟨B', _, hB'⟩ := hB.exists_bestOffender ρ
  have hc := earlier G V ρ hsq inferInstance hfaith hiF ⟨B', hB'⟩
  have hn := hc.natural_of_ratio_le_half ρ hq
  rw [hfit] at hn
  rcases hn with hn | ⟨d,hd,⟨e⟩⟩
  · exact hn
  · exact (no_linearThree_binary_equiv F hd (mark.symm.trans e.groupEquiv)).elim

/-- The pairwise source budget and the actual SL3 lower bound make every
noncentral chief ratio at most one half. -/
theorem linearThree_flag_ratio_bound {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V)
    {K : GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (hsemisimple : SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.SemisimpleInput K)
    (h36 : Chapter1.Section02.A36Input K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    [IsQuasisimple (generalizedFitting G)] (hsq : IsSQTK K (generalizedFitting G))
    (hfaith : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    (hp : IsPGroup 2 (G ⧸ generalizedFitting G))
    (F : BinaryField) (mark : generalizedFitting G ≃* SL(3,F.Carrier))
    (f : ReducibleChiefFlag ρ (generalizedFitting G))
    (A : Subgroup G) (hA : IsMinimalBestOffender ρ A) {i : ℕ} (hi : i ∈ f.noncentral) :
    quadraticRatio (imageRepresentation
      (sectionRepresentation ρ (f.chain i) (f.chain (i + 1)))) ≤ 1 / 2 := by
  have he := f.estimates ρ hfaith inferInstance hcore A hA
  let q := fun k => quadraticRatio (imageRepresentation
    (sectionRepresentation ρ (f.chain k) (f.chain (k + 1))))
  have hqt (k : ℕ) (hk : k ∈ f.noncentral) : q k ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) (he.2.2.1 k hk).2.le
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp f.multiple
  obtain ⟨j, hj, hij⟩ : ∃ j ∈ f.noncentral, i ≠ j := by
    by_cases hia : i = a
    · exact ⟨b, hb, hia ▸ hab⟩
    · exact ⟨a, ha, hia⟩
  have hlo := linearThree_flag_ratio_lower ρ hK hsemisimple h36 earlier hsq hcore hp F mark f hj
  have hl := ENNReal.toReal_mono (hqt j hj) hlo
  have hpair := ENNReal.toReal_mono (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) (he.2.2.2.1 i hi j hj hij)
  change (q i + q j).toReal ≤ (1 : ℝ≥0∞).toReal at hpair
  rw [ENNReal.toReal_add (hqt i hi) (hqt j hj)] at hpair
  apply (ENNReal.toReal_le_toReal (hqt i hi) (by norm_num)).mp
  norm_num [ENNReal.toReal_div] at hl hpair ⊢
  linarith

/-- All noncentral members of the original SL3 chief flag are faithful,
single irreducible natural component modules. -/
theorem linearThree_flag_natural {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V)
    {K : GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (hsemisimple : SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.SemisimpleInput K)
    (h36 : Chapter1.Section02.A36Input K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    [IsQuasisimple (generalizedFitting G)] (hsq : IsSQTK K (generalizedFitting G))
    (hfaith : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    (hp : IsPGroup 2 (G ⧸ generalizedFitting G))
    (F : BinaryField) (mark : generalizedFitting G ≃* SL(3,F.Carrier))
    (f : ReducibleChiefFlag ρ (generalizedFitting G))
    (A : Subgroup G) (hA : IsMinimalBestOffender ρ A)
    (hgen : generalizedFitting G ⊔ A = ⊤) :
    ∀ i ∈ f.noncentral,
      let τ := sectionRepresentation ρ (f.chain i) (f.chain (i + 1))
      Function.Injective τ ∧ IsIrreducible (τ.comp (generalizedFitting G).subtype) ∧
        ∃ E : BinaryField, IsLinearNatural (τ.comp (generalizedFitting G).subtype) E 3 := by
  intro i hi
  have hhalf := linearThree_flag_ratio_bound ρ hK hsemisimple h36 earlier hsq hfaith hcore hp
    F mark f A hA hi
  have hf := (half_flag_factor_reconstruction ρ hK hsemisimple h36 earlier hsq hcore hp f hi hhalf).1
  let τ := sectionRepresentation ρ (f.chain i) (f.chain (i + 1))
  have hactual : quadraticRatio τ ≤ 1 / 2 := (image_ratio_of_faithful τ hf) ▸ hhalf
  exact ⟨hf, linearThree_chief_natural τ (f.irreducible ρ ((f.mem_noncentral i).mp hi).1)
    hK h36 earlier (generalizedFitting G) hsq rfl hcore hf F mark A
    (hA.1.1.2.isPGroup 2 A) hgen hactual⟩

/-- All three source families now yield single natural chief factors on
the original actor, with no homogeneity or module-shape premise. -/
theorem natural_flag_single_chiefs {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V)
    {K : GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (hsemisimple : SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.SemisimpleInput K)
    (h36 : Chapter1.Section02.A36Input K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    [IsQuasisimple (generalizedFitting G)] (hsq : IsSQTK K (generalizedFitting G))
    (hfaith : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    (hp : IsPGroup 2 (G ⧸ generalizedFitting G))
    (mark : NaturalActor (generalizedFitting G))
    (f : ReducibleChiefFlag ρ (generalizedFitting G))
    (A : Subgroup G) (hA : IsMinimalBestOffender ρ A)
    (hgen : generalizedFitting G ⊔ A = ⊤) :
    ∀ i ∈ f.noncentral,
      let τ := sectionRepresentation ρ (f.chain i) (f.chain (i + 1))
      Function.Injective τ ∧ IsIrreducible (τ.comp (generalizedFitting G).subtype) ∧
        SmallNaturalConstituent τ (generalizedFitting G) := by
  rcases mark with ⟨F,⟨e⟩⟩ | ⟨d,hd,⟨e⟩⟩
  · intro i hi
    obtain ⟨hf,hirr,hn⟩ := linearThree_flag_natural ρ hK hsemisimple h36 earlier hsq
      hfaith hcore hp F e f A hA hgen i hi
    exact ⟨hf,hirr,Or.inl hn⟩
  · intro i hi
    have hn := binary_flag_natural ρ hK earlier hsq hfaith hcore hd e f A hA hgen i hi
    exact ⟨binary_flag_factor_faithful ρ hd e f hi, hn.1, Or.inr ⟨d,hd,hn.2⟩⟩

/-- The original reducible B.5.1 source hypotheses supply an actual LA-chief
flag whose every noncentral factor is faithful and a single irreducible natural
L-module. Full earlier B.4.2, A.2.1 and A.3.6 are the only earlier inputs. -/
theorem reducible_single_natural_chiefs {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V)
    {K : GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (hsemisimple : SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.SemisimpleInput K)
    (h36 : Chapter1.Section02.A36Input K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    {L : Subgroup G} (h : QuasisimpleSourceHypothesis ρ K L)
    (hnot : ¬ IsIrrPlus ρ L (moved ρ L)) :
    NaturalActor L ∧ ∃ A : Subgroup G, IsMinimalBestOffender ρ A ∧
      ∃ f : ReducibleChiefFlag (ρ.comp (L ⊔ A).subtype) (generalizedFitting ↥(L ⊔ A)),
        ∀ i ∈ f.noncentral,
          let τ := sectionRepresentation (ρ.comp (L ⊔ A).subtype) (f.chain i) (f.chain (i + 1))
          Function.Injective τ ∧ IsIrreducible (τ.comp (generalizedFitting ↥(L ⊔ A)).subtype) ∧
            SmallNaturalConstituent τ (generalizedFitting ↥(L ⊔ A)) := by
  let := h.finite_module
  let : IsQuasisimple L := h.quasisimple
  let : L.Normal := component_normal_of_fitting_eq_sup_center L h.fitting
  obtain ⟨hn, A, hA, f, _⟩ := reducible_naturalActor ρ hK hsemisimple h36 earlier h hnot
  refine ⟨hn, A, hA, f, ?_⟩
  let H := L ⊔ A
  let σ := ρ.comp H.subtype
  have hp : IsPGroup 2 A := hA.1.1.2.isPGroup 2 A
  have hfit : generalizedFitting H = L.subgroupOf H :=
    IrreducibleBranch.local_generalizedFitting L A h.fitting h.twoCore hp
  let : IsQuasisimple (L.subgroupOf H) :=
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe (show L ≤ H from le_sup_left)).symm
  let : IsQuasisimple (generalizedFitting H) := hfit.symm ▸ inferInstance
  have hsq : IsSQTK K (generalizedFitting H) := by
    rw [hfit]
    exact (IsSQTK.equiv (subgroupOfEquivOfLe (show L ≤ H from le_sup_left))).mpr h.sqtk
  have hq : IsPGroup 2 (H ⧸ generalizedFitting H) :=
    (IrreducibleBranch.local_quotient_isTwoGroup L A hp).of_equiv
      (QuotientGroup.quotientMulEquivOfEq hfit.symm)
  have hcore : pCore 2 H = ⊥ :=
    IrreducibleBranch.local_twoCore_eq_bot L H h.fitting h.twoCore le_sup_left
  have hmark : NaturalActor (generalizedFitting H) := NaturalActor.of_equiv
    ((MulEquiv.subgroupCongr hfit).trans
      (subgroupOfEquivOfLe (show L ≤ H from le_sup_left))) hn
  have hAH : A ≤ H := le_sup_right
  have hmin : IsMinimalBestOffender σ (A.subgroupOf H) := by
    refine ⟨hA.1.subgroupOf ρ hAH, ?_⟩
    intro B hB hBA
    apply Subgroup.map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le hAH]
    apply hA.2 _ (hB.map_subtype ρ)
    refine ⟨(map_mono hBA.1).trans_eq (map_subgroupOf_eq_of_le hAH), ?_⟩
    have hw := hBA.2
    rw [weight_comp_map ρ H.subtype H.subtype_injective,
      weight_comp_map ρ H.subtype H.subtype_injective,
      map_subgroupOf_eq_of_le hAH] at hw
    exact hw
  have hgen : generalizedFitting H ⊔ A.subgroupOf H = ⊤ := by
    rw [hfit]
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show L ≤ H from le_sup_left),
      map_subgroupOf_eq_of_le hAH]
    exact H.range_subtype.symm.trans H.subtype.range_eq_map
  exact natural_flag_single_chiefs σ hK hsemisimple h36 earlier hsq
    (h.faithful.comp H.subtype_injective) hcore hq hmark f (A.subgroupOf H) hmin hgen

end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
