module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.FlagBounds

/-!
# Homogeneous natural prefixes and exclusion of source case (C)

The next actual chief section has ratio at least one quarter. Codimension
additivity bounds the preceding term's action ratio by three quarters, using
the same original minimal best offender. The complete B.4.9 calculation gives
strictly larger ratio for a natural-plus-dual term, so that strict-induction
alternative is impossible. No splitting is needed for this budget comparison.

Consequently every nonzero proper term of the original binary source flag is
exactly i copies of one natural module, under one actual group marking. The
proved dimension and length identities give i≤n-2. This discharges the source
maximal-submodule alternatives up to the final attachment of the last natural
factor; full binary moved-module semisimplicity is already proved separately.

Source: Aschbacher--Smith, B.5.1, printed p.102, exclusion of (C), and B.4.9(2)
for the natural-plus-dual ratio values.
-/

public section
open Representation Representation.BinaryOffender Theory.GroupTheory Subgroup
open scoped MatrixGroups BigOperators ENNReal
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
universe u v
variable {G : Type u} [Group G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

private theorem ratio_le_actionEquiv {H X : Type*} [Group H]
    [AddCommGroup X] [Module (ZMod 2) X] {σ : Representation (ZMod 2) H X}
    (e : ActionEquiv ρ σ) : quadraticRatio σ ≤ quadraticRatio ρ := by
  apply le_iInf
  intro A
  apply le_iInf
  rintro ⟨hA,hq⟩
  have hAm : IsElementaryTwo (A.map e.groupEquiv.toMonoidHom) := by
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let : IsElementaryAbelian 2 A := hA.2
    refine ⟨?_,IsElementaryAbelian.map _⟩
    intro hh
    apply hA.1
    apply Subgroup.map_injective (f := e.groupEquiv.toMonoidHom) e.groupEquiv.injective
    simpa only [Subgroup.map_bot] using hh
  have hqm : IsQuadratic σ (A.map e.groupEquiv.toMonoidHom) := by
    rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ w
    obtain ⟨v,rfl⟩ := e.linearEquiv.surjective w
    have hh := congrArg e.linearEquiv (hq a ha b hb v)
    change σ (e.groupEquiv a) (σ (e.groupEquiv b) (e.linearEquiv v) - e.linearEquiv v) =
      σ (e.groupEquiv b) (e.linearEquiv v) - e.linearEquiv v
    simpa only [e.intertwines,map_sub] using hh
  have hr : actionRatio σ (A.map e.groupEquiv.toMonoidHom) = actionRatio ρ A := by
    unfold actionRatio
    rw [← fixedCodim_map_equivariant ρ σ _ e.linearEquiv e.intertwines,
      rank_map_injective _ e.groupEquiv.injective]
  exact iInf_le_of_le (A.map e.groupEquiv.toMonoidHom) (iInf_le_of_le ⟨hAm,hqm⟩ hr.le)

/-- The complete B.4.9 mixed-pair calculation applies to any actually marked
natural-plus-dual action, retaining its original actor and FF witness. -/
theorem naturalDual_ratio_gt_three_quarters [Finite G] [FiniteDimensional (ZMod 2) V]
    {d : ℕ} (hd : d = 4 ∨ d = 5) (hn : IsNaturalPlusDual ρ d) (hff : IsFFModule ρ) :
    (3 / 4 : ℝ≥0∞) < quadraticRatio ρ := by
  obtain ⟨a⟩ := hn
  have hm : IsFFModule (naturalPlusDual d) :=
    hff.map_equivariant ρ _ a.groupEquiv.toMonoidHom a.groupEquiv.injective a.linearEquiv a.intertwines
  let ν := linearNatural BinaryField.two d
  have hf : Function.Injective ν := by
    change Function.Injective (specialLinearNatural (k := ZMod 2) d)
    exact specialLinearNatural_injective d
  have hmodel := NaturalPair.three_quarters_lt_dual_ratio ν ν.dual hd hf
    ⟨MulEquiv.refl _,LinearEquiv.refl _ _,fun _ _ => rfl⟩ (Representation.Equiv.refl _) hm
  exact hmodel.trans_le (ratio_le_actionEquiv ρ a)

/-- Codimension additivity on a literal section bounds a prefix together
with its next factor, even before a splitting is chosen. -/
theorem prefix_section_ratio_le [FiniteDimensional (ZMod 2) V]
    (U W : Subrepresentation ρ) (hUW : U ≤ W) (A : Subgroup G) :
    actionRatio (sectionRepresentation ρ U W) A + actionRatio U.toRepresentation A ≤
      actionRatio ρ A := by
  have hb := fixedCodim_quotient_add_subrepresentation_le W.toRepresentation (sectionLower ρ U W) A
  have he : fixedCodim (sectionLower ρ U W).toRepresentation A = fixedCodim U.toRepresentation A := by
    simpa only [Subgroup.map_id] using fixedCodim_map_equivariant
      (sectionLower ρ U W).toRepresentation U.toRepresentation (MonoidHom.id G)
      (sectionLowerEquiv ρ hUW) (fun _ _ => rfl) A
  rw [he] at hb
  have hc := hb.trans (fixedCodim_subrepresentation_le ρ W A)
  simp only [actionRatio,← ENNReal.add_div,← Nat.cast_add]
  apply ENNReal.div_le_div_right
  exact_mod_cast hc

private theorem prefix_budget {x : ℝ≥0∞} (h : 1 / 4 + x ≤ 1) : x ≤ 3 / 4 := by
  have hx : x ≤ 1 := (le_add_left le_rfl).trans h
  have hxf : x ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) hx
  apply (ENNReal.toReal_le_toReal hxf (ENNReal.div_ne_top (by norm_num) (by norm_num))).mp
  have hr := ENNReal.toReal_mono (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) h
  rw [ENNReal.toReal_add (by norm_num) hxf] at hr
  norm_num [ENNReal.toReal_div] at hr ⊢
  linarith

/-- A proper source prefix spends at most three quarters of the original
minimal offender's rank, since its next natural factor spends at least one quarter. -/
theorem binary_source_prefix_ratio [Finite G] [FiniteDimensional (ZMod 2) V]
    {K : CFSG.Quasithin.GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    [IsQuasisimple (generalizedFitting G)] (hsq : IsSQTK K (generalizedFitting G))
    (hf : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    {d : ℕ} (hd : d = 4 ∨ d = 5) (mark : generalizedFitting G ≃* SL(d,ZMod 2))
    (f : ReducibleChiefFlag ρ (generalizedFitting G))
    (A : Subgroup G) (hA : IsMinimalBestOffender ρ A)
    (hindices : f.noncentral = Finset.range f.length) {i : ℕ} (hi : i < f.length) :
    actionRatio (f.chain i).toRepresentation A ≤ 3 / 4 := by
  have hi' : i ∈ f.noncentral := hindices ▸ Finset.mem_range.mpr hi
  have hb := f.estimates ρ hf inferInstance hcore A hA
  have hlo := binary_flag_ratio_lower ρ hK earlier hsq hcore hd mark f hi' ((hb.2.2.1 i hi').2.le)
  have hfi := binary_flag_factor_faithful ρ hd mark f hi'
  rw [image_ratio_of_faithful _ hfi] at hlo
  have hquarter : (1 / 4 : ℝ≥0∞) ≤ 1 / (d-1 : ℕ) := by
    rcases hd with rfl | rfl <;> norm_num
  have hs : (1 / 4 : ℝ≥0∞) ≤ actionRatio (sectionRepresentation ρ (f.chain i) (f.chain (i+1))) A :=
    (hquarter.trans hlo).trans (iInf_le_of_le A
      (iInf_le_of_le ⟨hA.1.1,quadratic_section ρ _ _ (hA.isQuadratic ρ)⟩ le_rfl))
  apply prefix_budget
  exact (add_le_add hs le_rfl).trans
    ((prefix_section_ratio_le ρ (f.chain i) (f.chain (i+1)) (f.monotone (by omega)) A).trans
      ((actionRatio_le_one_iff ρ hA.1.1).mpr (hA.1.isOffender ρ).2))


/-- The actual proper terms in the binary source flag are sums of precisely
i isomorphic natural modules, with i≤n-2. The natural-plus-dual strict-IH
alternative is excluded by the original next-factor ratio budget. -/
theorem binary_source_flag_repeated [Finite G] [FiniteDimensional (ZMod 2) V]
    {K : CFSG.Quasithin.GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    (ih : SmallerDimensionInput.{u,v} K (Module.finrank (ZMod 2) V))
    [IsQuasisimple (generalizedFitting G)] (hsq : IsSQTK K (generalizedFitting G))
    (hwhole : generalizedFitting G = ⊤)
    (hf : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    {d : ℕ} (hd : d = 4 ∨ d = 5) (mark : generalizedFitting G ≃* SL(d,ZMod 2))
    (f : ReducibleChiefFlag ρ (generalizedFitting G))
    (A : Subgroup G) (hA : IsMinimalBestOffender ρ A)
    (hm : Coinvariants.ker (ρ.comp (generalizedFitting G).subtype) = ⊤)
    {i : ℕ} (hi0 : 0 < i) (hi : i < f.length) :
    IsRepeatedLinearNatural (f.chain i).toRepresentation BinaryField.two d i ∧ i ≤ d-2 := by
  have hgen : generalizedFitting G ⊔ A = ⊤ := by rw [hwhole,top_sup_eq]
  obtain ⟨hindices,_⟩ := binary_source_flag_pure ρ hK earlier hsq hf hcore hd mark f A hA hgen hm
  have hlength := binary_source_flag_length ρ hK earlier hsq hf hcore hd mark f A hA hindices
  refine ⟨?_,by omega⟩
  rcases binary_source_flag_coordinates ρ hK earlier ih hsq hwhole hf hcore hd mark f A hA hm hi0 hi
    with ⟨r,_,hn⟩ | hn
  · have hnall (j : ℕ) (hj : j < f.length) : IsLinearNatural
        ((sectionRepresentation ρ (f.chain j) (f.chain (j+1))).comp (generalizedFitting G).subtype)
        BinaryField.two d :=
      (binary_flag_natural ρ hK earlier hsq hf hcore hd mark f A hA hgen j
        (hindices ▸ Finset.mem_range.mpr hj)).2
    have heq := binary_repeated_flag_multiplicity ρ (generalizedFitting G) f (by omega : 0 < d)
      hnall hi.le hn
    exact heq ▸ hn
  · have hr := binary_source_prefix_ratio ρ hK earlier hsq hf hcore hd mark f A hA hindices hi
    have hb := bestOffender_on_subrepresentation ρ (f.chain i) hA.1
    have hgt := naturalDual_ratio_gt_three_quarters (f.chain i).toRepresentation hd hn
      ⟨A,hb.isOffender _⟩
    have hle : quadraticRatio (f.chain i).toRepresentation ≤
        actionRatio (f.chain i).toRepresentation A :=
      iInf_le_of_le A (iInf_le_of_le
        ⟨hA.1.1,quadratic_subrepresentation ρ (f.chain i) (hA.isQuadratic ρ)⟩ le_rfl)
    exact (not_lt_of_ge (hle.trans hr) hgt).elim

end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
