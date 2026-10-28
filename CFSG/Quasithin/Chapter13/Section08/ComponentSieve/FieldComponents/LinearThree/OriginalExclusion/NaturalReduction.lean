module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.OriginalExclusion.NativeSource
public import Theory.Representation.PSL3Two.ResidualFFForms.ConstituentBudget.InvolutionBound
public import Theory.Representation.BinaryOffender.ConjugationGeneration
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.RankOne

/-!
# The remaining natural-three branch of the binary whole quotient

The original critical geometry supplies a transvection on U_H/V₁. Faithfulness
makes it an involution. Three conjugates generate SL₃(2); the original seed
commutator identity makes the whole quotient module their displacement span.
Consequently its dimension is at most three. The five marked H.6.5 alternatives
therefore leave only the natural three-space, with the same line parabolic.

Independently, the two-core quotient preserves three-rank. A binary whole
quotient has three-rank one, whereas the covered local point residual has
three-rank two. Thus the local quotient must be ordinary A₆. This excludes
the covered binary branch outright and leaves only the ordinary natural-three
contradiction. No universal 13.7.6 or transvection-classification premise is
used. The field owner retains that last contradiction; SourceContext retains
the genuine preceding source inputs, finally supplied by qt-d-1381-source.

Source: Aschbacher–Smith, 13.7.5(5), 13.7.6(1), and 13.8.19, printed
pp.938–940,953 (combined manuscript, 1 March 2004).
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.OriginalExclusion
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open Geometry Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

private theorem whole_moved
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : SourceAction H V₃ V₁)
    (e : Source.Hstar H ≃* BinaryLinearThree.Group) :
    subspaceCommutator (act.representation.comp e.symm.toMonoidHom) ⊤ ⊤ = ⊤ := by
  let σ := act.representation.comp e.symm.toMonoidHom
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hg : ⁅H,Source.UH H V₃⁆ = Source.UH H V₃ := by
    rw [commutator_comm]
    exact Section07.ModelExclusions.span_commutator_of_containing_normal_component
      (localNaturalSetup c.localSetup) le_rfl H.le_normalizer
      (le_sup_left.trans c.component.local_overgroup.1.2)
  have hm := commutator_eq_top_of_conjugation σ (Source.UH H V₃) H
    (le_normalizer_conjugateSpanBy V₃ H) f
    (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)))
    (QuotientGroup.mk'_surjective _) (fun h u => ?_) hg
  · rwa [MonoidHom.range_eq_top_of_surjective f hf] at hm
  · change act.representation (e.symm (e (QuotientGroup.mk' (pCore 2 H) h))) _ = _
    rw [e.symm_apply_apply]
    exact act.conjugation h u

/-- Three conjugate source involutions bound the actual quotient dimension. -/
theorem source_binary_dimension_le_three
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : SourceAction H V₃ V₁) (e₀ : Source.Hstar H ≃* Matrix.PSL3Two.PSL) :
    Module.finrank (ZMod 2) (Additive (Source.Utilde H V₃ V₁)) ≤ 3 := by
  let e := e₀.trans Matrix.PSL3Two.equiv.symm
  let σ := act.representation.comp e.symm.toMonoidHom
  obtain ⟨a, ha, hne, hr⟩ := source_binary_involution c act e₀
  have he (g : Source.Hstar H) (v : Additive (Source.Utilde H V₃ V₁)) :
      (LinearEquiv.refl (ZMod 2) _ : _ ≃ₗ[ZMod 2] _) (act.representation g v) =
        σ (e g) ((LinearEquiv.refl (ZMod 2) _ : _ ≃ₗ[ZMod 2] _) v) := by
    change act.representation g v = act.representation (e.symm (e g)) v
    rw [e.symm_apply_apply]
  have hc := fixedCodim_map_equivariant act.representation σ e.toMonoidHom
    (LinearEquiv.refl _ _) he (zpowers a)
  simp only [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom] at hc
  have hb := BinaryLinearThree.ResidualFFForms.ConstituentBudget.finrank_le_three_mul_involution_fixedCodim
    σ (whole_moved c act e) (e a) (by rw [←map_pow,ha,map_one])
    (fun hz => hne (e.injective (hz.trans (map_one e).symm)))
  rw [←hc,hr] at hb
  simpa using hb

/-- The natural three-space is the only remaining H.6.5 module, with the
original L₁T image marked by the same actor isomorphism. -/
theorem source_binary_marked_natural
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : SourceAction H V₃ V₁) (e₀ : Source.Hstar H ≃* Matrix.PSL3Two.PSL) :
    ∃ e : Source.Hstar H ≃* BinaryLinearThree.Group,
      Nonempty (Representation.Equiv (act.representation.comp e.symm.toMonoidHom) BinaryLinearThree.W) ∧
      (Source.starImage H (one L T V₁ ⊔ (T : Subgroup G))).map e.toMonoidHom =
        Matrix.PSL3Two.lineParabolicSL := by
  let : Nonempty BinaryLinearThree.Point := ⟨⟨![1,0,0], by decide⟩⟩
  obtain ⟨e,hclass,hP⟩ := source_binary_marking c act e₀
  have hd := source_binary_dimension_le_three c act e₀
  refine ⟨e,?_,hP⟩
  unfold H65Alternatives at hclass
  rcases hclass with h | h | h | h | h
  · exact h
  · obtain ⟨f⟩ := h
    rw [f.toLinearEquiv.finrank_eq, BinaryPermutation.finrank_core,
      Matrix.PSL3Two.Fano.card_point] at hd
    omega
  · obtain ⟨f⟩ := h
    rw [f.toLinearEquiv.finrank_eq, BinaryLinearThree.finrank_steinberg] at hd
    omega
  · obtain ⟨f⟩ := h
    rw [f.toLinearEquiv.finrank_eq, Module.finrank_prod,
      BinaryLinearThree.finrank_steinberg] at hd
    omega
  · obtain ⟨f⟩ := h
    rw [f.toLinearEquiv.finrank_eq, Module.finrank_prod,
      BinaryLinearThree.finrank_steinberg] at hd
    omega

omit [IsElementaryAbelian 2 (Source.UH H V₃)] in
/-- The actual binary whole quotient forces the ordinary local A₆ quotient. -/
theorem source_binary_local_ordinary
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (e : Source.Hstar H ≃* Matrix.PSL3Two.PSL) :
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) := by
  let d := localNaturalSetup c.localSetup
  have hL₁H : sourceOne L T V₁ ≤ H := le_sup_left.trans c.component.local_overgroup.1.2
  have hr : primeRank 3 H = 1 := by
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 H) pCore_isPGroup,
      primeRank_equiv 3 e]
    exact ExternalComponentAction.RankReduction.rank_psl3
  have hu := (primeRank_mono 3 (show H ⊓ normalizer (V₃ : Set G) ≤ H from inf_le_left)).trans_eq hr
  have hn : primeRank 3 (sourceOne L T V₁) ≠ 0 := by
    intro hz
    have hq : primeRank 3 (sourceOne L T V₁ ⧸ pCore 2 (sourceOne L T V₁)) = 0 := by
      rw [primeRank_quotient_eq_of_isTwoGroup 3 (by decide) _ pCore_isPGroup,hz]
    have hnd := PrimeRank.eq_zero_iff_not_dvd_card.mp hq
    rcases Section07.ModelExclusions.point_residual_quotient_card d with hc | hc <;>
      rw [hc] at hnd <;> exact hnd (by decide)
  have hl := primeRank_mono 3 (le_inf hL₁H (Section07.ModelExclusions.point_residual_normalizes_seed d))
  exact Section07.ModelExclusions.ordinary_of_rank_one d hL₁H (by omega)

/-- The binary whole quotient would make the actual U_H/V₁ a three-space
and U_H an elementary abelian group of order sixteen. -/
theorem source_binary_module_size
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : SourceAction H V₃ V₁) (e₀ : Source.Hstar H ≃* Matrix.PSL3Two.PSL) :
    Module.finrank (ZMod 2) (Additive (Source.Utilde H V₃ V₁)) = 3 ∧
      Nat.card (Source.UH H V₃) = 16 := by
  obtain ⟨_,⟨f⟩,_⟩ := source_binary_marked_natural c act e₀
  have hd : Module.finrank (ZMod 2) (Additive (Source.Utilde H V₃ V₁)) = 3 :=
    f.toLinearEquiv.finrank_eq.trans (by simp [BinaryLinearThree.Vector, Matrix.PSL3Two.Fano.Vector])
  have hc : Nat.card (Source.Utilde H V₃ V₁) = 8 := by
    change Nat.card (Additive (Source.Utilde H V₃ V₁)) = 8
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hd]
    decide
  have hm := (V₁.subgroupOf (Source.UH H V₃)).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe act.line_le).toEquiv,
    c.localSetup.line_card, index_eq_card, hc] at hm
  exact ⟨hd, hm.symm⟩

omit [IsElementaryAbelian 2 (Source.UH H V₃)] in
/-- The covered local A₆ case cannot have binary whole quotient: its
point residual has three-rank two, whereas H has three-rank one. -/
theorem source_binary_covered_exclusion
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (hcover : Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms)) :
    ¬ Nonempty (Source.Hstar H ≃* Matrix.PSL3Two.PSL) := by
  rintro ⟨e⟩
  obtain ⟨eL⟩ := source_binary_local_ordinary c e
  obtain ⟨eC⟩ := hcover
  have hc := Nat.card_congr (centerCongr (eC.symm.trans eL)).toEquiv
  rw [Representation.Hexacode.even_center_card,
    alternatingGroup.center_eq_bot (by simp),card_bot] at hc
  omega
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.OriginalExclusion
