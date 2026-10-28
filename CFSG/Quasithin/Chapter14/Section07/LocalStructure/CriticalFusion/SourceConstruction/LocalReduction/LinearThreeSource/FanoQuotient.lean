module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LinearThreeSource.PointQuotient
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LinearThreeSource.FanoParabolic
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.Guarded.SmallGeometry
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.Coordinates
public import Theory.Representation.PSL3Two.FixedParabolicQuotient
public import Theory.Representation.BinaryConjugationSection.ConjugateSpan
public import Theory.Representation.BinaryConjugationSection.FullMovement

/-!
# The Fano quotient of the original point section

The actual plane stabilizer in the original point normalizer is a maximal
Sylow overgroup. When the full point quotient is SL₃(2), it has index seven
and fixes the original line V₂/V₁. That line generates U/V₁, producing an
actual Fano-line permutation quotient with the same Sylow and parabolic
marking. The original seed commutator makes the quotient fully moved, so
its action is dual natural or the six-dimensional Fano core.

The final producer obtains the full point quotient under contrary plane
centrality from the original local SL₃(2) component. No natural-module
conclusion is inferred from the faithful-component catalogue.
Source: Aschbacher–Smith H.5.3, 12.8.8(6), and 14.7.48–49,
printed pp.385–386, 851–852, and 1064, refs/quasithin.pdf.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LinearThreeSource
open Chapter12.Section08 CriticalFusion.Source WholeResidualAssembly
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam
universe u v
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]

/-- Actual Fano intertwiners and full-module alternatives, with the original
plane stabilizer and Sylow marked under one quotient isomorphism. -/
def FanoPointSection (F : InvariantFlag T V 3)
    (ρ : Representation (ZMod 2) F.H W) : Prop :=
  (Module.finrank (ZMod 2) W = 3 ∨ Module.finrank (ZMod 2) W = 6) ∧
  ρ.ker = pCore 2 F.H ∧
  ∃ e : (F.H ⧸ pCore 2 F.H) ≃* BinaryLinearThree.Group,
    let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 F.H))
    ((F.Gi 2).subgroupOf F.H).map f = Matrix.PSL3Two.lineParabolicSL ∧
    ((T : Subgroup G).subgroupOf F.H).map f = Matrix.PSL3Two.borelSL ∧
    (∃ q : Representation.IntertwiningMap
      (BinaryLinearThree.FanoLineQuotients.lineRepresentation.comp f) ρ,
      Function.Surjective q) ∧
    (∃ r : ρ.IntertwiningMap (BinaryLinearThree.W.dual.comp f), Function.Surjective r) ∧
    (Nonempty (Representation.Equiv (BinaryLinearThree.W.dual.comp f) ρ) ∨
      Nonempty (Representation.Equiv
        (BinaryLinearThree.FanoDecomposition.lineCoreRepresentation.comp f) ρ))

/-- The full point quotient forces the Fano action on every literal U/V₁
coordinate section; no movement or natural-module premise is supplied. -/
theorem fano_point_section_of_full_point_quotient
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (e₀ : (F.H ⧸ pCore 2 F.H) ≃* Matrix.PSL3Two.PSL)
    {ρ : Representation (ZMod 2) F.H W}
    (c : BinaryConjugationSection F.H F.U (F.Vi 1) ρ) : FanoPointSection F ρ := by
  let := h.chosen.elementary
  let := F.localKernel_tilde_seed_elementary
  let : Finite W := Finite.of_surjective (fun v : F.U => (c.coordinates v).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  have hH := F.H_mem_Hz (by decide) L _ (h.flag_escape_at F previous)
  obtain ⟨H₂,Y,h₂H,hT₂,hR,_,_,_,_,_,_,_,_,h₂eq,_⟩ :=
    InnerLinearExclusion.Guarded.small_local_middle_intersections
      h hab structural previous faithful F.H hH (Or.inl ⟨e₀⟩)
  let S := T.subtype (F.sylow_le_of_mem_Hz hH)
  let P := H₂.subgroupOf F.H
  have hSP : (S : Subgroup F.H) ≤ P := fun _ ht => hT₂ ht
  have hindex : P.index = 7 := maximal_sylow_overgroup_index_seven
    e₀ S P hSP hR.right_maximal
  have hplane : Module.finrank (ZMod 2) (c.imageSpace (F.Vi 2)) = 1 := by
    apply c.imageSpace_finrank_of_index (F.Vi 2)
      ((F.le_seed 2).trans (le_conjugateSpanBy V F.H)) 1
    have hc := relIndex_mul_card_of_le (F.monotone (by decide : 1 ≤ 2))
    rw [F.card 1 (by decide),F.card 2 (by decide)] at hc
    norm_num at hc ⊢
    omega
  obtain ⟨w,hw0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (by omega :
    0 < Module.finrank (ZMod 2) (c.imageSpace (F.Vi 2)))
  have hw0' : (w : W) ≠ 0 := fun hz => hw0 (Subtype.ext hz)
  have hline : c.imageSpace (F.Vi 2) = Submodule.span (ZMod 2) {(w : W)} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hplane w.property hw0'
  have hw (a : P) : ρ a w = w := by
    obtain ⟨x,hx,hcoord⟩ := (c.mem_imageSpace_iff (F.Vi 2) w).mp w.property
    rw [←hcoord]
    apply flag_plane_fixed ρ c ((F.le_seed 2).trans (le_conjugateSpanBy V F.H))
      (F.monotone (by decide : 1 ≤ 2)) (by simpa using F.card 1 (by decide))
      (by simpa using F.card 2 (by decide)) a.val ?_ x hx
    have ha : (a.val : G) ∈ H₂ := a.property
    rw [h₂eq] at ha
    exact ha.2
  have hspan : F.U = conjugateSpanBy (F.Vi 2) F.H :=
    F.U_eq_plane_span L (by decide) h.chosen.normalizes
      (F.invariant_subgroup_of_ambient_natural h.naturalMarking (by decide))
  have hs : Submodule.span (ZMod 2) (Set.range (fun a : F.H => ρ a (w : W))) = ⊤ := by
    apply top_unique
    rw [←c.imageSpace_self,congrArg c.imageSpace hspan,
      c.imageSpace_conjugateSpan (F.Vi 2) ((F.le_seed 2).trans (le_conjugateSpanBy V F.H))]
    apply iSup_le
    intro a x hx
    obtain ⟨y,hy,rfl⟩ := hx
    rw [hline] at hy
    obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp hy
    rw [←hr,map_smul]
    exact Submodule.smul_mem _ r (Submodule.subset_span ⟨a,rfl⟩)
  have hseed : Module.finrank (ZMod 2) (c.imageSpace V) = 2 := by
    apply c.imageSpace_finrank_of_index V (le_conjugateSpanBy V F.H) 2
    have hc := relIndex_mul_card_of_le (F.le_seed 1)
    have hV : Nat.card V = 8 := by
      simpa only [F.last,Nat.reducePow] using F.card 3 (by decide)
    rw [F.card 1 (by decide),hV] at hc
    norm_num at hc ⊢
    omega
  have hd : 1 < Module.finrank (ZMod 2) W := by
    have hh := Submodule.finrank_le (c.imageSpace V)
    rw [hseed] at hh
    omega
  have hmove : F.U = ⁅F.H,F.U⁆ ⊔ F.Vi 1 := by
    have he : F.U = ⁅F.U,F.H⁆ := conjugateSpanBy_eq_commutator_of_seed
      V F.H F.H (F.Li L 1) le_rfl F.H.le_normalizer
      ((F.Li_le L 1).trans inf_le_right) (seed_commutator h F)
    rw [commutator_comm,←he,sup_eq_left.mpr c.kernel_le]
  have hm : Representation.BinaryOffender.subspaceCommutator ρ ⊤ ⊤ = ⊤ := by
    simpa only [subgroupOf_self] using
      c.subspaceCommutator_eq_top_of_movement F.H le_rfl hmove
  obtain ⟨_,hker,e,hP,hS,⟨q,hq,hrange,hmodels⟩,r,hr⟩ :=
    BinaryLinearThree.FixedParabolicQuotient.quotient_and_head
      e₀ S P hSP hindex ρ (w : W) hw hs hd
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 F.H))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hdim := BinaryLinearThree.FanoLineMoved.moved_dimension f hf ρ q hq hd
  rw [hm,finrank_top] at hdim
  let R := (BinaryLinearThree.FanoLineMoved.coreMap f ρ q).range
  have hRtop : R.toSubmodule = ⊤ := hrange.trans hm
  let i : R.toRepresentation.IntertwiningMap ρ := {
    toLinearMap := R.toSubmodule.subtype
    isIntertwining' _ := rfl }
  have hi : Function.Bijective i := ⟨Subtype.val_injective,fun x =>
    ⟨⟨x,hRtop ▸ Submodule.mem_top⟩,rfl⟩⟩
  have hmodels' : Nonempty (Representation.Equiv (BinaryLinearThree.W.dual.comp f) ρ) ∨
      Nonempty (Representation.Equiv
        (BinaryLinearThree.FanoDecomposition.lineCoreRepresentation.comp f) ρ) := by
    rcases hmodels with ha | ha
    · obtain ⟨a⟩ := ha
      exact Or.inl ⟨a.trans (i.ofBijective hi)⟩
    · obtain ⟨a⟩ := ha
      exact Or.inr ⟨a.trans (i.ofBijective hi)⟩
  have hPeq : P = (F.Gi 2).subgroupOf F.H := by
    ext x
    change (x : G) ∈ H₂ ↔ (x : G) ∈ F.Gi 2
    rw [h₂eq]
    exact and_iff_right x.property
  exact ⟨hdim,hker,e,hPeq ▸ hP,hS,⟨q,hq⟩,⟨r,hr⟩,hmodels'⟩

/-- Under contrary plane centrality, the original local linear-three row
produces the actual quotient action and its Fano classification. -/
theorem fano_point_action_of_linear_three_and_plane_centralized_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (source47 : Earlier14747 F L)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (e : (C ⧸ pCore 2 C) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hc : ⁅F.Vi 2,F.H.pCoreIn 2⁆ = ⊥) :
    ∃ hU : IsElementaryAbelian 2 (F.UH F.H), let := hU
      ∃ a : LocalQuotientAction F.H (F.UH F.H) (F.Vi 1),
        quadraticRatio a.representation ≤ 2 ∧
        FanoPointSection F (a.representation.comp (QuotientGroup.mk' (pCore 2 F.H))) := by
  obtain ⟨e₀⟩ := full_point_quotient_of_linear_three_and_plane_centralized_at
    d h hab structural previous faithful earlier source47 I hI C hC e hc
  have hH := F.H_mem_Hz (by decide) L _ (h.flag_escape_at F previous)
  obtain ⟨hU,a,ha⟩ := local_quadratic_bound_at h structural hab F.H hH
  let := hU
  exact ⟨hU,a,ha,fano_point_section_of_full_point_quotient
    h hab structural previous faithful e₀ (AlternatingSevenSource.localQuotientSection a)⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LinearThreeSource
