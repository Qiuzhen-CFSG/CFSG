module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.NonnormalBinarySourceAt.FactorExclusion
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition.Recognition
public import Theory.Representation.NormalPairSupport
public import Theory.Representation.BinaryOffender.CentralSectionAction

/-!
# The original exchanged orthogonal module

The split-factor exclusion forces both component fixed spaces to vanish
on every irreducible proper quotient. Normality of the marked simple
square makes the sum of those fixed spaces invariant. Intrinsic exchanged
field-four recognition then identifies the quotient, including its group
and linear coordinates and their intertwining action.

The original quadratic actor supplies the cubic bound on the actual chief
quotient. On the whole literal U/V₁ section, the same actor and the proved
no-strong-offender theorem force the chief kernel to be centralized by the
component orbit: otherwise the quotient would be an FF-module, contrary
to its orthogonal identification. The commuting-cubic central-cover theorem
removes that kernel. The final application retains the original actor in
R₁ and its bound on this whole module.

Source: Aschbacher–Smith, proof of 14.7.32, printed p.1057,
refs/quasithin.pdf; the intrinsic exchanged recognition and central-cover
arguments from 13.8.16(1) apply with the actual Chapter 14 markings. The
critical-actor geometry and subsequent weak-closure contradiction remain
separate source steps.
-/

/-! This same-G,T source replay uses only Structural1222At and Theorem12213At
at the original Sylow; it does not infer universal earlier records. -/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.Components Swapped Swapped.LinearTwo ModuleAlternatives
open F918Sections.NoStrong

private theorem fixedSpace_of_range {D S U : Type*} [Group D] [Group S]
    [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) D U) (f : S →* D) (A : Subgroup D)
    (hf : f.range = A) : invariants (ρ.comp f) = fixedSpace ρ A := by
  ext v
  constructor
  · intro hv a
    obtain ⟨s,hs⟩ := (show (a : D) ∈ f.range from hf ▸ a.property)
    change ρ (a : D) v = v
    rw [←hs]
    exact hv s
  · intro hv s
    exact hv ⟨f s,hf ▸ (show f s ∈ f.range from ⟨s,rfl⟩)⟩

private theorem exchanged_component_fixed_eq_bot
    {D k U : Type*} [Group D] [Finite D] [Field k] [Finite k] [CharP k 2]
    (a : ExchangedActor KnownSimple.IsKnownSimple D k 2)
    [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) D U) [ρ.IsIrreducible]
    (hno : ¬ (subspaceCommutator ρ ⊤ a.component ≤ fixedSpace ρ a.second ∧
      subspaceCommutator ρ ⊤ a.second ≤ fixedSpace ρ a.component)) :
    fixedSpace ρ a.component = ⊥ ∧ fixedSpace ρ a.second = ⊥ := by
  let e := a.productEquiv
  let i := a.orbit.subtype.comp e.symm.toMonoidHom
  have hi : Function.Injective i := a.orbit.subtype_injective.comp e.symm.injective
  have hfirst : (i.comp (MonoidHom.inl PSL(2,k) PSL(2,k))).range = a.component := by
    ext x
    constructor
    · rintro ⟨s,rfl⟩
      have hh : (s,1) ∈ (a.component.subgroupOf a.orbit).map e.toMonoidHom := by
        rw [a.first_mark]
        exact ⟨trivial,rfl⟩
      exact (mem_map_equiv).mp hh
    · intro hx
      let xN : a.orbit := ⟨x,a.component_le hx⟩
      have hm : e xN ∈ (⊤ : Subgroup PSL(2,k)).prod ⊥ :=
        a.first_mark ▸ mem_map_of_mem e.toMonoidHom hx
      refine ⟨(e xN).1,?_⟩
      change (e.symm ((e xN).1,1) : D) = x
      rw [←show e xN = ((e xN).1,1) from Prod.ext rfl hm.2,e.symm_apply_apply]
  have hsecond : (i.comp (MonoidHom.inr PSL(2,k) PSL(2,k))).range = a.second := by
    ext x
    constructor
    · rintro ⟨s,rfl⟩
      have hh : (1,s) ∈ (a.second.subgroupOf a.orbit).map e.toMonoidHom := by
        rw [a.second_mark]
        exact ⟨rfl,trivial⟩
      exact (mem_map_equiv).mp hh
    · intro hx
      let xN : a.orbit := ⟨x,a.second_le hx⟩
      have hm : e xN ∈ (⊥ : Subgroup PSL(2,k)).prod ⊤ :=
        a.second_mark ▸ mem_map_of_mem e.toMonoidHom hx
      refine ⟨(e xN).2,?_⟩
      change (e.symm (1,(e xN).2) : D) = x
      rw [←show e xN = (1,(e xN).2) from Prod.ext hm.1 rfl,e.symm_apply_apply]
  let : IsQuasisimple a.component := a.component_isComponent.2
  have hinl : Function.Injective (i.comp (MonoidHom.inl PSL(2,k) PSL(2,k))) :=
    hi.comp (fun x y he => congrArg Prod.fst he)
  let f := (MonoidHom.ofInjective hinl).trans (MulEquiv.subgroupCongr hfirst)
  let : IsQuasisimple PSL(2,k) := IsQuasisimple.of_mulEquiv f.symm
  have hr : i.range = a.orbit := by
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr e.symm.surjective,
      ←MonoidHom.range_eq_map,range_subtype]
  let : i.range.Normal := hr.symm ▸ a.orbit_normal
  have hl : NormalPairSupport.left ρ i = fixedSpace ρ a.second :=
    fixedSpace_of_range ρ _ _ hsecond
  have hr' : NormalPairSupport.right ρ i = fixedSpace ρ a.component :=
    fixedSpace_of_range ρ _ _ hfirst
  by_contra hbad
  have hsep : NormalPairSupport.left ρ i ≠ ⊥ ∨ NormalPairSupport.right ρ i ≠ ⊥ := by
    by_contra! hh
    exact hbad ⟨hr' ▸ hh.2,hl ▸ hh.1⟩
  have hsum := NormalPairSupport.support_sup_eq_top ρ i hi
    (Atlas.RankOneFieldAutomorphisms.psl_center_eq_bot (F := k)) hsep
  rw [hl,hr'] at hsum
  have hc : a.component ≤ centralizer (a.second : Set D) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (a.component_isComponent.commutator_eq_bot_of_ne a.second_isComponent a.distinct.symm)
  apply hno
  constructor
  · exact subspaceCommutator_le_of_le_sup_fixedSpace ρ
      (fixedSpace_stable_of_normalizes ρ (hc.trans (Subgroup.centralizer_le_normalizer _))) hsum.ge
  · exact subspaceCommutator_le_of_le_sup_fixedSpace ρ
      (fixedSpace_stable_of_normalizes ρ ((le_centralizer_iff.mp hc).trans
        (Subgroup.centralizer_le_normalizer _))) (by simpa only [sup_comm] using hsum.ge)

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The original irreducible quotient is the actual orthogonal module once
its source quadratic actor supplies the cubic-ratio bound. No factor or
natural-module recognition is assumed. -/
theorem local_nonnormal_component_quotient_orthogonal_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent)
    (hnormal : ¬ (K.subgroupOf I).Normal)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) (HStar F.H) W)
    (c : BinaryConjugationSection F.H F.U (F.Vi 1) (σ.comp (starMap F)))
    (Q : Subrepresentation σ) (hQ : Q ≠ ⊤) [Q.quotientRepresentation.IsIrreducible]
    (hratio : cubicRatio Q.quotientRepresentation ≤ 2) :
    HasOrthogonalFourOrbit Q.quotientRepresentation
      (Chapter13.Section08.Source.starImage F.H (conjugateSpanBy K (T : Subgroup G))) := by
  let : Finite W := Finite.of_surjective (fun v : F.U => (c.coordinates v).toAdd)
    (fun w => c.onto (Multiplicative.ofAdd w))
  let : FiniteDimensional (ZMod 2) W := Module.Finite.of_finite
  obtain ⟨t,ht,htn,k,hk,hfin,hchar,a,ha,hb,horbit,hS⟩ :=
    local_nonnormal_component_exchanged_actor_at d h hab structural previous faithful earlier
      I K hI hKI hK hnormal
  have hno : ¬ (subspaceCommutator Q.quotientRepresentation ⊤ a.component ≤
        fixedSpace Q.quotientRepresentation a.second ∧
      subspaceCommutator Q.quotientRepresentation ⊤ a.second ≤
        fixedSpace Q.quotientRepresentation a.component) := by
    rw [ha,hb]
    intro hh
    exact local_nonnormal_component_no_cross_quotient_at d h hab structural previous faithful earlier
      I K hI hKI hK hnormal σ c ht htn ⟨Q,hQ,hh⟩
  obtain ⟨hfirst,hsecond⟩ := exchanged_component_fixed_eq_bot a Q.quotientRepresentation hno
  rw [←horbit]
  exact SourceRecognition.exchanged_cubic_orthogonal a Q.quotientRepresentation
    (local_nonnormal_component_quotient_faithful_at d h hab structural previous faithful earlier
      I K hI hKI hK hnormal σ c Q hQ) hfirst hsecond hratio


open Chapter15.Section03.AbelianAmalgam

/-- The original exchanged component supplies an orthogonal chief quotient of
its literal full-point section. The exact seed kernel and original quadratic
actor are retained, and the cubic bound is discharged by that actor. -/
theorem local_nonnormal_component_orthogonal_chief_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent)
    (hnormal : ¬ (K.subgroupOf I).Normal) :
    ∃ hU : IsElementaryAbelian 2 F.U,
      letI := hU
      ∃ a : LocalQuotientAction F.H F.U (F.Vi 1),
      ∃ A : Subrepresentation a.representation,
        IsCoatom A ∧ A.quotientRepresentation.IsIrreducible ∧
        Function.Injective A.quotientRepresentation ∧
        HasOrthogonalFourOrbit A.quotientRepresentation
          (Chapter13.Section08.Source.starImage F.H (conjugateSpanBy K (T : Subgroup G))) ∧
        subspaceCommutator A.quotientRepresentation ⊤
          (Chapter13.Section08.Source.starImage F.H (conjugateSpanBy K (T : Subgroup G))) = ⊤ ∧
        (∀ v : F.U, (v : G) ∈ V →
          (A.toSubmodule.mkQ (Additive.ofMul
              (QuotientGroup.mk' ((F.Vi 1).subgroupOf F.U) v)) = 0 ↔
            (v : G) ∈ F.Vi 1)) ∧
        cubicRatio A.quotientRepresentation ≤ 2 ∧
        ∃ B : Subgroup F.H, B ≤ (F.Ri L 1).subgroupOf F.H ∧
          IsElementaryTwo (B.map (starMap F)) ∧
          IsQuadratic A.quotientRepresentation (B.map (starMap F)) ∧
          fixedCodim A.quotientRepresentation (B.map (starMap F)) ≤
            2 * rank (B.map (starMap F)) := by
  obtain ⟨hU,a,A,hA,hirr,hfaith,hfull,hseed,hratio,B,hBR,hB,hquad,hcod⟩ :=
    local_nonnormal_component_quadratic_chief_at d h hab structural previous faithful earlier
      I K hI hKI hK hnormal
  let := hU
  let := hirr
  have hpoint : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  let s := ModuleBound.OriginalF916.conjugationSection a
    (normalizer_le_centralizer_of_card_two _ hpoint)
  let c : BinaryConjugationSection F.H F.U (F.Vi 1)
      (a.representation.comp (starMap F)) := {
    section_le := s.le
    kernel_le := s.line_le
    normalized := s.normalizes
    coordinates := s.quotient
    onto := s.surjective
    kernel_eq := s.kernel
    equivariant := fun x v => (s.conjugates x v).symm }
  exact ⟨hU,a,A,hA,hirr,hfaith,
    local_nonnormal_component_quotient_orthogonal_at d h hab structural previous faithful earlier
      I K hI hKI hK hnormal a.representation c A hA.1 hratio,
    hfull,hseed,hratio,B,hBR,hB,hquad,hcod⟩


/-- The literal full-point module in the exchanged branch is orthogonal.
The original quadratic actor rules out a noncentral chief kernel via the
no-strong-offender theorem. The commuting-cubic cover theorem then removes
its central kernel. -/
theorem local_nonnormal_component_whole_orthogonal_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent)
    (hnormal : ¬ (K.subgroupOf I).Normal) :
    ∃ hU : IsElementaryAbelian 2 F.U,
      letI := hU
      ∃ a : LocalQuotientAction F.H F.U (F.Vi 1),
        HasOrthogonalFourOrbit a.representation
          (Chapter13.Section08.Source.starImage F.H (conjugateSpanBy K (T : Subgroup G))) ∧
        ∃ B : Subgroup F.H, B ≤ (F.Ri L 1).subgroupOf F.H ∧
          IsElementaryTwo (B.map (starMap F)) ∧
          IsQuadratic a.representation (B.map (starMap F)) ∧
          fixedCodim a.representation (B.map (starMap F)) ≤
            2 * rank (B.map (starMap F)) := by
  obtain ⟨t,ht,htn,k,hk,hfin,hchar,e,he1,he2,horbit,hS⟩ :=
    local_nonnormal_component_exchanged_actor_at d h hab structural previous faithful earlier
      I K hI hKI hK hnormal
  let := e.orbit_normal
  have hgen : e.orbit ⊔ ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf F.H).map
      (starMap F) = ⊤ := by
    apply top_unique
    rw [←e.generated]
    apply sup_le_sup_left
    rw [hS]
    exact map_mono (subgroupOf_mono F.H le_sup_right)
  have hH := F.H_mem_Hz (by decide) L _ (h.flag_escape_at F previous)
  obtain ⟨hU,a,_,B,hBR,hB,hquad,hcod,hfaithB⟩ :=
    WholeResidualAssembly.GuardedSource.local_prime_supplement_quadratic_actor h hab structural previous F.H hH e.orbit hgen
  change IsElementaryAbelian 2 F.U at hU
  let := hU
  change LocalQuotientAction F.H F.U (F.Vi 1) at a
  have hpoint : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  let s := ModuleBound.OriginalF916.conjugationSection a
    (normalizer_le_centralizer_of_card_two _ hpoint)
  let c : BinaryConjugationSection F.H F.U (F.Vi 1)
      (a.representation.comp (starMap F)) := {
    section_le := s.le
    kernel_le := s.line_le
    normalized := s.normalizes
    coordinates := s.quotient
    onto := s.surjective
    kernel_eq := s.kernel
    equivariant := fun x v => (s.conjugates x v).symm }
  let : Finite (Additive (F.U ⧸ (F.Vi 1).subgroupOf F.U)) :=
    Finite.of_surjective (fun v : F.U => (c.coordinates v).toAdd)
      (fun w => c.onto (Multiplicative.ofAdd w))
  let : FiniteDimensional (ZMod 2) (Additive (F.U ⧸ (F.Vi 1).subgroupOf F.U)) :=
    Module.Finite.of_finite
  obtain ⟨A,hA,hirr,hfaith,hfull,hseed⟩ :=
    local_nonnormal_component_chief_quotient_at d h hab structural previous faithful earlier
      I K hI hKI hK hnormal a.representation c
  let := hirr
  have hq : IsQuadratic A.quotientRepresentation (B.map (starMap F)) :=
    quadratic_of_equivariant_surjection a.representation A.quotientRepresentation
      A.toSubmodule.mkQ A.toSubmodule.mkQ_surjective
      (fun g v => (A.quotientRepresentation_mk g v).symm) _ hquad
  have hb : fixedCodim A.quotientRepresentation (B.map (starMap F)) ≤
      2 * rank (B.map (starMap F)) := by
    have hh := fixedCodim_quotient_add_subrepresentation_le a.representation A (B.map (starMap F))
    exact (Nat.le_add_right _ _).trans (hh.trans hcod)
  have hm : HasOrthogonalFourOrbit A.quotientRepresentation e.orbit := by
    rw [horbit]
    exact local_nonnormal_component_quotient_orthogonal_at d h hab structural previous faithful earlier
      I K hI hKI hK hnormal a.representation c A hA.1
      ((cubicRatio_le_nat_iff _ 2).mpr ⟨B.map (starMap F),hB,isCubic_of_isQuadratic hq,hb⟩)
  have hmoved : subspaceCommutator a.representation ⊤ e.orbit = ⊤ := by
    rw [horbit]
    exact local_nonnormal_component_star_moved_at d h hab structural previous faithful earlier
      I K hI hKI hK hnormal a.representation c
  have hcentral : A.toSubmodule ≤ fixedSpace a.representation e.orbit := by
    by_contra hnc
    obtain ⟨hnW,hnQ⟩ := e.section_exclusions_of_faithful_exclusion a.representation
      (fun _ _ _ _ ρ hf => SourceRecognition.exchanged_not_strong e ρ hf) hmoved
    have hff := F918Sections.two_ff_sections_of_noncentral a.representation e.component e.sylow
      (B.map (starMap F)) e.component_isComponent hB hcod
      (e.orbit_eq ▸ hfaithB) (e.orbit_eq ▸ hmoved) A hA.1 (e.orbit_eq ▸ hnc)
      (hnW A hA.1 hnc) (hnQ A hA.1)
    exact SourceRecognition.orthogonal_image_not_ff A.quotientRepresentation e.orbit hm hff.2
  have hwhole := (SourceRecognition.orthogonal_quotient_is_whole a.representation e.orbit A
    hcentral hmoved hm).2
  exact ⟨hU,a,horbit ▸ hwhole,B,hBR,hB,hquad,hcod⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
