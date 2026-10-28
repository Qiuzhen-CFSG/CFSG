module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightReciprocalOffender
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.NoncentralKernel
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2SourceRecognition
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.OffenderModels.Assembly
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.CriticalLine

/-!
# A noncentral maximal kernel forces the actual rank-one offender

The original reciprocal critical path supplies the quadratic actor, its
rank comparison and its common displacement line. On the literal U/V₁
section, the complete offender alternatives recognize both sections in a
single S₈ marking. The critical-line contradiction excludes each strong
branch. The surviving conclusion retains the actual transposition actor,
its rank one, whole fixed codimension two and the natural-or-cover model
of the kernel's component commutator. No chief-factor series or strongness
assumption is supplied by the caller.

Source: Aschbacher–Smith 14.7.51, printed p.1065, and the offender analysis
of 13.8.25, printed pp.960–962, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource
open Chapter12.Section08 CriticalFusion.Source WholeResidualAssembly
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction
open Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
open OffenderModels Orthogonal.SourceTransport
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The literal critical line, its denominator commutator, and both positions
relative to the chosen kernel. This is produced by the offender analysis. -/
structure CriticalTransvectionGeometry
    [IsElementaryAbelian 2 (F.UH F.H)]
    (a : LocalQuotientAction F.H (F.UH F.H) (F.Vi 1))
    (N : Subrepresentation a.representation) (c : CriticalPath (L := L) F) : Prop where
  line_le : c.Zα ≤ F.U
  line_atom : IsAtom ((AlternatingSevenSource.localQuotientSection a).imageSpace c.Zα)
  commutator_eq : ⁅commutatorPreimage F.U c.Uα c.Zα, c.Uα⁆ = c.Zα
  positions :
    let b := AlternatingSevenSource.localQuotientSection a
    let s := G2Source.starSection b
    (c.Zα ≤ preimage s N.toSubmodule ∧
      N.toSubmodule ≤ b.imageSpace (commutatorPreimage F.U c.Uα c.Zα) ∧
      subspaceCommutator a.representation N.toSubmodule (star F c.Uα) = b.imageSpace c.Zα) ∨
    (¬ c.Zα ≤ preimage s N.toSubmodule ∧
      N.toSubmodule ⊔ b.imageSpace (commutatorPreimage F.U c.Uα c.Zα) = ⊤ ∧
      subspaceCommutator N.quotientRepresentation ⊤ (star F c.Uα) =
        (b.imageSpace c.Zα).map N.toSubmodule.mkQ)

/-- For the original full point normalizer, noncentrality of the chosen
maximal kernel leaves only the marked transvection alternative. The selected
critical path and both compatible module models are conclusions. -/
theorem noncentral_maximal_kernel_transvection_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (source47 : Earlier14747 F L)
    (hH : F.H ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup F.H) (hC : C.IsCComponent)
    [IsElementaryAbelian 2 (F.UH F.H)]
    (a : LocalQuotientAction F.H (F.UH F.H) (F.Vi 1))
    (N : Subrepresentation a.representation) (hN : IsCoatom N)
    (eH : HStar F.H ≃* Equiv.Perm (Fin 8))
    (hK : (C.map (starMap F)).map eH.toMonoidHom = alternatingGroup (Fin 8))
    (hQ : IsEightNatural N.quotientRepresentation eH)
    (hKW : ∃ k ∈ C.map (starMap F), ∃ w : N.toSubmodule,
      N.toRepresentation k w ≠ w) :
    ∃ c : CriticalPath (L := L) F, c.RankSelection ∧ c.Uα ≤ F.Ri L 1 ∧
      CriticalTransvectionGeometry a N c ∧ ∃ g : Equiv.Perm (Fin 8),
        Nonempty (TransvectionModels a.representation N (C.map (starMap F))
          (star F c.Uα) (conjugateMarking eH g)) := by
  let : IsElementaryAbelian 2 (Chapter13.Section08.Source.UH F.H V) :=
    inferInstanceAs (IsElementaryAbelian 2 (F.UH F.H))
  let : IsElementaryAbelian 2 (Chapter13.Section08.Source.Utilde F.H V (F.Vi 1)) := {
    exponent_dvd_p := MonoidHom.exponent_dvd
      (f := QuotientGroup.mk' ((F.Vi 1).subgroupOf (Chapter13.Section08.Source.UH F.H V)))
      (QuotientGroup.mk'_surjective _) |>.trans
        (IsElementaryAbelian.exponent_dvd_p 2 (Chapter13.Section08.Source.UH F.H V)) }
  let b := AlternatingSevenSource.localQuotientSection a
  let s := G2Source.starSection b
  obtain ⟨c, hsel, hplace, _, _, hquad, _, hbound, _, _⟩ :=
    exists_eight_selected_critical_action_at h hab structural previous faithful eH b
  have hAH : c.Uα ≤ F.H := (critical_le_Q_at h structural c).trans (Q_le_H F)
  have hA := G2Source.critical_elementary h hab c hplace hsel
  have hquad' : IsQuadratic a.representation (star F c.Uα) := by
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ v
    exact hquad x hx y hy v
  have hbound' : fixedCodim a.representation (star F c.Uα) ≤
      2 * rank (star F c.Uα) := by
    change Module.finrank (ZMod 2) (_ ⧸ fixedSpace (a.representation.comp (starMap F))
      (c.Uα.subgroupOf F.H)) ≤ _ at hbound
    rw [fixedSpace_comp_map] at hbound
    exact hbound
  have hstar : Chapter13.Section08.Source.starImage F.H (C.map F.H.subtype) =
      C.map (starMap F) := by
    change ((C.map F.H.subtype).comap F.H.subtype).map (starMap F) = _
    rw [comap_map_eq_self_of_injective F.H.subtype_injective]
  have hK' : (Chapter13.Section08.Source.starImage F.H (C.map F.H.subtype)).map
      eH.toMonoidHom = alternatingGroup (Fin 8) := by rwa [hstar]
  have hKW' : ∃ k ∈ Chapter13.Section08.Source.starImage F.H (C.map F.H.subtype),
      ∃ w : N.toSubmodule, N.toRepresentation k w ≠ w := by rwa [hstar]
  have hn : F.U ≤ normalizer (c.Zα : Set G) :=
    (G2Source.reciprocal_placement h c).trans
      ((s.centralizes_conjugate_line c.conjugator⁻¹).trans (Subgroup.centralizer_le_normalizer _))
  have hcard : Nat.card c.Zα = 2 := by
    rw [CriticalPath.Zα, conjugate,
      card_map_of_injective (MulAut.conj c.conjugator⁻¹).injective]
    simpa using F.card 1 (by decide)
  obtain ⟨hd, hl, hdisp⟩ := G2Source.critical_linear_bounds b h c hplace hsel
  have hindex : Nat.log 2 ((Chapter13.Section08.Source.DH F.U c.Uα c.Zα).relIndex F.U) ≤
      rank (star F c.Uα) := by
    rw [← s.quotient_finrank _ (s.line_le_DH _ _ hAH)]
    exact hd
  have halt := source_offender_model_alternatives F.H V (F.Vi 1) (C.map F.H.subtype)
    c.Uα c.Zα a.representation s N hN eH hK' hQ hKW' (map_subtype_le C)
    (local_component_full_movement_at h structural source47 F.H hH C hC)
    hA hquad' hbound' hAH hn hcard hindex
    (OriginalSource.symmetric_b4 _ eH hK')
    (fun eK => OriginalSource.component_b4 _ eH eK hK')
  refine ⟨c, hsel, hplace, ?_⟩
  rcases halt with hstrongQ | ⟨_, hrest⟩
  · obtain ⟨_, g, ⟨m⟩, _⟩ := hstrongQ
    exact (orthogonal_sections_critical_line_contradiction a.representation N m.J
      (conjugateMarking eH g) m.model (Or.inl m.quotient_natural)
      (star F c.Uα) m.actor_marking
      (b.imageSpace (commutatorPreimage F.U c.Uα c.Zα)) (b.imageSpace c.Zα)
      hd hl hdisp).elim
  · rcases hrest with hstrongW | hrank
    · obtain ⟨_, _, g, ⟨m⟩, _⟩ := hstrongW
      exact (orthogonal_sections_critical_line_contradiction a.representation N m.J
        (conjugateMarking eH g) m.model (Or.inl m.quotient_natural)
        (star F c.Uα) m.actor_marking
        (b.imageSpace (commutatorPreimage F.U c.Uα c.Zα)) (b.imageSpace c.Zα)
        hd hl hdisp).elim
    · obtain ⟨_, hZU, hatom, hcomm, hposition, g, ⟨m⟩⟩ := hrank
      refine ⟨⟨hZU, hatom, hcomm, hposition⟩, g, ?_⟩
      rw [hstar] at m
      exact ⟨m⟩

/-- The original linear-four full point row produces the remaining
rank-one configuration. The actual action, maximal kernel, noncentrality,
permutation marking and critical geometry are all constructed internally. -/
theorem full_point_four_transvection_configuration_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (source47 : Earlier14747 F L)
    (C : Subgroup F.H) (hC : C.IsCComponent)
    (e : (C ⧸ pCore 2 C) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) :
    ∃ hU : IsElementaryAbelian 2 (F.UH F.H),
      let := hU
      ∃ (a : LocalQuotientAction F.H (F.UH F.H) (F.Vi 1))
        (N : Subrepresentation a.representation) (eH : HStar F.H ≃* Equiv.Perm (Fin 8))
        (c : CriticalPath (L := L) F),
        IsCoatom N ∧ Function.Injective N.toRepresentation ∧
        Function.Injective N.quotientRepresentation ∧ c.RankSelection ∧
        c.Uα ≤ F.Ri L 1 ∧ CriticalTransvectionGeometry a N c ∧
        Nonempty (TransvectionModels a.representation N (C.map (starMap F))
          (star F c.Uα) eH) := by
  have hH := F.H_mem_Hz (by decide) L _ (h.flag_escape_at F previous)
  obtain ⟨hU, hr⟩ := local_four_exists_natural_quotient_at d h hab structural previous
    faithful earlier source47 F.H hH C hC e
  let := hU
  obtain ⟨a, N, b, _, hN, hirr, hfQ, hq, hK, hQ⟩ := hr
  have hKW := local_four_quotient_kernel_moved_at d h hab structural previous faithful
    earlier source47 F.H hH C hC e a N hN.ne_top hirr hq
  have hfN := StrongSections.SourceConstituents.faithful_of_noncentral
    N.toRepresentation b (C.map (starMap F)) hK (by
      intro hfix
      obtain ⟨k,hk,w,hw⟩ := hKW
      exact hw (hfix k hk w))
  obtain ⟨c,hsel,hplace,hgeom,g,⟨m⟩⟩ := noncentral_maximal_kernel_transvection_at
    h hab structural previous faithful source47 hH C hC a N hN b hK hQ hKW
  exact ⟨hU,a,N,conjugateMarking b g,c,hN,hfN,hfQ,hsel,hplace,hgeom,⟨m⟩⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource
