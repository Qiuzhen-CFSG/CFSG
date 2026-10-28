module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSectionModelBinaryThree
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSectionScalarPlane
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.IrreducibleCohomology.CohomologyReduction

/-!
# Whole-module natural coordinates from the actual half-cost B.5 source

The actual quadratic actor and its moved plane survive on the literal
central quotient. Half ratio restricts the marked catalogue to natural
linear actions. A larger defining field would make the binary moved plane
a field line and cannot support a strong actor. The binary-three central
cover is excluded by its involution costs; the higher binary linear rows
split by the proved cohomology calculation. Fully moved geometry then lifts
all surviving markings to the entire original module and same component.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.DecomposableQuinticControl
open ChapterB.QuasisimpleSource
variable {G W : Type*} [Group G] [Finite G] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

/-- The original fully moved half-cost source is natural binary linear in
dimension three, four or five, with the same original component action. -/
theorem whole_natural_of_half_cost
    (σ : Representation (ZMod 2) G W) {A L : Subgroup G}
    (hA : IsElementaryTwo A) (hq : IsQuadratic σ A)
    (hcost : (rank A = 2 ∧ fixedCodim σ A = 1) ∨
      (rank A = 4 ∧ fixedCodim σ A = 2))
    (hd : Module.finrank (ZMod 2) (moved σ A) ≤ 2)
    (hm : moved σ L = ⊤) (s : MovedSection σ L)
    (hc : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleActionCase σ L s) :
    ∃ n, (n = 3 ∨ n = 4 ∨ n = 5) ∧
      Nonempty (ActionEquiv (σ.comp L.subtype) (linearNatural BinaryField.two n)) := by
  have hstrong : IsStrongOffender σ A := ⟨hA, by rcases hcost with h | h <;> omega⟩
  have hsTop : s.space.toSubmodule = ⊤ := s.space_eq.trans hm
  rcases strong_source_marked_of_plane σ hstrong hd s hc with
    ⟨hi, hf, hirr, hsA, hrows⟩ | ⟨n, hn, ⟨e⟩⟩
  · have hr := moved_section_ratio_le_half_of_exact_cost σ hA hq hcost s
    rcases linear_rows_of_half_ratio s.action hrows hr with
      ⟨F, hF, hgen, ⟨e⟩, hratio⟩ | ⟨n, hn, hgen, ⟨e⟩, hratio⟩
    · have hqs : IsQuadratic s.action A :=
        quadratic_of_equivariant_surjection s.space.toRepresentation s.action
          s.central.toSubmodule.mkQ s.central.toSubmodule.mkQ_surjective
          (fun _ _ => rfl) A (quadratic_subrepresentation σ s.space hq)
      have hbound : 2 * fixedCodim s.action A ≤ rank A := by
        have h₁ := fixedCodim_quotient_add_subrepresentation_le s.space.toRepresentation s.central A
        have h₂ := fixedCodim_subrepresentation_le σ s.space A
        change fixedCodim s.action A + _ ≤ _ at h₁
        rcases hcost with h | h <;> omega
      have hbest := SourceCompletion.bestOffender_of_half_bound s.action hratio.ge hA hqs
        (SourceCompletion.actionRatio_le_half_of_twice s.action hA hbound)
      have hAL : A ≤ L := hgen ▸ hbest.le_offenderSubgroup s.action
      have hdim := (moved_finrank_quotient_le s.space.toRepresentation s.central A).trans
        ((moved_finrank_subrepresentation_le σ s.space A).trans hd)
      have hF1 : F.degree = 1 := by
        by_contra hn
        have hlarge : 1 < F.degree := by have hp := F.degree_pos; omega
        let B := (A.subgroupOf L).map e.groupEquiv.toMonoidHom
        have hBoff := ((show IsOffender s.action A from ⟨hA, hsA.2.le⟩).subgroupOf
          s.action hAL).map_equivariant (s.action.comp L.subtype) (linearNatural F 3)
            e.groupEquiv.toMonoidHom e.groupEquiv.injective e.linearEquiv e.intertwines
        have hrB : rank B = rank A := by
          rw [rank_map_injective _ e.groupEquiv.injective, rank_subgroupOf hAL]
        have hcB : fixedCodim (linearNatural F 3) B = fixedCodim s.action A := by
          rw [←fixedCodim_map_equivariant (s.action.comp L.subtype) (linearNatural F 3)
            e.groupEquiv.toMonoidHom e.linearEquiv e.intertwines, fixedCodim_subgroupOf s.action hAL]
        have hdB : Module.finrank (ZMod 2) (moved (linearNatural F 3) B) ≤ 2 := by
          have he := moved_finrank_equivariant (s.action.comp L.subtype) (linearNatural F 3)
            e.groupEquiv.toMonoidHom e.linearEquiv e.intertwines (A.subgroupOf L)
          rw [subspaceCommutator_comp_map, map_subgroupOf_eq_of_le hAL] at he
          exact he.symm.le.trans hdim
        apply not_strong_of_nonbinary_scalar_plane F (specialLinearNatural 3)
          (specialLinearNatural_injective 3) hlarge B hdB
        refine ⟨hBoff.1, ?_⟩
        change fixedCodim (linearNatural F 3) B < rank B
        rw [hcB, hrB]
        exact hsA.2
      let q := ExtensionConsequences.degreeOneNaturalEquiv F hF1 3
      let e₂ : ActionEquiv (s.action.comp L.subtype) (linearNatural BinaryField.two 3) :=
        ⟨e.groupEquiv.trans q.groupEquiv, e.linearEquiv.trans q.linearEquiv,
          fun g v => (congrArg q.linearEquiv (e.intertwines g v)).trans
            (q.intertwines (e.groupEquiv g) (e.linearEquiv v))⟩
      exact ⟨3, Or.inl rfl,
        (binary_three_whole_action_of_half_cost σ hA hq hcost s hi hm e₂ hgen hratio).2⟩
    · have hcompl := ExtensionConsequences.binaryLinear_isCompl s hi
        (by rcases hn with rfl | rfl <;> decide) e
      have hz : fixedSpace σ L = ⊥ := by
        have he := hcompl.inf_eq_bot
        rwa [hsTop, top_inf_eq] at he
      let f := s.fullComponentActionEquiv hm hz
      exact ⟨n, Or.inr hn, ⟨⟨e.groupEquiv, f.linearEquiv.trans e.linearEquiv, fun g v =>
        (congrArg e.linearEquiv (f.intertwines g v)).trans (e.intertwines g (f.linearEquiv v))⟩⟩⟩
  · let i := (LinearEquiv.ofTop s.space.toSubmodule hsTop).symm
    refine ⟨n, Or.inr hn, ⟨⟨e.groupEquiv, i.trans e.linearEquiv, ?_⟩⟩⟩
    intro g v
    have he : i (σ g v) = s.space.toRepresentation g (i v) := by
      apply Subtype.ext
      rfl
    exact (congrArg e.linearEquiv he).trans (e.intertwines g (i v))

end CFSG.Quasithin.Chapter15.DecomposableQuinticControl
