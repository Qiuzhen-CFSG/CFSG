module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LinearMembership
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LocalSeparation

/-!
# Excluding higher fields in the original linear-three FF rows

Both actual rank-one residuals belong to L(G₁,S), are nonshort, and have
SL₂(q) core quotients and generalized Fitting subgroup O₂. The proved
original nonblock theorem places both in M_Z. They generate K, contradicting
the escaping hypothesis. Thus every natural or doubled-natural SL₃ row
in the literal B.5 source action has field degree one.

The final local-family consumer constructs the actual B.5 classifier and
discharges both row exclusions. Original-marker and exchanged-source
applications retain both original primes and both exchanged plane sizes.
The proof does not need general Borel equality or ambient C-componenthood.

The remaining finite block/parabolic catalogue and general Borel placement
stay with this catalogue owner. Original 15.1.14 remains explicit for its
existing producer and pre-exclusion assembly owner.
Source: Aschbacher--Smith 15.1.20(2), printed p.1095; B.5.1, pp.99--103.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
open ChapterB.QuasisimpleSource Matrix.PSL3.LinearThree
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- Positive repeated natural coordinates on the actual moved space or section
force the binary field, by residual membership, nonblock placement and generation. -/
theorem localFamily_linear_row_field_eq_one
    (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (a : d.NormalizerAction K) :
    letI := a.reduced.elementary
    ∀ (J : Subgroup ((K ⊔ d.normalizerSylow K : Subgroup G) ⧸
        centralizer (d.normalizerModule K : Set (K ⊔ d.normalizerSylow K : Subgroup G))))
      (_hLJ : d.normalizerImage K ≤ J)
      (s : MovedSection (a.representation.comp J.subtype) ((d.normalizerImage K).subgroupOf J))
      (F : BinaryField) (r : ℕ), 0 < r →
      (Nonempty (ActionEquiv (s.action.comp ((d.normalizerImage K).subgroupOf J).subtype)
          (repeated (linearNatural F 3) r)) ∨
       Nonempty (ActionEquiv (s.space.toRepresentation.comp ((d.normalizerImage K).subgroupOf J).subtype)
          (repeated (linearNatural F 3) r))) → F.degree = 1 := by
  let := a.reduced.elementary
  intro J hLJ s F r hr hm
  by_contra hn
  have hlarge : 1 < F.degree := by have := F.degree_pos; omega
  let : Group.IsPerfect K := Chapter1.mem_L_isPerfect hK.2
  have hfour : 4 ≤ Nat.card F.Carrier := by
    rw [F.card_eq]
    exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hlarge
  obtain ⟨e,hfam⟩ := d.localFamily_linear_residual_members hG h hK hq a J hLJ s F r hr hlarge hm
  have hd := a.linear_three_residual_data hG h hK.1 hq hfour e
  have hns := a.linear_three_residuals_not_short e hfour
  have hplace (P : Subgroup SL(3,F.Carrier))
      (hP : P ∈ ({pointParabolicSL F.Carrier,lineParabolicSL F.Carrier} : Set (Subgroup SL(3,F.Carrier)))) :
      d.normalizerParabolicResidual K (P.map e.symm.toMonoidHom) ≤ d.MZ := by
    let R := d.normalizerParabolicResidual K (P.map e.symm.toMonoidHom)
    have hr := hfam P hP
    let : Group.IsPerfect R := Chapter1.mem_L_isPerfect hr.2
    obtain ⟨hf,⟨er⟩⟩ := hd P hP
    let : IsSimpleGroup SL(2,F.Carrier) :=
      Theory.SpecificGroups.SymplecticFour.NaturalExtension.model_simple (by omega)
    let : IsSimpleGroup (R ⧸ pCore 2 R) := er.isSimpleGroup
    have hz : center (R ⧸ pCore 2 R) = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (R ⧸ pCore 2 R)) inferInstance with hz | hz
      · exact hz
      · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp hz)).elim
    let hqr : IsQuasisimple (R ⧸ pCore 2 R) :=
      { simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup }
    have hnot : ¬ ChapterC.IsShort R := by
      rcases hP with rfl | hP
      · exact hns.1
      · have he : P = lineParabolicSL F.Carrier := hP
        subst P
        exact hns.2
    exact d.localFamily_nonblock_le_MZ hG hempty hM hJ hu h hr hqr hf
      (fun hc => hnot hc.short) F.Carrier er
  apply hout
  rw [←a.linear_three_residuals_generate hq e F.card_eq hlarge]
  exact sup_le (hplace _ (Or.inl rfl)) (hplace _ (Or.inr rfl))
/-- The actual B.5 classifier, with both of its linear-three rows restricted
by the original nonblock argument to the binary field. -/
@[expose] def NormalizerAction.LinearSourceRowsBinary
    {d : CaseIComponentData T M Mc V} {K : Subgroup G} (a : d.NormalizerAction K) : Prop :=
  letI := a.reduced.elementary
  let J := offenderSubgroup a.representation
  ∃ (_hLJ : d.normalizerImage K ≤ J)
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      (a.representation.comp J.subtype) ((d.normalizerImage K).subgroupOf J)),
    (∀ F : BinaryField,
      ActionEquiv (c.sectionData.action.comp ((d.normalizerImage K).subgroupOf J).subtype)
        (linearNatural F 3) → F.degree = 1) ∧
    (∀ F : BinaryField,
      ActionEquiv (c.sectionData.space.toRepresentation.comp ((d.normalizerImage K).subgroupOf J).subtype)
        (repeated (linearNatural F 3) 2) → F.degree = 1)

/-- Source classification and both linear exclusions for every original
local-family member. All parabolic-membership and placement premises are
discharged, without an ambient C-component assumption. -/
theorem localFamily_linear_source_rows_binary (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hf : generalizedFitting K = pCore 2 K) :
    ∃ a : d.NormalizerAction K, a.LinearSourceRowsBinary := by
  let := h.elementary
  have a := d.localFamily_normalizerAction hG hempty hM hJ hu h hK hq hout hf
  let := a.reduced.elementary
  have hsq := caseI_centralizer_sqtk hG d.Z1 d.Z1_ne_bot
    ((IsElementaryAbelian.isPGroup 2 V).to_le (d.Z1_le_fixed.trans inf_le_left))
  have hsqK := (IsSQTK.equiv (subgroupOfEquivOfLe hK.1)).mp (hsq.subgroup (K.subgroupOf d.G1))
  obtain ⟨hLJ,⟨c⟩⟩ := a.source_classification hsqK
  refine ⟨a,hLJ,c,?_,?_⟩
  · intro F e
    apply d.localFamily_linear_row_field_eq_one hG hempty hM hJ hu h hK hq hout a
      _ hLJ c.sectionData F 1 (by decide)
    apply Or.inl
    refine ⟨⟨e.groupEquiv,e.linearEquiv.trans
      (LinearEquiv.funUnique (Fin 1) (ZMod 2) (Fin 3 → F.Carrier)).symm,?_⟩⟩
    intro g v
    funext i
    exact e.intertwines g v
  · intro F e
    exact d.localFamily_linear_row_field_eq_one hG hempty hM hJ hu h hK hq hout a
      _ hLJ c.sectionData F 2 (by decide) (Or.inr ⟨e⟩)

/-- Both original pre-exclusion primes use the same actual source classifier
and the same binary restriction of its two linear-three rows. -/
theorem PreExclusionSource.constrained_linear_source_rows_binary
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L) :
    ∃ a : d.NormalizerAction d.L, a.LinearSourceRowsBinary :=
  d.localFamily_linear_source_rows_binary hG hempty hM hJ hu h
    ⟨d.L_component.1,s.local_component⟩ s.quasisimple d.L_not_le_MZ hf

/-- The later exchanged selection preserves both plane sizes and the original
normalizer quotient in the same source-row exclusion. -/
theorem ExchangedSource.constrained_linear_source_rows_binary
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hf : generalizedFitting d.L = pCore 2 d.L) :
    ∃ a : d.NormalizerAction d.L, a.LinearSourceRowsBinary :=
  d.localFamily_linear_source_rows_binary hG hempty hM hJ hu h
    ⟨d.L_component.1,s.local_component⟩ s.quasisimple d.L_not_le_MZ hf

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Actual original-marker consumer of the source linear-three exclusion,
retaining its Z₁, row and prime. Original 15.1.14 remains explicit for its
existing producer and pre-exclusion assembly owner. -/
theorem PreparedChosenModule.source_preExclusion_constrained_linear_source_rows_binary
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      (generalizedFitting d.L = pCore 2 d.L →
        ∃ a : d.NormalizerAction d.L, a.LinearSourceRowsBinary) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hf =>
    s.constrained_linear_source_rows_binary (h := h) hG hempty hM hJ hu hf⟩
end CFSG.Quasithin.Chapter15.Section01
