module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.SmallResidualControl
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SmallActionUniqueness
public import Theory.GroupTheory.PrimeIndexCentralSeed
public import Theory.GroupTheory.FiveResidualBorel
public import Theory.GroupTheory.ReducedNormal.SylowCentralSeed
public import Theory.GroupTheory.PGroup.OmegaCenterIn

/-!
# The original marked-five full parabolic and its faithful chosen module

The source residual has two-core of index five, so YT has Sylow index
five. The central seed Z(T) intersect V generates V under Y and hence
under YT. Its normalizer lies in Mc; uniqueness for YT therefore forces
the seed to be noncentral in YT. Prime-index maximality identifies its
centralizer as T and the centralizer of V as O₂(YT).

The same original subgroup is two-reduced and its core quotient is
D₁₀ or the concrete Sz(2). The first factor YRc is kept distinct from
this full parabolic. These facts feed the Chapter 15 quintic graph setup;
marked recognition and the final quotient remain with qt-e-152-small-parabolic.

Source: Aschbacher--Smith, original 15.2.6--8, printed pp.1109--1110,
and F.7.6, printed p.312.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
variable {G : Type*} [Group G] [Finite G]

/-- The original first full parabolic has index five over T and its chosen
module has precisely the two-core as centralizer. -/
theorem ChosenSmallSource.marked_five_first_parabolic
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hd : letI := h.prepared.elementary
      ∃ l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
        (Jhat (imageRepresentation M V h.prepared.normalized)).subtype),
        DihedralMarking l 5 2) :
    let P := h.residual ⊔ (T : Subgroup G)
    (T : Subgroup G).relIndex P = 5 ∧
      generalizedFitting P = pCore 2 P ∧
      V ≤ P ∧
      V = conjugateSpanBy (centralInvolutions T ⊓ V) P ∧
      IsPReduced 2 (V.subgroupOf P) ∧
      centralizer (V.subgroupOf P : Set P) = pCore 2 P ∧
      (Nonempty ((P ⧸ pCore 2 P) ≃* DihedralGroup 5) ∨
        Nonempty ((P ⧸ pCore 2 P) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0)) := by
  let := h.prepared.elementary
  obtain ⟨l,hd⟩ := hd
  have hp : PrimeDimensionOptions 5 2 := (primeDimensionOptions_iff 5 2).mpr (Or.inr ⟨rfl,rfl⟩)
  let Y := h.residual
  let P := Y ⊔ (T : Subgroup G)
  let Z := centralInvolutions T ⊓ V
  have hw := (h.smallResidualWitness_of_marked_five ⟨l,hd⟩).1
  have hYM : Y ≤ M := source_caseIIResidual_le T h.maximal.1.2 (map_subtype_le _)
  have hPM : P ≤ M := sup_le hYM h.maximal.1.2
  have hTP : (T : Subgroup G) ≤ P := le_sup_right
  have hPN : P ≤ normalizer (V : Set G) := hPM.trans h.prepared.normalized
  have hVP : V ≤ P :=
    ((source_dihedral_five_residual_core_normalizer h.ambient T h.empty h.maximal
      h.centralizing h.partner h.many h.prepared l hp hd).1.trans (pCoreIn_le 2 Y)).trans le_sup_left
  have hspan : V = conjugateSpanBy Z P := by
    apply le_antisymm ?_ (conjugateSpanBy_le inf_le_right hPN)
    exact (source_dihedral_five_residual_seed_span h.ambient T h.empty h.maximal
      h.centralizing h.partner h.many h.prepared l hp hd).le.trans
        (conjugateSpanBy_mono le_rfl le_sup_left)
  have hZT : Z ≤ centralizer (T : Set G) :=
    inf_le_left.trans (centralInvolutions_le_centralizer_sylow T)
  have hZP : Z ≤ P := inf_le_right.trans hVP
  have hnot : ¬ P ≤ normalizer (Z : Set G) := by
    intro hn
    have hPMC : P ≤ Mc := hn.trans (h.prepared.central_seed_normalizer_le_partner T h.partner)
    have hMc : Mc ∈ maximalTwoLocalOvergroups
        (centralizer (centralInvolutions T : Set G)) := h.partner ▸ Set.mem_singleton Mc
    have hm : Mc ∈ maximalTwoLocalOvergroups P := ⟨hMc.1,hPMC⟩
    rw [hw.unique] at hm
    exact h.different (Set.mem_singleton_iff.mp hm).symm
  obtain ⟨hindex,hcore⟩ := source_dihedral_five_residual_core_index h.ambient T h.empty
    h.maximal h.centralizing h.partner h.many h.prepared l hp hd
  have hcoreT : Y.pCoreIn 2 ≤ (T : Subgroup G) := by
    apply hcore.trans
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le h.maximal.1.2] using
      pCoreIn_le_sylow M (T.subtype h.maximal.1.2)
  have hTfive : ¬ 5 ∣ Nat.card T := by
    obtain ⟨n,hn⟩ := T.isPGroup'.exists_card_eq
    rw [hn]
    exact fun hh => (by decide : ¬ (5 : ℕ) ∣ 2) (Nat.Prime.dvd_of_dvd_pow (by decide) hh)
  have hi : (T : Subgroup G).relIndex P = 5 :=
    index_five_of_core_le_borel Y T hindex hcoreT hw.invariant hTfive
  have hr : IsPReduced 2 (V.subgroupOf P) :=
    reduced_of_sylow_central_seed T P V Z hTP hVP hPN inf_le_right hZT hspan
  have hnc : ¬ Z.subgroupOf P ≤ center P := by
    intro hc
    apply hnot
    apply (show P ≤ centralizer (Z : Set G) from ?_).trans (Subgroup.centralizer_le_normalizer _)
    intro x hx z hz
    exact congrArg Subtype.val (mem_center_iff.mp (hc (show (⟨z,hZP hz⟩ : P) ∈ Z.subgroupOf P from hz)) ⟨x,hx⟩).symm
  have hc : centralizer (V.subgroupOf P : Set P) = pCore 2 P := by
    have hseed : (T.subtype hTP : Subgroup P) ≤ centralizer (Z.subgroupOf P : Set P) := by
      intro t ht z hz
      exact Subtype.ext (hZT hz t ht).symm
    have hh := centralizer_normalClosure_eq_core_of_prime_index (T.subtype hTP)
      (Z.subgroupOf P) hi (by decide : Nat.Prime 5) hseed hnc
    rw [normalClosure_subgroupOf_eq_conjugateSpanBy Z P hZP,←hspan] at hh
    exact hh
  have hnT : ¬ ((T : Subgroup G).subgroupOf P).Normal := by
    intro hn
    apply hnot
    have hNT : P ≤ normalizer (T : Set G) := (normal_subgroupOf_iff_le_normalizer hTP).mp hn
    have hNZ : P ≤ normalizer (centralInvolutions T : Set G) := by
      exact hNT.trans (normalizer_le_normalizer_omegaCenterIn _)
    exact le_normalizer_inf hNZ hPN
  have hproper : pCore 2 P < (T.subtype hTP : Subgroup P) := by
    refine lt_of_le_of_ne (pCore_isPGroup.le_sylow_of_normal (T.subtype hTP)) ?_
    intro he
    apply hnT
    change pCore 2 P = (T : Subgroup G).subgroupOf P at he
    rw [←he]
    infer_instance
  refine ⟨hi,?_,hVP,hspan,hr,hc,sylow_index_five_core_quotient (T.subtype hTP) hi hproper⟩
  exact generalizedFitting_eq_pCore_of_sylow_overgroup T P M hTP hPM
    (h.ambient.evenCharacteristic T M h.maximal.1.1 h.maximal.1.2)
end CFSG.Quasithin.Chapter15.Section02
