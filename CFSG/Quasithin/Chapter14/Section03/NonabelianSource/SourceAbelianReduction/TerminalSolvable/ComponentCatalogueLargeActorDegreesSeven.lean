module

public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueLargeActorDegreesSieve
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.Sieve

/-!
# Excluding the natural A₇ row for the original larger actor

The faithful extension of the marked natural A₇ action embeds the whole
dotted group in S₇. Hence the original elementary actor has rank at most
three, and the larger-actor inequality makes its rank exactly three in
degree six. The proved degree-six kernel calculation now identifies the
terminal kernel with O₂(H). Since F*(H-dot) is simple, every moved component
is that actual A₇ subgroup. Lifting it and transporting the kernel gives
the original K/O₂(K) ≅ A₇, excluded by the source empty-family sieve.

This proves the exclusion directly from the original rank-two hypotheses;
no point-centralizer three-rank implication or classification certificate is
assumed. Source: Aschbacher--Smith 14.3.6, 14.3.13--14, printed pp.991--994;
G.11.2(4), printed p.364.
-/

public noncomputable section
open Subgroup Module Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

namespace LargeActorSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  (s : LargeActorSource T M Mc F g B v)
include s

/-- G.11.2(4) is impossible for the literal larger actor. The quotient
used by the source A₇ sieve is derived from the six-dimensional action. -/
theorem not_caseFour : ¬ ChapterG.Section11.CaseFour F.terminalRepresentation := by
  rintro ⟨hd, eF, eV, he⟩
  obtain ⟨f, hf, _, _⟩ := BinaryPermutation.SevenParabolic.faithful_extension
    (generalizedFitting F.TerminalHdot) F.terminalRepresentation s.hypothesis.faithful eF eV he
  let X := F.terminalDot (F.X g)
  let : IsElementaryAbelian 2 (X.map f) := IsElementaryAbelian.map f
  have hc := AlternatingSevenConjugatePair.ElementaryGeometry.elementary_card_le
    (A := X.map f) inferInstance
  rw [Subgroup.card_map_of_injective hf, Nat.card_congr Additive.ofMul,
    Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hc
  have hmle : finrank (ZMod 2) (Additive X) ≤ 3 :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc
  have hmge := s.half_degree_le_actor
  have hm : finrank (ZMod 2) (Additive X) = 3 := by dsimp only [X] at hmle ⊢; omega
  have hfit := Recognition.original_terminal_fitting_centralizer_ne_bot
    s.simple T s.empty s.maximal s.unique_overgroup s.many_overgroups s.seed_card
    (Classical.choice s.centralizer_quotient) F s.nonabelian g s.parabolic_mem
    s.normalizer_not_mem s.nonsolvable
  obtain ⟨D, hD, hmove, _⟩ :=
    s.hypothesis.exists_moved_component_constituents s.nonsolvable hfit
  let : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by simp : 5 ≤ Nat.card (Fin 7))
  let : IsSimpleGroup (generalizedFitting F.TerminalHdot) := eF.isSimpleGroup
  have hle : D ≤ generalizedFitting F.TerminalHdot := component_le_generalizedFitting _ D hD
  have hne : D.subgroupOf (generalizedFitting F.TerminalHdot) ≠ ⊥ := by
    intro hb
    have hh := congrArg (map (generalizedFitting F.TerminalHdot).subtype) hb
    rw [map_subgroupOf_eq_of_le hle, Subgroup.map_bot] at hh
    exact hD.isCComponent.ne_bot hh
  have heq : D = generalizedFitting F.TerminalHdot := by
    have ht := (show (D.subgroupOf (generalizedFitting F.TerminalHdot)).IsSubnormal
      from hD.1.subgroupOf).eq_bot_or_top_of_isSimpleGroup inferInstance
    exact le_antisymm hle (subgroupOf_eq_top.mp (ht.resolve_left hne))
  have hnorm : D.Normal := heq.symm ▸ inferInstance
  let eD : D ≃* alternatingGroup (Fin 7) := (MulEquiv.subgroupCongr heq).trans eF
  obtain ⟨K, hKH, hlocal, hcomp, himage, _, hspan⟩ :=
    Recognition.terminal_component_lift s.simple F (by decide) D hD
  change F.terminalDot K = D at himage
  have hK : ComponentLift F g K :=
    ⟨hKH, hlocal, hcomp, himage.symm ▸ hD, himage.symm ▸ hmove, hspan⟩
  have hk := rankTwo_terminal_kernel_of_six_three
    (source_lemma_14_2_4 s.simple T s.empty s.maximal s.unique_overgroup s.many_overgroups
      s.seed_card (Classical.choice s.centralizer_quotient))
    F s.nonabelian g s.parabolic_mem s.normalizer_not_mem s.hypothesis hd hm
  let eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7) :=
    (hK.twoCoreQuotientEquivDot hk).trans ((MulEquiv.subgroupCongr himage).trans eD)
  exact source_excluded_quotient_row_false s.simple T s.empty s.maximal s.unique_overgroup
    s.many_overgroups s.seed_card (Classical.choice s.centralizer_quotient) s.not_model F g K hK
    (hK.eq_conjugateSpanBy_of_image_normal (himage.symm ▸ hnorm))
    (Or.inr (Or.inl ⟨eK⟩))

/-- Apply the A₇ exclusion to the existing literal catalogue sieve. Only
the split six-space and outer Ω₄⁺(4) rows remain beyond the required degree
alternatives. Exhaustiveness of the catalogue is still an explicit premise. -/
theorem degree_cases_or_remaining_five_seven
    (hc : ChapterG.Section11.Conclusion F.terminalRepresentation B
      (F.terminalDot (F.X g))) :
    ((finrank (ZMod 2) (Additive F.Uhat) = 4 ∧
        2 ≤ finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) ∨
      (finrank (ZMod 2) (Additive F.Uhat) = 6 ∧
        finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 3 ∧
        Nonempty (F.TerminalHdot ≃* Atlas.G2.Model (ZMod 2)))) ∨
      (ChapterG.Section11.CaseFive F.terminalRepresentation B ∨
        ChapterG.Section11.CaseSeven F.terminalRepresentation (F.terminalDot (F.X g))) := by
  rcases s.degree_cases_or_remaining_catalogue hc with hdegrees | h4 | h5 | h7
  · exact Or.inl hdegrees
  · exact (s.not_caseFour h4).elim
  · exact Or.inr (Or.inl h5)
  · exact Or.inr (Or.inr h7)

end LargeActorSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
