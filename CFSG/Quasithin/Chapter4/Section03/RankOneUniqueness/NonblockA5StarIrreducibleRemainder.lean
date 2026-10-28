module

public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockA5StarRemainder
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockA5AlternatingSevenMoved

/-!
# The actual irreducible star-action remainder for the original A₅ source

The full C.2.7 conclusion supplies the original moved section and its central
quotient action. The proved source exclusions remove every reducible row and
all irreducible rows except the natural Sp₄ and G₂ actions over F₄ and A₇.
For A₇ the strict cardinal bound supplies natural coordinates on the whole
moved space and excludes the exceptional four-space. The marked S₇ action,
irreducibility and the full B.4.2 action case are retained.
No block condition or independent choice of a quotient/module row is assumed.
Source: Aschbacher--Smith C.2.7, C.4.5--8, B.5.1 and original 4.3.7--10,
pp.145--154, 99--103 and 615--617.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open ChapterC ChapterB.QuasisimpleSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}

private theorem not_binary_four_or_five
    (d : Chapter13.Section05.A5Source.Context T L V V₁ V₂ V₃)
    (c : SourceConfiguration T L) (hf : generalizedFitting c.K = pCore 2 c.K)
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : starImage (K c) (c.I.pCoreIn 2) (K c) ≃* SL(n,ZMod 2)) : False := by
  rcases hn with rfl | rfl
  · exact c.c28.no_constrained_normal_a5_star_alternating_eight
      (normal_subgroupOf_of_le_normalizer inf_le_right) d.quotient
      c.K c.component c.quotient c.block_source_outside hf
      (e.trans (Atlas.Order20160A8.sl4TwoEquivPSL.trans
        Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.symm))
  · exact not_linearFiveTwo_star_of_a5 c hf d.quotient e

private def binarySymplecticDerivedEquiv :
    commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)) ≃* alternatingGroup (Fin 6) := by
  let e := Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm
  refine (e.subgroupMap _).trans (MulEquiv.subgroupCongr ?_)
  rw [map_commutator_eq,MonoidHom.range_eq_top.mpr e.surjective]
  exact alternatingGroup.commutator_perm_eq (by norm_num)

private theorem irreducible_rows
    {D X : Type*} [Group D] [Finite D] [AddCommGroup X] [Module (ZMod 2) X]
    [FiniteDimensional (ZMod 2) X]
    (d : Chapter13.Section05.A5Source.Context T L V V₁ V₂ V₃)
    (c : SourceConfiguration T L) (hf : generalizedFitting c.K = pCore 2 c.K)
    {ρ : Representation (ZMod 2) D X} {B : Subgroup D}
    (s : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ B)
    (j : starImage (K c) (c.I.pCoreIn 2) (K c) ≃* B)
    (source : ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase s.sectionData.action B
      (offenderSubgroup s.sectionData.action))
    (hcard : 16 < Nat.card s.sectionData.space.toSubmodule) :
    (∃ F : BinaryField, F.degree = 2 ∧ Nonempty
      (ActionEquiv (s.sectionData.action.comp B.subtype) (binarySymplectic F))) ∨
    (∃ F : BinaryField, F.degree = 2 ∧ Nonempty
      (ActionEquiv (s.sectionData.action.comp B.subtype) (binaryG2 F))) ∨
    (Nonempty (starImage (K c) (c.I.pCoreIn 2) (K c) ≃* alternatingGroup (Fin 7)) ∧
      Nonempty (MarkedActionEquiv s.sectionData.action
        (offenderSubgroup s.sectionData.action) B
        (BinaryPermutation.naturalRepresentation (Fin 7)) (alternatingGroup (Fin 7))) ∧
      quadraticRatio s.sectionData.action = 1 ∧
      IsCompl s.sectionData.space.toSubmodule (fixedSpace ρ B) ∧
      IsAlternatingNatural (s.sectionData.space.toRepresentation.comp B.subtype) 7) := by
  have hn : (L.subgroupOf (c.H ⊓ normalizer (L : Set G))).Normal :=
    normal_subgroupOf_of_le_normalizer inf_le_right
  cases source with
  | linearTwo F _ a _ _ =>
    exact (c.block_star_not_linearTwo hf F (j.trans a.groupEquiv)).elim
  | linearThree F _ a _ =>
    exact (not_linearThree_star_of_a5 d c hf F (j.trans a.groupEquiv)).elim
  | symplectic F hF _ a _ =>
    have hfour := (c.c28.constrained_normal_a5_symplectic_alignment hn d.quotient
      c.K c.component c.quotient c.block_source_outside hf (j.trans a.groupEquiv) F.card_eq hF).1
    have hdegree : F.degree = 2 := Nat.pow_right_injective (by decide : 1 < (2 : ℕ))
      (show 2 ^ F.degree = 2 ^ 2 from F.card_eq.symm.trans hfour)
    exact Or.inl ⟨F,hdegree,⟨a⟩⟩
  | symplecticTwo a _ =>
    exact (c.block_star_not_alternatingSix hf
      (j.trans (a.subgroupEquiv.trans binarySymplecticDerivedEquiv))).elim
  | g2 F hF _ a _ _ =>
    have hlarge : 4 ≤ Nat.card F.Carrier := by
      rw [F.card_eq]
      exact (show 4 = 2 ^ 2 from rfl).trans_le
        (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hF)
    have hfour := (c.c28.constrained_normal_a5_g2_alignment hn d.quotient
      c.K c.component c.quotient c.block_source_outside hf (j.trans a.groupEquiv) hlarge).1
    have hdegree : F.degree = 2 := Nat.pow_right_injective (by decide : 1 < (2 : ℕ))
      (show 2 ^ F.degree = 2 ^ 2 from F.card_eq.symm.trans hfour)
    exact Or.inr (Or.inl ⟨F,hdegree,⟨a⟩⟩)
  | g2Two a _ _ =>
    exact (c.block_star_not_g2DerivedTwo hf (j.trans a.subgroupEquiv)).elim
  | symmetric n hd a _ hr =>
    rcases hd with rfl | rfl
    · exact (c.block_star_not_alternatingFive hf (j.trans a.subgroupEquiv)).elim
    · exact Or.inr (Or.inr ⟨⟨j.trans a.subgroupEquiv⟩,⟨a⟩,hr,
        SourceCompletion.AlternatingSevenActor.natural_moved_of_card_gt_sixteen
          s a.subgroupEquiv hcard⟩)
  | alternatingSix _ a _ _ =>
    exact (c.block_star_not_alternatingSix hf (j.trans a.groupEquiv)).elim
  | alternatingSeven _ _ a hd _ _ =>
    have hsplit := (SourceCompletion.AlternatingSevenActor.natural_moved_of_card_gt_sixteen
      s a hcard).1
    have hz : s.sectionData.central.toSubmodule = ⊥ := by
      rw [s.sectionData.central_eq]
      apply bot_unique
      intro x hx
      apply Subtype.ext
      exact (disjoint_iff.mp hsplit.disjoint).le
        ⟨x.property,fun g => congrArg Subtype.val (hx g)⟩
    have hc : Nat.card s.sectionData.space.toSubmodule = 16 := by
      rw [←Nat.card_congr (s.sectionData.central.toSubmodule.quotEquivOfEqBot hz).toEquiv,
        Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hd]
      rfl
    exact (Nat.lt_irrefl 16 (hcard.trans_eq hc)).elim
  | tripleSix _ a _ =>
    have hc : (center _).map j.toMonoidHom = center _ := by
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩
        exact (centerCongr j ⟨y,hy⟩).property
      · intro hx
        exact ⟨j.symm x,(centerCongr j.symm ⟨x,hx⟩).property,j.apply_symm_apply x⟩
    exact (c.block_star_central_not_alternatingSix hf
      ((QuotientGroup.congr _ _ j hc).trans a.quotientEquiv)).elim
  | binaryLinear n hd _ a _ =>
    exact (not_binary_four_or_five d c hf hd (j.trans a.groupEquiv)).elim
  | orthogonalSix _ _ a _ _ =>
    exact (c.c28.no_constrained_normal_a5_star_alternating_eight hn d.quotient
      c.K c.component c.quotient c.block_source_outside hf (j.trans a.groupEquiv)).elim
  | symmetricEight _ a _ =>
    exact (c.c28.no_constrained_normal_a5_star_alternating_eight hn d.quotient
      c.K c.component c.quotient c.block_source_outside hf (j.trans a.subgroupEquiv)).elim
  | exteriorFive _ _ a _ _ _ =>
    exact (not_linearFiveTwo_star_of_a5 c hf d.quotient (j.trans a)).elim

private theorem source_remainder
    {D X : Type*} [Group D] [Finite D] [AddCommGroup X] [Module (ZMod 2) X]
    [FiniteDimensional (ZMod 2) X]
    (d : Chapter13.Section05.A5Source.Context T L V V₁ V₂ V₃)
    (c : SourceConfiguration T L) (hf : generalizedFitting c.K = pCore 2 c.K)
    {ρ : Representation (ZMod 2) D X} {B : Subgroup D}
    (s : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ B)
    (j : starImage (K c) (c.I.pCoreIn 2) (K c) ≃* B)
    (hcard : 16 < Nat.card s.sectionData.space.toSubmodule) :
    IsIrrPlus ρ B s.sectionData.space.toSubmodule ∧
    Function.Injective s.sectionData.action ∧
    Representation.IsIrreducible (s.sectionData.action.comp B.subtype) ∧
    ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase s.sectionData.action B (offenderSubgroup s.sectionData.action) ∧
    ((∃ F : BinaryField, F.degree = 2 ∧ Nonempty
      (ActionEquiv (s.sectionData.action.comp B.subtype) (binarySymplectic F))) ∨
    (∃ F : BinaryField, F.degree = 2 ∧ Nonempty
      (ActionEquiv (s.sectionData.action.comp B.subtype) (binaryG2 F))) ∨
    (Nonempty (starImage (K c) (c.I.pCoreIn 2) (K c) ≃* alternatingGroup (Fin 7)) ∧
      Nonempty (MarkedActionEquiv s.sectionData.action
        (offenderSubgroup s.sectionData.action) B
        (BinaryPermutation.naturalRepresentation (Fin 7)) (alternatingGroup (Fin 7))) ∧
      quadraticRatio s.sectionData.action = 1 ∧
      IsCompl s.sectionData.space.toSubmodule (fixedSpace ρ B) ∧
      IsAlternatingNatural (s.sectionData.space.toRepresentation.comp B.subtype) 7)) := by
  cases s.clause_one with
  | doubleThree F _ a _ _ =>
    exact (not_linearThree_star_of_a5 d c hf F (j.trans a.groupEquiv)).elim
  | naturalDual n hn _ ha =>
    obtain ⟨a⟩ := ha
    exact (not_binary_four_or_five d c hf hn (j.trans a.groupEquiv)).elim
  | repeatedNatural n r hn _ _ _ ha =>
    obtain ⟨a⟩ := ha
    exact (not_binary_four_or_five d c hf hn (j.trans a.groupEquiv)).elim
  | irreducible hi ha hirr source _ =>
    exact ⟨hi,ha,hirr,source,irreducible_rows d c hf s j source hcard⟩

set_option backward.isDefEq.respectTransparency false in
/-- The actual C.2.7 moved section has an irreducible central quotient, and
its remaining rows retain their action coordinates on that very section. -/
theorem a5_star_irreducible_remainder
    (d : Chapter13.Section05.A5Source.Context T L V V₁ V₂ V₃)
    (c : SourceConfiguration T L) (hf : generalizedFitting c.K = pCore 2 c.K) :
    let ρ := starRepresentation (K c) (c.I.pCoreIn 2)
    let O := offenderSubgroup ρ
    let C := starImage (K c) (c.I.pCoreIn 2) (K c)
    C ≤ O ∧ ∃ s : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp O.subtype) (C.subgroupOf O),
      let σ := s.sectionData.action
      IsIrrPlus (ρ.comp O.subtype) (C.subgroupOf O) s.sectionData.space.toSubmodule ∧
      Function.Injective σ ∧
      Representation.IsIrreducible (σ.comp (C.subgroupOf O).subtype) ∧
      ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase σ (C.subgroupOf O)
        (offenderSubgroup σ) ∧
      ((∃ F : BinaryField, F.degree = 2 ∧ Nonempty
        (ActionEquiv (σ.comp (C.subgroupOf O).subtype)
          (binarySymplectic F))) ∨
       (∃ F : BinaryField, F.degree = 2 ∧ Nonempty
        (ActionEquiv (σ.comp (C.subgroupOf O).subtype) (binaryG2 F))) ∨
       (Nonempty (C ≃* alternatingGroup (Fin 7)) ∧
        Nonempty (MarkedActionEquiv σ
          (offenderSubgroup σ) (C.subgroupOf O)
          (BinaryPermutation.naturalRepresentation (Fin 7)) (alternatingGroup (Fin 7))) ∧
        quadraticRatio σ = 1 ∧
        IsCompl s.sectionData.space.toSubmodule
          (fixedSpace (V := Additive (starV (K c) (c.I.pCoreIn 2)))
            (ρ.comp O.subtype) (C.subgroupOf O)) ∧
        IsAlternatingNatural
          (s.sectionData.space.toRepresentation.comp (C.subgroupOf O).subtype) 7)) := by
  have hs := C27Source.star_moved_section_from_source (c.block_source_input hf)
  have hCO := hs.1
  let s := Classical.choice hs.2
  let j := (subgroupOfEquivOfLe hCO).symm
  have hr := source_remainder d c hf s j
    (a5_star_moved_card_gt_sixteen d c hf hCO s.sectionData)
  exact ⟨hCO,s,hr⟩

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
