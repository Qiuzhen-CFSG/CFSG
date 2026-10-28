module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Preparation.Contracts
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Preparation.ComponentRanks.OddLinearThree
public import Theory.SpecificGroups.GL2.OddPrimeRank
public import Theory.SpecificGroups.Classical.BinaryDerivedCubicRank
public import Theory.SpecificGroups.Classical.SignedThreeCubicRank
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8

/-!
# Intrinsic component ranks before B.5.9

Start with the full B.5.5(1iv) list and the source three-rank-one hypothesis.
The derived Sp₄ and G₂ groups have explicit binary rank-two witnesses.
Two disjoint three-cycles exclude A₇. For the central triple cover of A₆,
rank one forces cyclic Sylow three-subgroups, whose quotient images remain
cyclic; the actual A₆ quotient contradicts this. Thus no arbitrary quotient
monotonicity of prime rank is used. The actual A₈–SL₄(2) equivalence and
extension of binary linear maps to dimension five exclude the last two rows.
The cubic diagonal torus forces odd field degree in the surviving SL₃ row.

SL₂ embeds in GL₂, whose odd-prime ranks are already bounded by two.
The imported determinant-one character calculation gives the same bound for
SL₃. `component_stronglyQuasithin` extracts the model from
`ComponentConclusion.chief` and `ChiefConclusion.model`, on the original
component and action. It discharges the remaining intrinsic rank premise of
`Preparation.prepared_of_component_rank`; final `Prepared` assembly belongs
to qt-b05-preliminary-seed-preparation.

The only earlier-source premise is the complete universal B.5.5 implication
`ComponentInput`. Its producer is qt-b05-quotient-components and its final
discharge belongs to qt-b05-general-classification. Neither B.5.9 nor a
classification of the seed representation is used here.

The binary embeddings reuse the constructions in the existing rank-comparison
arguments, importing only their Theory foundations. The exceptional comparison
is the licensed ATLAS port; attribution remains in its defining module.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.5(1iv),
printed pp.104–105, and the reduction preceding B.5.9, printed p.107.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions.Preparation
open QuasisimpleSource
universe u v
variable {G : Type u} [Group G] [Finite G]

private theorem binary_four_rank :
    2 ≤ primeRank 3 (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) := by
  let e := (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide : 0 < 4)).symm.trans
    Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8
  rw [primeRank_equiv 3 e]
  exact alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)

private theorem binary_five_rank :
    2 ≤ primeRank 3 (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) := by
  let e : (Fin 5 → ZMod 2) ≃ₗ[ZMod 2] ((Fin 4 → ZMod 2) × ZMod 2) :=
    LinearEquiv.ofFinrankEq (R := ZMod 2) _ _ (by simp)
  let f : BinaryLinear.OuterCyclic.LinearGroup 4 →* BinaryLinear.OuterCyclic.LinearGroup 5 :=
    { toFun := fun g => e.trans ((g.prodCongr (LinearEquiv.refl _ _)).trans e.symm)
      map_one' := by ext x; simp
      map_mul' := by intros; ext x; simp }
  have hf : Function.Injective f := by
    intro a b h
    apply LinearEquiv.ext
    intro v
    have hh := congrArg (fun g : BinaryLinear.OuterCyclic.LinearGroup 5 =>
      (e (g (e.symm (v, 0)))).1) h
    simpa [f] using hh
  let g := (BinaryLinear.OuterCyclic.slEquivLinear 5).symm.toMonoidHom.comp
    (f.comp (BinaryLinear.OuterCyclic.slEquivLinear 4).toMonoidHom)
  exact binary_four_rank.trans (primeRank_le_of_injective 3 g
    ((BinaryLinear.OuterCyclic.slEquivLinear 5).symm.injective.comp
      (hf.comp (BinaryLinear.OuterCyclic.slEquivLinear 4).injective)))

/-- Inspection of the complete B.5.5(1iv) list at three-rank one. -/
theorem componentModels_of_three_rank_one {L : Subgroup G}
    (models : ComponentModels L) (hrank : primeRank 3 L = 1) :
    (∃ F : BinaryField, Nonempty (L ≃* Matrix.SpecialLinearGroup (Fin 2) F.Carrier)) ∨
      ∃ F : BinaryField, Odd F.degree ∧
        Nonempty (L ≃* Matrix.SpecialLinearGroup (Fin 3) F.Carrier) := by
  rcases models with h | h | h | h | h | h | h | h
  · exact Or.inl h
  · obtain ⟨F, ⟨e⟩⟩ := h
    refine Or.inr ⟨F, ?_, ⟨e⟩⟩
    by_contra hn
    have hl := Theory.SpecificGroups.SignedThreeCubicRank.linear_special F.card_eq
      (Nat.not_odd_iff_even.mp hn)
    rw [primeRank_equiv 3 e] at hrank
    omega
  · obtain ⟨F, ⟨e⟩⟩ := h
    have hl := Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.symplectic
      (F := F.Carrier)
    rw [primeRank_equiv 3 e] at hrank
    omega
  · obtain ⟨F, ⟨e⟩⟩ := h
    have hl := Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.g2
      (F := F.Carrier)
    rw [primeRank_equiv 3 e] at hrank
    omega
  · obtain ⟨e⟩ := h
    have hl := alternatingGroup.TwoThreeCycles.two_le_primeRank (n := 7) (by decide)
    rw [primeRank_equiv 3 e] at hrank
    omega
  · obtain ⟨_, ⟨e⟩⟩ := h
    obtain ⟨P⟩ := Sylow.nonempty (p := 3) (G := L)
    have hu := P.primeRank_quotient_le_one
      (P.isCyclic_of_odd_of_primeRank_le_one (by decide) hrank.le) (center L)
    rw [primeRank_equiv 3 e] at hu
    have hl := alternatingGroup.TwoThreeCycles.two_le_primeRank (n := 6) (by decide)
    omega
  · obtain ⟨e⟩ := h
    have hl := binary_four_rank
    rw [primeRank_equiv 3 e] at hrank
    omega
  · obtain ⟨e⟩ := h
    have hl := binary_five_rank
    rw [primeRank_equiv 3 e] at hrank
    omega

/-- The intrinsic odd-prime bound required by `prepared_of_component_rank`. -/
theorem stronglyQuasithin_of_componentModels {L : Subgroup G}
    (_hL : IsQuasisimple L) (models : ComponentModels L)
    (hrank : primeRank 3 L = 1) : IsStronglyQuasithin L := by
  obtain h | h := componentModels_of_three_rank_one models hrank
  · obtain ⟨F, ⟨e⟩⟩ := h
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    rw [primeRank_equiv p e]
    exact (primeRank_le_of_injective p Matrix.SpecialLinearGroup.toGL
      Matrix.SpecialLinearGroup.toGL_injective).trans
        (Matrix.GeneralLinearGroup.primeRank_le_two_of_odd F.Carrier ho)
  · obtain ⟨F, _, ⟨e⟩⟩ := h
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    rw [primeRank_equiv p e]
    exact ComponentRanks.linearThree_odd_primeRank_le_two F.Carrier ho

/-- Specialize the complete earlier B.5.5 implication to the original component.
Its model witness comes from the actual faithful chief-section conclusion. -/
theorem component_stronglyQuasithin
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) {K : GroupClass.{u}}
    (earlier : ComponentInput.{u,v} K) (hyp : FFHypothesis K ρ)
    {L : Subgroup G} (hL : IsComponent G L) (hrank : primeRank 3 L = 1) :
    IsStronglyQuasithin L := by
  obtain ⟨A, _, _, ⟨chief⟩⟩ := (earlier G V ρ hyp).chief L hL
  exact stronglyQuasithin_of_componentModels hL.2 chief.model hrank

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions.Preparation
