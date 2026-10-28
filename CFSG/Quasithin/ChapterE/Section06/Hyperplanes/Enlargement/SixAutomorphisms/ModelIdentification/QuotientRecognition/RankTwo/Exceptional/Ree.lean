module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.RankTwo.Exceptional.Transport
public import Theory.GroupTheory.PerfectCyclicSylowProjection
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Linear
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Linear.FullLeviRepresentation
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Coverage
public import Theory.SpecificGroups.Suzuki.OddSubgroups
public import Theory.Representation.QuadraticFourGroup.Recognition.FactorSylows.Linear
public import Theory.GroupAction.InnerInvolutionGeometry

/-!
# The Ree fixed-component reduction

The proved normalizer cover puts an inner involution centralizer into a
conjugate full parabolic. A perfect subgroup has trivial torus projection,
and the two-group radical leaves its three-subgroups embedded in the rank-one
Levi. Cyclic Sylow three-subgroups there exclude A₆.

The linear projection is already constructed. Innerness of actor involutions
and the full Suzuki-side projection remain explicit inputs, owned respectively
by the large-Ree automorphism and Suzuki-parabolic tasks. No exhaustive root
classification, order formula, or independent simplicity certification is
needed for this route. The source simplicity/perfectness hypotheses suffice.

Source: Aschbacher–Smith E.6.23, printed p.254, and 16.1.4(1,4), p.1171,
`refs/quasithin.pdf`; GLS3 3.1.3 for the imported normalizer cover. This is the
A₆ specialization of the argument in the seven-component Ree inspection.
-/

public section
open Subgroup Theory.GroupTheory
open alternatingGroup.SixSubgroupObstructions
open ReeF4.ConverseParabolics
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.RankTwo.Exceptional.Ree

private theorem linear_rank {S : Type*} [Group S] [Finite S] [Group.IsPerfect S]
    {m : ℕ} (hm : 1 ≤ m) (f : S →* parabolic m .linear) (hf : Function.Injective f) :
    primeRank 3 S ≤ 1 :=
  perfect_threeRank_le_one_of_embedding
    (linearProjectionOfLeviHom (linearFullLeviEmbedding hm))
    (linearProjectionOfLeviHom_ker_isPGroup _ (linearFullLeviEmbedding_injective hm))
    f hf (fun U hU => Matrix.SL2.odd_pGroup_isCyclic_of_injective hU
      (by decide : 3 ≠ 2) U.subtype U.subtype_injective)

private theorem suzuki_rank {S : Type*} [Group S] [Finite S] [Group.IsPerfect S]
    {m : ℕ} (hm : 1 ≤ m)
    (π : parabolic m .suzuki →*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m × (ReeF4.CoefficientField m)ˣ)
    (hk : IsPGroup 2 π.ker)
    (f : S →* parabolic m .suzuki) (hf : Function.Injective f) : primeRank 3 S ≤ 1 := by
  apply perfect_threeRank_le_one_of_embedding π hk f hf
  intro U hU
  obtain ⟨P, hUP⟩ := hU.exists_le_sylow
  let : IsCyclic P := BenderSuzuki.MatrixGroups.suzukiSylow_isCyclic_of_ne_two
    (by omega : 0 < m) (by decide : 3 ≠ 2) P
  exact Subgroup.isCyclic_of_le hUP

/-- Conditional only on involution innerness and the missing full Suzuki
projection. The actual full-parabolic coverage and linear projection are proved. -/
theorem excludesFixedSix_of_inner_and_projection {m : ℕ} (hm : 1 ≤ m)
    [IsSimpleGroup (ReeF4.Model m)] [Group.IsPerfect (ReeF4.Model m)]
    (hinner : ∀ a : MulAut (ReeF4.Model m), orderOf a = 2 →
      ∃ x : ReeF4.Model m, a = MulAut.conj x)
    (π : parabolic m .suzuki →*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m × (ReeF4.CoefficientField m)ˣ)
    (hk : IsPGroup 2 π.ker) : ExcludesFixedSix (ReeF4.Model m) := by
  have hz : center (ReeF4.Model m) = ⊥ := by
    rcases (inferInstance : (center (ReeF4.Model m)).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative (ReeF4.Model m)
        (center_eq_top_iff.mp h)).elim
  intro a ha S hS hs
  obtain ⟨x, hx, _, hfix⟩ := MulAut.inner_involution_representative hz a ha (hinner a ha)
  have hR : zpowers x ≠ ⊥ := zpowers_ne_bot.mpr (by
    intro h; simp only [h, orderOf_one] at hx; omega)
  have hp : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := 1) (by
    simpa only [Nat.card_zpowers, pow_one] using hx)
  obtain ⟨g, s, hc⟩ := normalizer_cover hm (zpowers x) hR hp
  have hSN : S ≤ normalizer (zpowers x : Set (ReeF4.Model m)) := by
    apply (hS.1.trans ?_).trans (centralizer_le_normalizer _)
    rw [hfix, zpowers_eq_closure, centralizer_closure]
  let f₀ : S →* ReeF4.Model m := (MulAut.conj g).toMonoidHom.comp S.subtype
  let f : S →* parabolic m s := f₀.codRestrict _
    (fun y => hc (mem_map_of_mem _ (hSN y.property)))
  have hf : Function.Injective f := by
    intro y z h
    exact Subtype.ext ((MulAut.conj g).injective (congrArg Subtype.val h))
  let : IsQuasisimple S := hS.quasisimple
  have hr : primeRank 3 S ≤ 1 := by
    cases s with
    | linear => exact linear_rank hm f hf
    | suzuki => exact suzuki_rank hm π hk f hf
  obtain ⟨e⟩ := hs
  exact not_injective_of_three_rank_le_one hr e.symm.toMonoidHom e.symm.injective

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.RankTwo.Exceptional.Ree
