module

public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointQuasisimpleSource
public import CFSG.Quasithin.ChapterG.Section07.SporadicLocal.PrimeEleven
public import CFSG.Quasithin.ChapterK.Section01To04.JankoTwo.TwoRank
public import Theory.Mathieu.SmallModuleRanks
public import Theory.Mathieu.M22.Properties.TwoRank
public import Theory.Mathieu.SchurMultipliers.SourceCovers
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismTwoRank
public import Theory.SpecificGroups.Rudvalis.Multiplier.Universe
public import Theory.SpecificGroups.Rudvalis.Model.TwoRankSix
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.Rudvalis

/-!
# Sporadic quotients of the original tensor point component

The eight-dimensional binary module induces automorphisms of rank at least
six. This excludes the small Mathieu, Janko and Higman--Sims quotients.
The full M₂₄ cover calculation contradicts the central nonsingular point.
For Rudvalis the multiplier bounds the center by two, improving the induced
rank to seven, while all automorphisms are inner and have rank at most six.
All conclusions concern the literal central quotient of the containing group.

Source: Aschbacher--Smith 9.4.1, printed p.735, using I.1.3.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

private theorem not_quotient_of_rank_le_five (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} [Group.IsPerfect I]
    (hLI : m.tensorPointResidual v ≤ I)
    (hIN : centralizer ({(v : G)} : Set G) ≤ normalizer (I : Set G))
    {S : Type*} [Group S] (a : I ⧸ center I ≃* S)
    (hr : primeRank 2 (MulAut S) ≤ 5) : False := by
  let : Finite S := Finite.of_equiv (I ⧸ center I) a.toEquiv
  have h := m.tensorPoint_containing_quotient_automorphism_rank v hv hLI hIN
  rw [primeRank_equiv 2 (MulAut.congr a)] at h
  omega

/-- The small sporadic quotient rows contradict the actual module action. -/
theorem tensorPoint_containing_not_small_sporadic (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} [IsQuasisimple I]
    (hLI : m.tensorPointResidual v ≤ I)
    (hIN : centralizer ({(v : G)} : Set G) ≤ normalizer (I : Set G))
    {name : ClassificationModels.SporadicName}
    (hn : name = .m11 ∨ name = .m12 ∨ name = .m22 ∨ name = .m23 ∨
      name = .j2 ∨ name = .hs)
    (a : I ⧸ center I ≃* name.Carrier) : False := by
  apply m.not_quotient_of_rank_le_five v hv hLI hIN a
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ChapterG.Section07.SporadicLocal.m11_automorphism_twoRank_le_three.trans (by decide)
  · exact Sporadic.Mathieu.m12_automorphism_twoRank_le_four.trans (by decide)
  · exact Sporadic.Mathieu.m22_automorphism_twoRank_le_five
  · exact Sporadic.Mathieu.m23_automorphism_twoRank_le_four.trans (by decide)
  · exact Sporadic.LeechRelated.J2.automorphism_primeRank_le_four.trans (by decide)
  · exact Sporadic.LeechRelated.HS.automorphism_twoRank_le_five

/-- J₁ has automorphism rank at most three. -/
theorem tensorPoint_containing_not_janko_one (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} [IsQuasisimple I]
    (hLI : m.tensorPointResidual v ≤ I)
    (hIN : centralizer ({(v : G)} : Set G) ≤ normalizer (I : Set G))
    (a : I ⧸ center I ≃* Janko1.Model) : False :=
  m.not_quotient_of_rank_le_five v hv hLI hIN a
    (ChapterG.Section07.SporadicLocal.j1_automorphism_twoRank_le_three.trans (by decide))

/-- M₂₄ has no nontrivial perfect central cover. -/
theorem tensorPoint_containing_not_mathieu_twenty_four (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} [IsQuasisimple I]
    (hLI : m.tensorPointResidual v ≤ I)
    (hIX : I ≤ centralizer ({(v : G)} : Set G))
    (a : I ⧸ center I ≃* Sporadic.Mathieu.M24) : False :=
  m.tensorPoint_containing_center_ne_bot v hv hLI hIX
    (Sporadic.Mathieu.SchurMultipliers.m24_center_eq_bot_of_centralQuotientEquiv a)

/-- The Rudvalis center bound forces rank seven, above its full automorphism rank. -/
theorem tensorPoint_containing_not_rudvalis (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} [IsQuasisimple I]
    (hLI : m.tensorPointResidual v ≤ I)
    (hIN : centralizer ({(v : G)} : Set G) ≤ normalizer (I : Set G))
    (a : I ⧸ center I ≃* Rudvalis.Model) : False := by
  let : IsSimpleGroup (I ⧸ center I) := IsQuasisimple.simple
  let : IsSimpleGroup Rudvalis.Model := a.symm.isSimpleGroup
  let : Group.IsPerfect Rudvalis.Model :=
    Group.IsPerfect.ofSurjective (f := a.toMonoidHom) a.surjective
  have hZ : Nat.card (center I) ≤ 2 := by
    rw [← PerfectCentralCovering.centralQuotientCover_ker a]
    exact Rudvalis.Multiplier.cover_kernel_card_le_two_any_universe
      (PerfectCentralCovering.centralQuotientCover a)
  have hlo := m.tensorPoint_containing_quotient_automorphism_rank_seven v hv hLI hIN hZ
  rw [primeRank_equiv 2 (MulAut.congr a)] at hlo
  let b : Rudvalis.Model ≃* MulAut Rudvalis.Model := MulEquiv.ofBijective MulAut.conj
    ⟨MulAut.conj_injective_of_center_eq_bot center_eq_bot_of_simple_perfect,
      Chapter1.XiEmbedding.OuterModels.rudvalis_conj_surjective⟩
  have hhi : primeRank 2 (MulAut Rudvalis.Model) ≤ 6 := by
    rw [← primeRank_equiv 2 b]
    exact Rudvalis.primeRank_le_six
  omega

/-- The full eleven-entry sporadic catalogue reduces to Held and J₄. -/
theorem tensorPoint_containing_sporadic_held_or_janko4 (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} [IsQuasisimple I]
    (hLI : m.tensorPointResidual v ≤ I)
    (hIX : I ≤ centralizer ({(v : G)} : Set G))
    (hIN : centralizer ({(v : G)} : Set G) ≤ normalizer (I : Set G))
    (hc : ChapterA.Section02.IsTheoremCSporadicModel (I ⧸ center I)) :
    Nonempty (I ⧸ center I ≃* Held.He) ∨ Nonempty (I ⧸ center I ≃* Janko4.Model) := by
  rcases hc with ⟨name,hn,⟨a⟩⟩ | ⟨a⟩
  · cases name with
    | m11 | m12 | m22 | m23 | j2 | hs =>
      exact (m.tensorPoint_containing_not_small_sporadic v hv hLI hIN (by simp) a).elim
    | m24 => exact (m.tensorPoint_containing_not_mathieu_twenty_four v hv hLI hIX a).elim
    | j3 => exact (hn rfl).elim
    | j4 => exact Or.inr ⟨a⟩
    | he => exact Or.inl ⟨a⟩
    | ru => exact (m.tensorPoint_containing_not_rudvalis v hv hLI hIN a).elim
  · exact (m.tensorPoint_containing_not_janko_one v hv hLI hIN a.some).elim

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
