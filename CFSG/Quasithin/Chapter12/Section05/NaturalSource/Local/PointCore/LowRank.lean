module

public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.PointCore.Movement
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.OddThreeExtensionProjectiveModels
public import Theory.GroupTheory.PerfectSmallNormalizerAction
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.GroupTheory.SubgroupTransport
public import Theory.Quasithin.CoprimeRank
public import Theory.Alternating.PrimeRank

/-!
# The original point module in low-rank component quotients

The image of the elementary seed in a quotient of two-rank at most two has
order at most four. The perfect original point residual normalizes that image
and therefore centralizes it. The literal identity [V,L₁] = V forces the
image to vanish. Relative normality then gives V ≤ O₂(G₁).

Both signed odd ternary models have the required rank, as do the triple
covers of A₆ and A₇: their odd central quotient preserves two-rank. These
arguments require neither LocalComponents nor a refined point alternative.
PointCore.Complete assembles them with the full source component catalogue.
Source: Aschbacher--Smith 12.5.8(1), printed p.820, using the models of A.3.6.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 Chapter1.Section02.LocalModels
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

/-- The original fully moved seed vanishes in every containing two-rank-two quotient. -/
theorem seed_le_twoCore_of_quotient_twoRank_le_two {K : Subgroup G}
    (hLK : s.marking.Li 1 ≤ K)
    (hr : primeRank 2 (K ⧸ pCore 2 K) ≤ 2) : V ≤ K.pCoreIn 2 := by
  let B := s.marking.Li 1
  let hVK : V ≤ K := s.seed_le_point_residual.trans hLK
  let A := V.subgroupOf K
  let C := B.subgroupOf K
  let r := QuotientGroup.mk' (pCore 2 K)
  let := D.elementary
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf hVK
  let : IsElementaryAbelian 2 (A.map r) := IsElementaryAbelian.map r
  have hc : Nat.card (A.map r) ≤ 4 :=
    (primeRank_le_iff_elementary_card_le _).mp hr (A.map r) inferInstance
  let : Group.IsPerfect B := s.marking.Li_perfect 1
  let a : C ≃* B := subgroupOfEquivOfLe hLK
  let : Group.IsPerfect C := Group.IsPerfect.ofSurjective
    (f := a.symm.toMonoidHom) a.symm.surjective
  let : Group.IsPerfect (C.map r) := Group.IsPerfect.map r
  have hn : C.map r ≤ normalizer (A.map r : Set (K ⧸ pCore 2 K)) := by
    apply (map_mono (f := r) ?_).trans (A.le_normalizer_map r)
    intro c hc x
    exact ((s.marking.Li_le_L 1).trans D.normalizes) hc (x : G)
  have hcomm : ⁅C.map r,A.map r⁆ = ⊥ :=
    commutator_eq_bot_of_perfect_normalizer_card_le_four _ _ hn hc
  have hmove : ⁅A.map r,C.map r⁆ = A.map r := by
    rw [← map_commutator, ← SubgroupTransport.subgroupOf_commutator V _ hVK hLK]
    exact congrArg (fun X : Subgroup G => (X.subgroupOf K).map r) s.seed_point_commutator
  have hz : A.map r = ⊥ := hmove.symm.trans (commutator_comm _ _ |>.trans hcomm)
  have hA : A ≤ pCore 2 K := by
    simpa only [r, QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff A).mp hz
  intro v hv
  exact ⟨⟨v,hVK hv⟩,hA hv,rfl⟩

/-- Relative normality lifts the low-rank quotient conclusion to the actual point core. -/
theorem seed_le_point_core_of_quotient_twoRank_le_two {K : Subgroup G}
    (hLK : s.marking.Li 1 ≤ K) (hKG : K ≤ s.marking.Gi 1)
    (hn : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hr : primeRank 2 (K ⧸ pCore 2 K) ≤ 2) : V ≤ (s.marking.Gi 1).pCoreIn 2 :=
  (s.seed_le_twoCore_of_quotient_twoRank_le_two hLK hr).trans
    (pCoreIn_mono_of_normalizes hKG ((normal_subgroupOf_iff_le_normalizer hKG).mp hn))

/-- Both signed odd ternary families, including their special covers, satisfy point-core containment. -/
theorem seed_le_point_core_of_odd_ternary {K : Subgroup G}
    (hLK : s.marking.Li 1 ≤ K) (hKG : K ≤ s.marking.Gi 1)
    (hn : (K.subgroupOf (s.marking.Gi 1)).Normal)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (unitary : Bool)
    (hm : IsPSLSign (K ⧸ pCore 2 K) unitary 3 p ∨
      IsSLSign (K ⧸ pCore 2 K) unitary 3 p) : V ≤ (s.marking.Gi 1).pCoreIn 2 := by
  let : Fact p.Prime := ⟨hp⟩
  exact s.seed_le_point_core_of_quotient_twoRank_le_two hLK hKG hn
    (ChapterA.Section03.SourceEmbeddings.odd_three_two_rank ho unitary hm)

/-- Odd central three-covers of the small alternating groups retain two-rank at most two. -/
theorem seed_le_point_core_of_small_alternating_cover {K : Subgroup G}
    (hLK : s.marking.Li 1 ≤ K) (hKG : K ≤ s.marking.Gi 1)
    (hn : (K.subgroupOf (s.marking.Gi 1)).Normal)
    {n : ℕ} (hn7 : n ≤ 7) (hm : IsAlternatingCover (K ⧸ pCore 2 K) n) :
    V ≤ (s.marking.Gi 1).pCoreIn 2 := by
  apply s.seed_le_point_core_of_quotient_twoRank_le_two hLK hKG hn
  let Q := K ⧸ pCore 2 K
  obtain ⟨z⟩ := hm.2.1
  obtain ⟨e⟩ := hm.2.2
  have hc : Nat.card (center Q) = 3 := by simpa using Nat.card_congr z.toEquiv
  have hr := primeRank_le_of_coprime_ker 2 (QuotientGroup.mk' (center Q))
    (by rw [QuotientGroup.ker_mk', hc]; decide)
  rw [primeRank_congr 2 e,
    (GLS3.Chapter5.PRank.alternating_hasPRank_two n).primeRank_eq Nat.prime_two] at hr
  change primeRank 2 Q ≤ 2
  omega

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
