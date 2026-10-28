module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Inspection.Lie
public import Theory.GroupTheory.PrimeRankNormalIntersection.Kernel
/-!
# The actual module centralizer has no cubic

The original component has cubic rank two, and its action kernel is its
actual two-core. The normal-intersection argument therefore makes the
whole module-action kernel prime to three. This identifies the bound on
C_G(V), with the original normalizer and module unchanged. The faithful
plane action then bounds the cubic part of C_M(A) and of its literal
star intersection by three.

These bounds feed the A₅ exclusion and field-parameter inspection in
original 13.3.12, printed pp.889--890 (Aschbacher--Smith).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  [IsElementaryAbelian 2 V]

/-- The original full module centralizer has order prime to three. -/
theorem Context.module_centralizer_coprime_three (s : Context T L V) :
    Nat.Coprime 3 (Nat.card (centralizer (V : Set G))) := by
  let N := normalizer (V : Set G)
  let D := L.subgroupOf N
  let e : D ≃* L := subgroupOfEquivOfLe s.chosen.normalizes
  let f := V.normalizerMonoidHom
  let : IsSimpleGroup Atlas.G2.Natural.BinaryNormalizer.Derived :=
    Atlas.G2.isSimple_commutator_binary
  have hk : (f.comp D.subtype).ker = (pCore 2 L).comap e.toMonoidHom := by
    ext x
    rw [←s.chosen.centralizer_eq_core_of_simple s.quotient.isSimpleGroup]
    change x.val ∈ f.ker ↔ (x.val : G) ∈ centralizer (V : Set G)
    rw [V.normalizerMonoidHom_ker]
    rfl
  have hp : IsPGroup 2 (f.comp D.subtype).ker := by
    rw [hk]
    exact pCore_isPGroup.comap_of_injective e.toMonoidHom e.injective
  have hcop : Nat.Coprime 3 (Nat.card (f.comp D.subtype).ker) := by
    obtain ⟨n,hn⟩ := hp.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hrL : 2 ≤ primeRank 3 D := by
    rw [primeRank_equiv 3 e,
      ←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 L) pCore_isPGroup,
      primeRank_equiv 3 s.quotient]
    exact Atlas.G2.EvenThreeRank.two_le_primeRank_derived
  have hr : primeRank 3 N ≤ 2 :=
    (s.hypothesis.qtke.twoLocal_sqtk
      ⟨V,s.chosen.ne_bot,IsElementaryAbelian.isPGroup 2 V,rfl⟩).stronglyQuasithin
        3 Nat.prime_three (by decide)
  have hc := f.ker_coprime_of_restriction_rank_two D hcop hrL hr
  rw [V.normalizerMonoidHom_ker,Nat.card_congr
    (subgroupOfEquivOfLe (Subgroup.centralizer_le_normalizer (V : Set G))).toEquiv] at hc
  exact hc
/-- A cubic in the actual module centralizer is impossible. -/
theorem Context.no_module_centralizer_cubic (s : Context T L V)
    (x : G) (hx : x ∈ centralizer (V : Set G)) (ho : orderOf x = 3) : False := by
  exact Nat.prime_three.coprime_iff_not_dvd.mp s.module_centralizer_coprime_three
    (ho ▸ Subgroup.orderOf_dvd_natCard (centralizer (V : Set G)) hx)

/-- The pointwise plane action and its actual kernel leave only one factor
of three in the order of C_M(A). -/
theorem Context.plane_local_nine_not_dvd (s : Context T L V) (d : MarkedPlane V) :
    ¬ 9 ∣ Nat.card (centralizer (d.A : Set G) ⊓ normalizer (L : Set G) : Subgroup G) := by
  let M := centralizer (d.A : Set G) ⊓ normalizer (L : Set G)
  let f := s.planeCentralizerAction d
  have hk : Nat.Coprime 3 (Nat.card f.ker) := by
    rw [s.planeCentralizerAction_ker d]
    rw [Nat.card_congr (subgroupOfEquivOfLe (show centralizer (V : Set G) ≤ M from
      le_inf (Subgroup.centralizer_le d.le_module) s.earlier_geometry.1.centralizer_le)).toEquiv]
    exact s.module_centralizer_coprime_three
  have hk9 : Nat.Coprime 9 (Nat.card f.ker) := by
    simpa using hk.pow_left 2
  have hc := f.ker.card_mul_index
  rw [index_eq_card] at hc
  intro hd
  have hq : 9 ∣ Nat.card (M ⧸ f.ker) := hk9.dvd_mul_left.mp (hc.symm ▸ hd)
  exact (by decide : ¬ 9 ∣ 6) (hq.trans (s.planeCentralizerAction_quotient_card_dvd_six d))

open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface

/-- The same order obstruction descends to the literal C.2.7 star intersection. -/
theorem Context.plane_starM_nine_not_dvd (s : Context T L V) (d : MarkedPlane V)
    (J : Subgroup G) :
    ¬ 9 ∣ Nat.card (starM J ((L ⊔ T).pCoreIn 2)
      (centralizer (d.A : Set G) ⊓ normalizer (L : Set G))) := by
  let M := centralizer (d.A : Set G) ⊓ normalizer (L : Set G)
  intro hd
  apply s.plane_local_nine_not_dvd d
  exact hd.trans ((card_map_dvd ((M ⊓ J).subgroupOf (J ⊔ (L ⊔ T).pCoreIn 2))
    (QuotientGroup.mk' (starKernel J ((L ⊔ T).pCoreIn 2)))).trans
      (by
        rw [Nat.card_congr (subgroupOfEquivOfLe (show M ⊓ J ≤ J ⊔ (L ⊔ T).pCoreIn 2 from
          inf_le_right.trans le_sup_left)).toEquiv]
        exact card_dvd_of_le inf_le_left))

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
