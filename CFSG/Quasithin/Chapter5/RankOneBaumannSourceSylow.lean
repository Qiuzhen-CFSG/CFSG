module
public import CFSG.Quasithin.Chapter5.RankOneBaumannSourceInput
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Quotient
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.LocalSylow
public import CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.BlockSylow
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Theory.GroupTheory.SelfCentralizingCorePGroupJoin
public import Theory.SpecificGroups.SL2.FrattiniParabolic
public import Theory.GroupTheory.SylowLocalCore

/-!
# Rank-one normalizer control for a Sylow-invariant subgroup

For R normal in T and containing a Sylow subgroup of L, T is already Sylow
in N_G(R). Apply the local C.5.6 obstruction directly to LT and N_G(R).
Uniqueness over LT rules out common normal subgroups, while the actual
PSL2 quotient gives three-rank at most one. Thus N_G(R) lies in N_G(L).

In particular, this applies to Baum(T) once the natural-module branch
supplies its Sylow intersection with L. No uniqueness over L or chosen
module is needed for this Sylow-invariant case.
Source: Aschbacher--Smith 4.3.1, 4.3.17 and 5.1.7(1), pp.613,619,633.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open Chapter4.Section03.RankOneUniqueness
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W : Subgroup G} {n : ℕ}

/-- The original rank-one Sylow join is a minimal parabolic. -/
theorem Input.local_minimal_parabolic
    (h : Input KnownSimple.IsKnownSimple T L W n) :
    ChapterB.IsMinimalParabolicOver
      (T.subtype (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)) ⊤ := by
  let H := L ⊔ (T : Subgroup G)
  let A := L.subgroupOf H
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  let : A.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer h.sylow_normalizes)
  let e : A ≃* L := subgroupOfEquivOfLe le_sup_left
  obtain ⟨F, _, _, hF, ⟨eF⟩⟩ := h.linear
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  let e' := eF.trans (Theory.PSL2.sl2QuotientEquiv F).symm
  let q := e'.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 L)).comp e.toMonoidHom)
  have hq : Function.Surjective q :=
    e'.surjective.comp ((QuotientGroup.mk'_surjective _).comp e.surjective)
  have hk : q.ker = pCore 2 A := by
    ext x
    change e' (QuotientGroup.mk' (pCore 2 L) (e x)) = 1 ↔ x ∈ pCore 2 A
    rw [e'.map_eq_one_iff]
    change e x ∈ (QuotientGroup.mk' (pCore 2 L)).ker ↔ x ∈ pCore 2 A
    rw [QuotientGroup.ker_mk', ← pCore_map_iso 2 e, mem_map_equiv]
    simp
  have hg : A ⊔ (S : Subgroup H) = ⊤ := by
    change L.subgroupOf H ⊔ (T : Subgroup G).subgroupOf H = ⊤
    rw [← subgroupOf_sup (show L ≤ H from le_sup_left) le_sup_right, subgroupOf_self]
  apply minimal_over_normal_rankOne_frattini F A S hg q hq
  rw [hk]
  intro x hx
  change (x : A ⧸ pCore 2 A) ∈ frattini (A ⧸ pCore 2 A)
  rw [(QuotientGroup.eq_one_iff _).mpr hx]
  exact one_mem _

/-- The local Sylow step of 4.3.1 on the original input, with T already
normalizing R. Only uniqueness over LT is used. -/
theorem Input.normalizer_le_of_sylow_invariant
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (R : Subgroup G) (hRT : R ≤ (T : Subgroup G))
    (hTR : (T : Subgroup G) ≤ normalizer (R : Set G))
    (Q : Sylow 2 L) (hQ : (Q : Subgroup L).map L.subtype ≤ R) :
    normalizer (R : Set G) ≤ normalizer (L : Set G) := by
  classical
  by_contra hout
  let M₀ := normalizer (R : Set G)
  let H := L ⊔ (T : Subgroup G)
  let P := T.subtype hTR
  let P₀ := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  have hP : (P : Subgroup M₀).map M₀.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le hTR
  have hP₀ : (P₀ : Subgroup H).map H.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le le_sup_right
  have hR := T.isPGroup'.to_le hRT
  have hRM := hRT.trans h.sylow_normalizes
  obtain ⟨P₁,hP₁⟩ := ChapterC.Section05.CounterexampleCharacteristic.chiZeroBlock_extension_sylow
    L R hR hRM Q hQ
  have hr : ∃ Z : Sylow 2 (R ⊔ L : Subgroup G),
      (Z : Subgroup (R ⊔ L : Subgroup G)).map (R ⊔ L).subtype = R := by
    rw [sup_comm R L]
    exact ⟨P₁,hP₁⟩
  obtain ⟨Z,hZ⟩ := hr
  have hf : generalizedFitting H = pCore 2 H :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2
      (centralizer_pCore_sup_le 2 L (T : Subgroup G)
        (by rw [←h.local_mem.2.2.2.1]; exact centralizer_generalizedFitting_le L)
        T.isPGroup' h.sylow_normalizes)
  have hHM : H ≤ normalizer (L : Set G) := sup_le L.le_normalizer h.sylow_normalizes
  have hH : IsSQTK KnownSimple.IsKnownSimple H :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hHM)).mp
      ((h.qtke.twoLocal_sqtk h.maximal.1).subgroup (H.subgroupOf (normalizer (L : Set G))))
  let c : ChapterC.Section05.BlockAnalysis.OriginalHypotheses H M₀ L R (T : Subgroup G) := {
    fitting := hf
    sylow := P₀
    sylow_image := hP₀
    unique := h.local_minimal_parabolic.1
    residual := embedded_pResidual_join_pGroup L (T : Subgroup G)
      h.local_mem.2.2.1 T.isPGroup' h.sylow_normalizes
    R_le := hRT
    T_le := hTR
    R_normal := le_rfl
    residual_sylow := Z
    residual_sylow_image := hZ
    no_common_normal := by
      intro N hNR hn
      by_contra hne
      have hNG : M₀ ⊔ H ≤ normalizer (N : Set G) :=
        (normal_subgroupOf_iff_le_normalizer
          (hNR.trans (R.le_normalizer.trans le_sup_left))).mp hn
      have hb := normalizer_le_of_unique_maximalTwoLocal
        (Chapter5.RankOneBaumannSource.unique_sylow_join h.qtke h.maximal_local
          h.sylow_normalizes) (hR.to_le hNR) hne (le_sup_right.trans hNG)
      exact hout (le_sup_left.trans (hNG.trans hb)) }
  have hrank : primeRank 3 H ≤ 1 := by
    rw [← ResidualCentralizerRank.primeRank_residual (by decide : Nat.Coprime 2 3)]
    let e : (pResidual 2 H) ≃* L :=
      (equivMapOfInjective (pResidual 2 H) H.subtype H.subtype_injective).trans
        (MulEquiv.subgroupCongr c.residual)
    rw [primeRank_congr 3 e]
    exact odd_primeRank_le_one h.linear (by decide)
  exact c.false_of_localSylow_threeRank_one hH hrank P hP

/-- The natural branch's Sylow intersection suffices on the original input. -/
theorem Input.baumann_normalizer_of_component_sylow
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (Q : Sylow 2 L)
    (hQ : (Q : Subgroup L).map L.subtype ≤ ChapterB.baumann (T : Subgroup G)) :
    normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G) :=
  h.normalizer_le_of_sylow_invariant _ inf_le_left
    ((T : Subgroup G).le_normalizer.trans (Stellmacher.normalizer_le_normalizer_baumann _)) Q hQ

/-- E.2.3's relative Sylow conclusion supplies the required intersection. -/
theorem Input.baumann_normalizer_of_baumann_sylow
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hs : Chapter1.IsSylowIn 2 (ChapterB.baumann (T : Subgroup G))
      (L ⊔ ChapterB.baumann (T : Subgroup G))) :
    normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G) := by
  let S := ChapterB.baumann (T : Subgroup G)
  let J := L ⊔ S
  obtain ⟨P,hP⟩ := hs
  have hJL : J ≤ normalizer (L : Set G) :=
    sup_le L.le_normalizer (inf_le_left.trans h.sylow_normalizes)
  obtain ⟨Q,hQ⟩ := P.exists_map_subtype_eq_inf_of_normalizes
    (show L ≤ J from le_sup_left) hJL
  exact h.baumann_normalizer_of_component_sylow Q
    (hQ.le.trans (inf_le_left.trans_eq hP))

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
