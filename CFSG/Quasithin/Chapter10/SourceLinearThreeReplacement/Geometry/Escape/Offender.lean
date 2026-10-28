module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.Escape.Coordinates
public import CFSG.Quasithin.ChapterI.Section06To08.TIConjugates
public import CFSG.Quasithin.ChapterE.Section03.Offenders.Transport

/-!
# The literal rank-four offender in the whole-module TI branch

The value w=2 is attained by A=Vᵍ∩N_G(V). Since |V|=64, rank additivity
makes A elementary of rank four. If any nonidentity element of A centralizes
V, the elementary TI-pair theorem forces V and Vᵍ to commute, contrary to
the offender condition. Thus the action is faithful. The same TI-pair theorem
identifies every C_V(a), for a∈A# , with the opposite mutual normalizer and
therefore with C_V(A).

This proves the offender construction in the second paragraph of
Aschbacher--Smith 10.3.2, printed p.756. The whole-module TI hypothesis remains
explicit for its independent diagonal-fusion producer.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.Escape
open Chapter3.Section02 ChapterE ChapterI.Section06To08 Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  (s : SourceLinearThreeSurvivor T D)
include s

/-- The genuine w-offender has rank four, acts faithfully, and has constant
nonidentity fixed subgroups on the original full module. -/
theorem ti_offender
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (hTI : IsTISubgroup D.fullModule) :
    ∃ g : G, IsWOffenderAt D.fullModule (T : Subgroup G) g ∧
      let A := offenderNormalizer D.fullModule g
      A ≤ D.maximalLocal ∧ IsElementaryAbelian 2 A ∧ rank A = 4 ∧
      A ⊓ centralizer (D.fullModule : Set G) = ⊥ ∧
      ∀ a ∈ A, a ≠ 1 →
        D.fullModule ⊓ centralizer ({a} : Set G) =
          D.fullModule ⊓ centralizer (A : Set G) := by
  let V := D.fullModule
  let : IsElementaryAbelian 2 V := by
    change IsElementaryAbelian 2 D.fullModule
    exact s.full_eq_local.symm ▸ D.module_elementary
  obtain ⟨g,hg⟩ := exists_isWOffenderAt_of_globalW_eq_nat
    (source_fullModule_weakClosure_hypotheses D) s.weakClosure
  let W := V.map (MulAut.conj g).toMonoidHom
  let A := offenderNormalizer V g
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 A := offender_elementary_of_le
    (show A ≤ W from inf_le_left)
  have hWM : A ≤ D.maximalLocal := inf_le_right.trans (source_fullModule_normalizer D).le
  have hrankW : rank W = 6 := by
    have hc : Nat.card W = Nat.card V := card_map_of_injective (MulAut.conj g).injective
    have hh : Nat.card W = 64 := hc.trans (full_card s hz)
    norm_num [rank,hh]
  have hcor : subgroupCorank W A = 2 := by
    have hh := hg.2
    rw [s.weakClosure] at hh
    exact ENat.natCast_inj.mp hh.symm
  have hsum : rank W = 2 + rank A := by
    have hh := offender_corank_add (W := W) (A := A) (B := ⊥) bot_le inf_le_left
    rw [hcor] at hh
    simpa only [subgroupCorank, relIndex_bot_left, rank] using hh
  have hrank : rank A = 4 := by omega
  have hd : Disjoint V W := by
    rcases hTI.eq_or_disjoint_conjugate g with he | hd
    · exfalso
      apply hg.1
      rw [he]
      exact commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer _)
    · exact hd.symm
  have hTW : IsTISubgroup W := hTI.map_equiv (MulAut.conj g)
  have hcard : Nat.card V = Nat.card W := (card_map_of_injective (MulAut.conj g).injective).symm
  have hfaith : A ⊓ centralizer (V : Set G) = ⊥ := by
    by_contra hn
    have hn' : W ⊓ centralizer (V : Set G) ≠ ⊥ := by
      intro he
      exact hn (bot_unique ((inf_le_inf_right _ (show A ≤ W from inf_le_left)).trans_eq he))
    have hf := ti_pair_full_normalizer_of_centralizer_ne_bot V W hd hTW hn'
    exact hg.1 (commutator_eq_bot_iff_le_centralizer.mpr
      (ti_pair_commute_of_full_normalizer V W hd hTI hTW hcard hf))
  refine ⟨g,hg,hWM,inferInstance,hrank,hfaith,?_⟩
  intro a ha hane
  have he := ti_pair_opposite_normalizer_eq_centralizer W V hd.symm hTW
    ha.1 ha.2 hane
  change V ⊓ centralizer ({a} : Set G) = V ⊓ centralizer (A : Set G)
  rw [← he]
  apply le_antisymm
  · exact le_inf inf_le_left (ti_pair_mutual_normalizers_commute V W hd)
  · intro v hv
    rw [he]
    exact ⟨hv.1, mem_centralizer_singleton_iff.mpr (hv.2 a ha).symm⟩

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.Escape
