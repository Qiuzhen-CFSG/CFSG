module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Components.Stabilization
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.RankOne
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Restriction
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections
public import Theory.GroupTheory.SylowOvergroupSolvability

/-!
# The selected strict component in source 10.2.6

Select whichever member of the original containing pair is strictly larger.
Its ambient image is normal only in H, lies outside M, and retains the full
odd-prime rank constraints. The original R=O₂(L₀T) gives C.2.3 directly in H.
Consequently the constrained branch needs only its intrinsic quasisimple
quotient to construct the full C.2.7 input.

A binary SL₂ quotient is excluded using the literal intersection of the
supplied Sylow with this component: a proper Sylow overgroup in the rank-one
cover is solvable, whereas the original local C-component is nonsolvable.
No factor-five or A₅ hypothesis enters this exclusion.

Source: Aschbacher--Smith, 10.2.6, pp.748--749; A.3.12, pp.47--48.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02 Chapter1 ChapterA.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}

/-- The strict factor selected from the actual containing pair. Its rank
field is produced by `ContainingPair.odd_ranks`, after distinctness is proved. -/
structure RankedEnlargement
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (H : Subgroup G) (s : G) (K : Subgroup G) : Prop where
  maximal : IsMaximalTwoLocal H
  half_le : halfJoin T L ≤ H
  sylow : IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (L : Set G)) H
  component : K ∈ cComponentsIn H
  normal : (K.subgroupOf H).Normal
  s_mem : s ∈ (T : Subgroup G)
  strict : L.map (MulAut.conj s).toMonoidHom < K
  intersection_normalizes : H ⊓ D.maximalLocal ≤
    normalizer (L.map (MulAut.conj s).toMonoidHom : Set G)
  ranks : ∀ p : ℕ, p.Prime → Odd p → p ∣ Nat.card (L ⧸ pCore 2 L) → primeRank p K ≤ 1

/-- Select either strict containment, transporting ranks along H's actual inclusion. -/
theorem ContainingPair.exists_rankedEnlargement
    {H : Subgroup G} {t : G} {K₁ K₂ : Subgroup H}
    (C : ContainingPair D H t K₁ K₂)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) (hne : K₁ ≠ K₂) :
    ∃ (s : G) (K : Subgroup G), RankedEnlargement D H s K := by
  have hmap (I : Subgroup H) : (I.map H.subtype).subgroupOf H = I :=
    comap_map_eq_self_of_injective H.subtype_injective I
  rcases C.strict with hs | hs
  · refine ⟨1,K₁.map H.subtype,C.maximal,C.half_le,C.sylow,
      ⟨map_subtype_le K₁,(hmap K₁).symm ▸ C.first_component⟩,
      (hmap K₁).symm ▸ C.first_normal,one_mem _,?_,?_,?_⟩
    · have hh := (map_lt_map_iff_of_injective H.subtype_injective).mpr hs
      rw [map_subgroupOf_eq_of_le C.left_le] at hh
      have he : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
        ext x
        simp
      simpa only [he, Subgroup.map_id] using hh
    · simpa using C.intersection_normalizes_left hn hne
    · intro p hp ho hd
      let : Fact p.Prime := ⟨hp⟩
      exact (primeRank_congr p (K₁.equivMapOfInjective H.subtype H.subtype_injective)).symm.trans_le
        (C.odd_ranks hn hne ho hd).1.le
  · refine ⟨t,K₂.map H.subtype,C.maximal,C.half_le,C.sylow,
      ⟨map_subtype_le K₂,(hmap K₂).symm ▸ C.second_component⟩,
      (hmap K₂).symm ▸ C.second_normal,C.t_mem,?_,C.intersection_normalizes_right hn hne,?_⟩
    · have hh := (map_lt_map_iff_of_injective H.subtype_injective).mpr hs
      rwa [map_subgroupOf_eq_of_le C.right_le] at hh
    · intro p hp ho hd
      let : Fact p.Prime := ⟨hp⟩
      exact (primeRank_congr p (K₂.equivMapOfInjective H.subtype H.subtype_injective)).symm.trans_le
        (C.odd_ranks hn hne ho hd).2.le

namespace RankedEnlargement
variable {H K : Subgroup G} {s : G} (E : RankedEnlargement D H s K)
include E

/-- The strict component cannot be contained in the original maximal local. -/
theorem outside : ¬ K ≤ D.maximalLocal :=
  source_strict_conjugate_component_outside D E.s_mem E.component E.strict

/-- The original radical gives C.2.3 in H, retaining both literal subgroups. -/
theorem pushingSetup : RadicalExclusions.PushingUpSetup KnownSimple.IsKnownSimple H
    ((localJoin T L).pCoreIn 2) (H ⊓ D.maximalLocal) :=
  pushingSetup_of_halfJoin_le D (D.simpleQTKE.twoLocal_sqtk E.maximal.1) E.half_le

/-- Relative normality supplies exactly the R-normalization required by C.2.7. -/
theorem radical_normalizes : (localJoin T L).pCoreIn 2 ≤ normalizer (K : Set G) :=
  ((join_core_le_stabilizer D).trans (le_sup_right.trans E.half_le)).trans
    ((normal_subgroupOf_iff_le_normalizer E.component.1).mp E.normal)

/-- With its intrinsic quasisimple quotient, the constrained branch has
every field of the original C.2.7 input. -/
theorem c27_input_of_quasisimple (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hf : generalizedFitting K = pCore 2 K) :
    RadicalExclusions.ModelReduction.FullSieve.SourceInterface.Input
      KnownSimple.IsKnownSimple H ((localJoin T L).pCoreIn 2) (H ⊓ D.maximalLocal) K :=
  ⟨E.pushingSetup,E.component,hq,hf,fun h => E.outside (h.trans inf_le_right),
    E.radical_normalizes⟩

/-- C.2.6 and the actual intersection stabilizer force the intrinsic quotient
to be quasisimple in the constrained branch. -/
theorem quotient_quasisimple (hf : generalizedFitting K = pCore 2 K) :
    IsQuasisimple (K ⧸ pCore 2 K) := by
  classical
  by_contra hnq
  have hF := ChapterC.Section02Source.fittingCore_le_of_nonquasisimple_component_setup
    E.pushingSetup E.component hf
    ((normal_subgroupOf_iff_le_normalizer E.component.1).mp E.normal) hnq
  let B := L.map (MulAut.conj s).toMonoidHom
  let B₀ := B.subgroupOf K
  let e : L ≃* B₀ := ((MulAut.conj s).subgroupMap L).trans
    (subgroupOfEquivOfLe E.strict.le).symm
  have htop : (⊤ : Subgroup K).IsCComponent := by
    simpa only [subgroupOf_self] using E.component.2.subgroupOf_of_le le_rfl E.component.1
  have hB : IsQuasisimple (B₀ ⧸ pCore 2 B₀) := by
    let := D.quasisimple
    exact IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e))
  have hFn : twoFittingCore K ≤ normalizer (B₀ : Set K) := by
    rw [←subgroupOf_normalizer_eq E.strict.le]
    intro x hx
    exact E.intersection_normalizes (hF (mem_map_of_mem K.subtype hx))
  exact hnq (quasisimple_quotient_of_fitting_normalizes htop B₀ hB hFn)

/-- Every C.2.7 hypothesis is discharged in the constrained branch, including
the intrinsic quotient hypothesis; only its stated Fitting case is assumed. -/
theorem c27_input (hf : generalizedFitting K = pCore 2 K) :
    RadicalExclusions.ModelReduction.FullSieve.SourceInterface.Input
      KnownSimple.IsKnownSimple H ((localJoin T L).pCoreIn 2) (H ⊓ D.maximalLocal) K :=
  E.c27_input_of_quasisimple (E.quotient_quasisimple hf) hf

/-- The local condition of the selected original factor uses the full Sylow
intersection inside K, not an arbitrary two-subgroup of K. -/
theorem local_sylow :
    ∃ S : Sylow 2 K,
      (S : Subgroup K) = ((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf K ∧
      (L.map (MulAut.conj s).toMonoidHom).subgroupOf K ∈ localCComponents S := by
  let B := L.map (MulAut.conj s).toMonoidHom
  let R := (T : Subgroup G) ⊓ normalizer (L : Set G)
  have hB : B ∈ Chapter1.L G (T : Subgroup G) := by
    have hh := (Chapter1.mem_L_map_iff (MulAut.conj s).toMonoidHom
      (MulAut.conj s).injective).mpr D.maximal.1
    have he : (T : Subgroup G).map (MulAut.conj s).toMonoidHom = T :=
      mem_normalizer_iff_map_conj_eq.mp ((T : Subgroup G).le_normalizer E.s_mem)
    rwa [he] at hh
  obtain ⟨S,hS⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
    E.sylow E.component.1 E.component.2.subnormal
  have he : (S : Subgroup K) = R.subgroupOf K := by
    apply map_injective K.subtype_injective
    rw [hS,subgroupOf_map_subtype]
  refine ⟨S,he,?_⟩
  rw [he]
  exact SourceEmbeddings.local_restrict
    (localCComponents_antitone inf_le_left hB.1) E.strict.le

/-- Binary rank-one quotients admit no strict enlargement of this local factor.
The Sylow premise comes from the containing pair, independently of 10.2.5. -/
theorem not_binary_rank_one {F : Type*} [Field F] [Finite F] [CharP F 2]
    (d : (K ⧸ pCore 2 K) ≃* SL(2,F)) : False := by
  obtain ⟨S,_,hlocal⟩ := E.local_sylow
  let B := (L.map (MulAut.conj s).toMonoidHom).subgroupOf K
  have htop : (⊤ : Subgroup K).IsCComponent := by
    simpa only [subgroupOf_self] using E.component.2.subgroupOf_of_le le_rfl E.component.1
  let P := B ⊔ (S : Subgroup K)
  have hp : ¬ Group.IsSolvable P := by
    intro hs
    let := hs
    exact hlocal.not_isSolvable inferInstance
  have heP : P = ⊤ := by
    by_contra hne
    exact hp (isSolvable_proper_sylow_overgroup_of_twoCore_quotient
      (isSolvable_proper_sylow_overgroup_of_equiv d
        Matrix.SpecialLinearGroup.isSolvable_of_proper_sylow_overgroup)
      S P le_sup_right hne)
  have hBc : B.IsCComponent := by
    change (B.subgroupOf P).IsCComponent at hlocal
    rw [heP] at hlocal
    simpa only [map_subgroupOf_eq_of_le le_top] using
      hlocal.map_subtype (show (⊤ : Subgroup K).IsSubnormal from .top)
  have heB := hBc.eq_of_le htop le_top
  exact E.strict.ne (le_antisymm E.strict.le (subgroupOf_eq_top.mp heB))

end RankedEnlargement
end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
