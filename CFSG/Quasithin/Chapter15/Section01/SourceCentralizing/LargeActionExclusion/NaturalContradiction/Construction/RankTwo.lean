module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalContradiction.Construction.LocalGeometry.EndOrbit
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalContradiction.Characteristic
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.FirstPair
public import Theory.SpecificGroups.BinaryLinear.CubicSylowGeneration
public import Theory.GroupTheory.SylowIndexThreeQuotient
public import Theory.GroupTheory.PResidual.PCoreQuotient
public import Theory.GroupTheory.GeneralizedFitting.PrimeCoreNormalized

/-!
# The actual rank-two group and its parabolic radical

For the original flag, K=⟨Y₀,Y₂⟩ is the two-residual of KS. The natural
action and the first-pair Levi calculation give KS/O₂(KS) ≅ SL₃(2).
Perfection makes K cover that quotient. Since O₂(KS) lies in O₂(P₂),
this proves KQ₂=KS and the actual quotient K/O₂(K) ≅ SL₃(2).

The common Sylow has index 21 in KS and index three in P₂, so P₂ has
index seven. Its own core quotient is S₃. These orders prove that Q₂
is different from O₂(KQ₂). Relative normality, C-component status,
characteristic two, SQTK, and the literal product are also established.

The final adapter constructs ten of the twelve NaturalRankTwoInput
clauses. The omega-center core identity and the nonblock assertion remain
explicit; they require the original centralizer marking and the two distinct
noncentral chief layers. This module does not complete source 15.1.29.
Source: Aschbacher--Smith, printed pp.1103--1104 of `refs/quasithin.pdf`.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
open BinaryLinear.SmallParabolicLevi

private theorem relIndex_subtype {G : Type*} [Group G] {H : Subgroup G}
    (K : Subgroup H) : (K.map H.subtype).relIndex H = K.index := by
  rw [relIndex,subgroupOf,comap_map_eq_self_of_injective H.subtype_injective]

namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData.NaturalFlag
open CFSG.Quasithin.ChapterA.Section05To06
open CFSG.Quasithin.Chapter15.Section03
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}
variable {d : CaseIComponentData T M Mc V} {t : G}

theorem pair_le (a : NaturalFlag d t) : a.parabolics.K ≤ d.L ⊔ d.S :=
  sup_le ((map_subtype_le _).trans a.parabolics_le.1)
    ((map_subtype_le _).trans a.parabolics_le.2.1)

theorem sylow_normalizes_pair (a : NaturalFlag d t) :
    d.S ≤ normalizer (a.parabolics.K : Set G) := by
  apply le_trans _ (normalizer_inf_normalizer_le_normalizer_sup _ _)
  exact le_inf
    ((a.sylow_le.1.trans a.parabolics.P0.le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image _ (pResidual 2 a.parabolics.P0)))
    ((a.sylow_le.2.1.trans a.parabolics.P2.le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image _ (pResidual 2 a.parabolics.P2)))

theorem second_core_le_sylow (a : NaturalFlag d t) (s : d.ExchangedSource) :
    a.parabolics.Q2 ≤ d.S := by
  obtain ⟨P,hP⟩ := a.node_sylow s ⟨1,by have := a.dimension; omega⟩
  exact (pCoreIn_le_sylow _ P).trans_eq hP

theorem pair_sylow_eq_nodes (a : NaturalFlag d t) (s : d.ExchangedSource) :
    a.parabolics.K ⊔ d.S = a.parabolics.P0 ⊔ a.parabolics.P2 := by
  change a.parabolics.K ⊔ d.S = a.node ⟨0,by have := a.dimension; omega⟩ ⊔
    a.node ⟨1,by have := a.dimension; omega⟩
  rw [a.node_supplement s ⟨0,by have := a.dimension; omega⟩,
    a.node_supplement s ⟨1,by have := a.dimension; omega⟩]
  change (a.parabolics.Y0 ⊔ a.parabolics.Y2) ⊔ d.S =
    (a.parabolics.Y0 ⊔ d.S) ⊔ (a.parabolics.Y2 ⊔ d.S)
  ac_rfl

/-- The actual natural-action quotient of KS is SL₃(2). -/
theorem pair_sylow_model (a : NaturalFlag d t) (s : d.ExchangedSource) :
    Nonempty (((a.parabolics.K ⊔ d.S : Subgroup G) ⧸
      pCore 2 (a.parabolics.K ⊔ d.S : Subgroup G)) ≃*
        Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  let J := a.parabolics.K ⊔ d.S
  have hJ : J ≤ d.L ⊔ d.S := sup_le a.pair_le le_sup_right
  let f := a.action.comp (inclusion hJ)
  have hf : f.range = minimalParabolic a.basis ⟨0,by have := a.dimension; omega⟩ ⊔
      minimalParabolic a.basis ⟨1,by have := a.dimension; omega⟩ := by
    have he : f.range = (J.subgroupOf (d.L ⊔ d.S)).map a.action := by
      ext g
      constructor
      · rintro ⟨x,rfl⟩
        exact mem_map_of_mem a.action x.property
      · rintro ⟨x,hx,rfl⟩
        exact ⟨⟨x,hx⟩,rfl⟩
    rw [he,show J = a.parabolics.K ⊔ d.S from rfl,a.pair_sylow_eq_nodes s,subgroupOf_sup a.parabolics_le.1 a.parabolics_le.2.1,
      Subgroup.map_sup]
    exact congrArg₂ (· ⊔ ·) (a.node_image _) (a.node_image _)
  obtain ⟨P,hP⟩ := s.centralizer_sylow.restrict
    (show d.S ≤ d.L ⊔ d.S from le_sup_right)
    (sup_le d.L_component.1 d.S_le_G1)
  have hB : (P.mapSurjective a.surjective : Subgroup (LinearGroup (a.m + 1))) =
      cutStabilizer a.basis Set.univ := by
    change (P : Subgroup _).map a.action = _
    have hPS : (P : Subgroup _) = d.S.subgroupOf (d.L ⊔ d.S) := by
      apply map_injective (d.L ⊔ d.S).subtype_injective
      rw [hP,map_subgroupOf_eq_of_le le_sup_right]
    rw [hPS]
    exact a.sylow
  rw [SylowFlagOvergroups.pair_eq_cutStabilizer _ a.basis hB] at hf
  have hk : IsPGroup 2 a.action.ker := by
    rw [show a.action.ker = pCore 2 (d.L ⊔ d.S : Subgroup G) from a.kernel]
    exact pCore_isPGroup
  have hkf : IsPGroup 2 f.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hk.comap_of_injective (inclusion hJ) (inclusion_injective hJ)
  let : Finite f.range := Finite.of_surjective _ f.rangeRestrict_surjective
  let e := f.rangeRestrict.pCoreQuotientEquiv f.rangeRestrict_surjective hkf
  obtain ⟨em⟩ := BinaryLinear.OrderedResidualConjugators.head_quotient a.dimension a.basis
  exact ⟨e.trans ((QuotientGroup.congr _ _ (MulEquiv.subgroupCongr hf)
    (pCore_map_iso 2 _)).trans em)⟩

theorem pair_radical_product (a : NaturalFlag d t) (s : d.ExchangedSource) :
    ∀ g ∈ a.parabolics.K ⊔ a.parabolics.Q2, ∃ k ∈ a.parabolics.K,
      ∃ r ∈ a.parabolics.Q2, k * r = g := by
  let J := a.parabolics.K ⊔ a.parabolics.Q2
  have hn : J ≤ normalizer (a.parabolics.K : Set G) :=
    sup_le a.parabolics.K.le_normalizer
      ((a.second_core_le_sylow s).trans a.sylow_normalizes_pair)
  let : (a.parabolics.K.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer hn
  have he : a.parabolics.K.subgroupOf J ⊔ a.parabolics.Q2.subgroupOf J = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le le_sup_left,
      map_subgroupOf_eq_of_le le_sup_right,←MonoidHom.range_eq_map,range_subtype]
  intro g hg
  obtain ⟨k,hk,r,hr,hkr⟩ := mem_sup_of_normal_left.mp
    (show (⟨g,hg⟩ : J) ∈ a.parabolics.K.subgroupOf J ⊔ a.parabolics.Q2.subgroupOf J by
      rw [he]; trivial)
  exact ⟨k.val,hk,r.val,hr,congrArg Subtype.val hkr⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData.NaturalFlag


private theorem perfect_twoPerfect {A : Type*} [Group A] [Finite A]
    [Group.IsPerfect A] : IsPPerfect 2 A := by
  intro N hN hq
  let : N.Normal := hN
  by_contra hne
  let : Nontrivial (A ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  let : Group.IsPerfect (A ⧸ N) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  let : Group.IsNilpotent (A ⧸ N) := hq.isNilpotent
  exact Group.IsPerfect.not_isSolvable (A ⧸ N) inferInstance

namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData.NaturalFlag
open CFSG.Quasithin.ChapterA.Section05To06
open CFSG.Quasithin.Chapter15.Section03
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}
variable {d : CaseIComponentData T M Mc V} {t : G}

/-- The two generating residuals give precisely O²(KS). -/
theorem pair_eq_residual (a : NaturalFlag d t) :
    (pResidual 2 (a.parabolics.K ⊔ d.S : Subgroup G)).map
      (a.parabolics.K ⊔ d.S).subtype = a.parabolics.K := by
  let := a.pair_perfect
  exact embedded_pResidual_join_pGroup _ _ perfect_twoPerfect
    (T.isPGroup'.to_le d.S_le_T) a.sylow_normalizes_pair

theorem pair_covers_quotient (a : NaturalFlag d t) (s : d.ExchangedSource) :
    a.parabolics.K ⊔ (a.parabolics.K ⊔ d.S).pCoreIn 2 = a.parabolics.K ⊔ d.S := by
  let J := a.parabolics.K ⊔ d.S
  obtain ⟨e⟩ := a.pair_sylow_model s
  let := Atlas.sl_perfect 3 (by decide) (F := ZMod 2)
  let : Group.IsPerfect (J ⧸ pCore 2 J) := Group.IsPerfect.ofSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  have he := map_pResidual_of_surjective 2 (QuotientGroup.mk' (pCore 2 J))
    (QuotientGroup.mk'_surjective _)
  rw [(pResidual_eq_top_iff 2 (J ⧸ pCore 2 J)).mpr perfect_twoPerfect] at he
  have hc := congrArg (comap (QuotientGroup.mk' (pCore 2 J))) he
  rw [comap_map_eq,QuotientGroup.ker_mk',comap_top] at hc
  have hh := congrArg (map J.subtype) hc
  rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] at hh
  exact (congrArg (· ⊔ J.pCoreIn 2) a.pair_eq_residual).symm.trans hh

theorem pair_sylow_sylow (a : NaturalFlag d t) (s : d.ExchangedSource) :
    Chapter1.IsSylowIn 2 d.S (a.parabolics.K ⊔ d.S) :=
  s.centralizer_sylow.restrict le_sup_right
    ((sup_le a.pair_le le_sup_right).trans (sup_le d.L_component.1 d.S_le_G1))

theorem pair_core_le_second_core (a : NaturalFlag d t) (s : d.ExchangedSource) :
    (a.parabolics.K ⊔ d.S).pCoreIn 2 ≤ a.parabolics.Q2 := by
  let J := a.parabolics.K ⊔ d.S
  have hP : a.parabolics.P2 ≤ J := by
    rw [a.second_supplement s]
    exact sup_le (le_sup_right.trans le_sup_left) le_sup_right
  obtain ⟨P,hPmap⟩ := a.pair_sylow_sylow s
  have hcore : J.pCoreIn 2 ≤ d.S := (pCoreIn_le_sylow _ P).trans_eq hPmap
  exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 J)
    (hcore.trans a.sylow_le.2.1)
    ((hP.trans J.le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image J (pCore 2 J)))

/-- The original parabolic radical supplements K to the same KS. -/
theorem pair_radical_eq_sylow_join (a : NaturalFlag d t) (s : d.ExchangedSource) :
    a.parabolics.K ⊔ a.parabolics.Q2 = a.parabolics.K ⊔ d.S := by
  apply le_antisymm (sup_le_sup_left (a.second_core_le_sylow s) _)
  rw [←a.pair_covers_quotient s]
  exact sup_le_sup_left (a.pair_core_le_second_core s) _

/-- Removing the kernel on the literal K preserves its intrinsic core quotient. -/
theorem pair_quotient_model (a : NaturalFlag d t) (s : d.ExchangedSource) :
    Nonempty ((a.parabolics.K ⧸ pCore 2 a.parabolics.K) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  let J := a.parabolics.K ⊔ d.S
  obtain ⟨e⟩ := a.pair_sylow_model s
  let q := QuotientGroup.mk' (pCore 2 J)
  let f := q.comp (inclusion (show a.parabolics.K ≤ J from le_sup_left))
  have hf : Function.Surjective f := by
    have hgen : a.parabolics.K.subgroupOf J ⊔ pCore 2 J = ⊤ := by
      apply map_injective J.subtype_injective
      rw [Subgroup.map_sup,map_subgroupOf_eq_of_le le_sup_left,
        ←MonoidHom.range_eq_map,range_subtype]
      exact a.pair_covers_quotient s
    have he := congrArg (map q) hgen
    rw [Subgroup.map_sup,QuotientGroup.map_mk'_self,sup_bot_eq,
      map_top_of_surjective q (QuotientGroup.mk'_surjective _)] at he
    intro x
    obtain ⟨k,hk,hkx⟩ := (show x ∈ (a.parabolics.K.subgroupOf J).map q by rw [he]; trivial)
    exact ⟨⟨k,hk⟩,hkx⟩
  have hk : IsPGroup 2 f.ker := by
    have hq : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
    exact hq.comap_of_injective _ (inclusion_injective _)
  have hbot : pCore 2 (J ⧸ pCore 2 J) = ⊥ := pCore_quotient_pCore_eq_bot 2
  exact ⟨(f.pCoreQuotientEquiv hf hk).trans
    (((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot).trans e)⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData.NaturalFlag

namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData.NaturalFlag
open CFSG.Quasithin.ChapterA.Section05To06
open CFSG.Quasithin.Chapter15.Section03
open Theory.SpecificGroups.BinaryComponentResidual
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}
variable {d : CaseIComponentData T M Mc V} {t : G}

theorem pair_radical_sylow (a : NaturalFlag d t) (s : d.ExchangedSource) :
    Chapter1.IsSylowIn 2 d.S (a.parabolics.K ⊔ a.parabolics.Q2) := by
  rw [a.pair_radical_eq_sylow_join s]
  exact a.pair_sylow_sylow s

theorem pair_radical_sqtk (a : NaturalFlag d t)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : PreparedChosenModule T M V) (s : d.ExchangedSource) :
    IsSQTK KnownSimple.IsKnownSimple (a.parabolics.K ⊔ a.parabolics.Q2 : Subgroup G) := by
  let := h.elementary
  have hsq := caseI_centralizer_sqtk hG d.Z1 d.Z1_ne_bot
    ((IsElementaryAbelian.isPGroup 2 V).to_le (d.Z1_le_fixed.trans inf_le_left))
  have hle : a.parabolics.K ⊔ a.parabolics.Q2 ≤ d.G1 := by
    rw [a.pair_radical_eq_sylow_join s]
    exact (sup_le a.pair_le le_sup_right).trans (sup_le d.L_component.1 d.S_le_G1)
  exact (IsSQTK.equiv (subgroupOfEquivOfLe hle)).mp (hsq.subgroup _)

/-- Characteristic two passes from L to LS and then to its Sylow overgroup. -/
theorem pair_radical_fitting (a : NaturalFlag d t)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : PreparedChosenModule T M V) (hs : d.HasExchangedLinearSource) :
    generalizedFitting (a.parabolics.K ⊔ a.parabolics.Q2 : Subgroup G) =
      pCore 2 (a.parabolics.K ⊔ a.parabolics.Q2 : Subgroup G) := by
  rw [a.pair_radical_eq_sylow_join hs.1]
  let := hs.1.quasisimple
  have hLc := (d.source_cubic_component hG h (by
    obtain ⟨n,hn,⟨e⟩⟩ := hs.2.2
    exact facts_of_small_binary_model (small_binary_model_of_marking hn e))).1
  have hn : d.S ≤ normalizer (d.L : Set G) := by
    rw [hLc]
    exact (d.S_le_G1.trans d.G1.le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image _ (primeToResidual 3 d.G1))
  have hc : centralizer (pCore 2 d.L : Set d.L) ≤ pCore 2 d.L := by
    rw [←hs.2.1]
    exact centralizer_generalizedFitting_le _
  have hLS := centralizer_pCore_sup_le 2 d.L d.S hc (T.isPGroup'.to_le d.S_le_T) hn
  let J := a.parabolics.K ⊔ d.S
  have hJ : J ≤ d.L ⊔ d.S := sup_le a.pair_le le_sup_right
  obtain ⟨P,hP⟩ := hs.1.centralizer_sylow.restrict
    (show d.S ≤ d.L ⊔ d.S from le_sup_right)
    (sup_le d.L_component.1 d.S_le_G1)
  have hcore : pCore 2 (d.L ⊔ d.S : Subgroup G) ≤ J.subgroupOf (d.L ⊔ d.S) := by
    intro x hx
    exact mem_sup_right (hP.le (mem_map_of_mem (d.L ⊔ d.S).subtype
      (pCore_isPGroup.le_sylow_of_normal P hx)))
  have hself := centralizer_pCore_le_of_pCore_le (J.subgroupOf (d.L ⊔ d.S)) hLS hcore
  exact generalizedFitting_eq_pCore_of_selfCentralizing 2
    ((Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hJ)).mp hself)

/-- The literal K is a C-component relative to KQ₂. -/
theorem pair_radical_component (a : NaturalFlag d t) (s : d.ExchangedSource) :
    (a.parabolics.K.subgroupOf (a.parabolics.K ⊔ a.parabolics.Q2)).IsCComponent := by
  let J := a.parabolics.K ⊔ a.parabolics.Q2
  have hn : J ≤ normalizer (a.parabolics.K : Set G) :=
    sup_le a.parabolics.K.le_normalizer
      ((a.second_core_le_sylow s).trans a.sylow_normalizes_pair)
  let : (a.parabolics.K.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer hn
  let := a.pair_perfect
  let eK := subgroupOfEquivOfLe (show a.parabolics.K ≤ J from le_sup_left)
  let : Group.IsPerfect (a.parabolics.K.subgroupOf J) :=
    Group.IsPerfect.ofSurjective (f := eK.symm.toMonoidHom) eK.symm.surjective
  obtain ⟨e⟩ := a.pair_quotient_model s
  let : IsQuasisimple (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := {
    toIsPerfect := Atlas.sl_perfect 3 (by decide)
    simple := Atlas.psl_simple_high_rank 3 (by decide) }
  let eQ := QuotientGroup.congr _ _ eK (pCore_map_iso 2 eK)
  let : IsQuasisimple ((a.parabolics.K.subgroupOf J) ⧸
      pCore 2 (a.parabolics.K.subgroupOf J)) := IsQuasisimple.of_mulEquiv (eQ.trans e).symm
  exact isCComponent_of_isPPerfect_of_quasisimple_core_quotient
    (inferInstance : (a.parabolics.K.subgroupOf J).Normal).isSubnormal
    (p := 2) perfect_twoPerfect

theorem second_lt_pair_radical (a : NaturalFlag d t) (s : d.ExchangedSource) :
    a.parabolics.P2 < a.parabolics.K ⊔ a.parabolics.Q2 := by
  rw [a.pair_radical_eq_sylow_join s,a.pair_sylow_eq_nodes s]
  apply lt_iff_le_not_ge.mpr ⟨le_sup_right,?_⟩
  intro hle
  have h02 : a.parabolics.P0 ≤ a.parabolics.P2 := le_sup_left.trans hle
  have hc := a.node_cover s ⟨1,by have := a.dimension; omega⟩
  have he := (covBy_iff_lt_and_eq_or_eq.mp hc).2 _ a.sylow_le.1 h02
  rcases he with he | he
  · exact (a.node_cover s ⟨0,by have := a.dimension; omega⟩).ne he.symm
  · have hi := a.node_injective he
    have hi' := congrArg Fin.val hi
    simp at hi'

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData.NaturalFlag



namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData.NaturalFlag
open CFSG.Quasithin.Chapter15.Section03
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}
variable {d : CaseIComponentData T M Mc V} {t : G}

theorem node_index (a : NaturalFlag d t) (s : d.ExchangedSource) (i : Fin a.m) :
    d.S.relIndex (a.node i) = 3 := by
  let H := d.L ⊔ d.S
  have hker : a.action.ker ≤ d.S.subgroupOf H := by
    intro x hx
    apply (a.mem_sylow_iff s x).mpr
    rw [MonoidHom.mem_ker.mp hx]
    exact one_mem _
  calc
    d.S.relIndex (a.node i) = (d.S.subgroupOf H).relIndex ((a.node i).subgroupOf H) := by
      rw [←relIndex_map_map_of_injective _ _ H.subtype_injective,
        map_subgroupOf_eq_of_le (show d.S ≤ H from le_sup_right),map_subgroupOf_eq_of_le (a.node_le i)]
    _ = ((d.S.subgroupOf H).map a.action).relIndex
        (((a.node i).subgroupOf H).map a.action) := by
      rw [relIndex_map_map,sup_of_le_left hker,
        sup_of_le_left (hker.trans (subgroupOf_mono H (a.sylow_le_node i)))]
    _ = 3 := by
      have hs : (d.S.subgroupOf H).map a.action = cutStabilizer a.basis Set.univ := a.sylow
      rw [hs,a.node_image]
      exact CubicSylowGeneration.minimalParabolic_index a.basis i

theorem sylow_normalizer (a : NaturalFlag d t) (s : d.ExchangedSource) :
    (d.L ⊔ d.S) ⊓ normalizer (d.S : Set G) = d.S := by
  apply le_antisymm _ (le_inf le_sup_right d.S.le_normalizer)
  rintro x ⟨hx,hxn⟩
  let g : (d.L ⊔ d.S : Subgroup G) := ⟨x,hx⟩
  have hg : g ∈ normalizer (d.S.subgroupOf (d.L ⊔ d.S) : Set (d.L ⊔ d.S : Subgroup G)) := by
    rw [←subgroupOf_normalizer_eq (show d.S ≤ d.L ⊔ d.S from le_sup_right)]
    exact hxn
  have hm := (d.S.subgroupOf (d.L ⊔ d.S)).le_normalizer_map a.action (mem_map_of_mem _ hg)
  have hs : (d.S.subgroupOf (d.L ⊔ d.S)).map a.action = cutStabilizer a.basis Set.univ := a.sylow
  rw [hs,SylowFlagOvergroups.normalizer_fullFlag_eq] at hm
  exact (a.mem_sylow_iff s g).mpr hm

/-- Each actual minimal parabolic has core quotient S₃. -/
theorem node_quotient_model (a : NaturalFlag d t) (s : d.ExchangedSource) (i : Fin a.m) :
    Nonempty ((a.node i ⧸ pCore 2 (a.node i)) ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨P,hP⟩ := a.node_sylow s i
  have hi : (P : Subgroup (a.node i)).index = 3 := by
    rw [←relIndex_subtype (P : Subgroup (a.node i)), hP]
    exact a.node_index s i
  apply sylow_index_three_core_quotient P hi
  apply lt_of_le_of_ne (pCore_isPGroup.le_sylow_of_normal P)
  intro he
  have hS : (P : Subgroup (a.node i)) = d.S.subgroupOf (a.node i) := by
    apply map_injective (a.node i).subtype_injective
    rw [hP,map_subgroupOf_eq_of_le (a.sylow_le_node i)]
  have hn : (d.S.subgroupOf (a.node i)).Normal := by
    rw [←hS,←he]
    infer_instance
  have hle : a.node i ≤ d.S := by
    rw [←a.sylow_normalizer s]
    exact le_inf (a.node_le i)
      ((normal_subgroupOf_iff_le_normalizer (a.sylow_le_node i)).mp hn)
  exact (a.node_cover s i).lt.not_ge hle

theorem pair_sylow_index (a : NaturalFlag d t) (s : d.ExchangedSource) :
    d.S.relIndex (a.parabolics.K ⊔ d.S) = 21 := by
  let J := a.parabolics.K ⊔ d.S
  obtain ⟨e⟩ := a.pair_sylow_model s
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 J := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  obtain ⟨P,hP⟩ := a.pair_sylow_sylow s
  let B := P.mapSurjective hf
  have hb : Nat.card B = 8 := by
    rw [B.card_eq_multiplicity,Matrix.PSL3Two.card_SL]
    decide +kernel
  have hi : (B : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))).index = 21 := by
    have hc := (B : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))).card_mul_index
    rw [hb,Matrix.PSL3Two.card_SL] at hc
    omega
  have he : (B : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))).index = (P : Subgroup J).index :=
    (P : Subgroup J).index_map_eq hf (hk ▸ pCore_isPGroup.le_sylow_of_normal P)
  rw [←relIndex_subtype (P : Subgroup J),hP] at he
  exact he.symm.trans hi

/-- The common Sylow indices give the source index seven. -/
theorem second_index (a : NaturalFlag d t) (s : d.ExchangedSource) :
    (a.parabolics.P2.subgroupOf (a.parabolics.K ⊔ a.parabolics.Q2)).index = 7 := by
  rw [a.pair_radical_eq_sylow_join s]
  have hP : a.parabolics.P2 ≤ a.parabolics.K ⊔ d.S := by
    rw [a.pair_sylow_eq_nodes s]
    exact le_sup_right
  have hm := relIndex_mul_relIndex d.S a.parabolics.P2 (a.parabolics.K ⊔ d.S)
    a.sylow_le.2.1 hP
  rw [a.pair_sylow_index s,show d.S.relIndex a.parabolics.P2 = 3 from a.node_index s _] at hm
  change a.parabolics.P2.relIndex (a.parabolics.K ⊔ d.S) = 7
  omega

/-- The S₃ and SL₃(2) quotient orders prevent equality of the two cores. -/
theorem second_core_ne_pair_core (a : NaturalFlag d t) (s : d.ExchangedSource) :
    a.parabolics.Q2 ≠ (a.parabolics.K ⊔ a.parabolics.Q2).pCoreIn 2 := by
  intro he
  let J := a.parabolics.K ⊔ a.parabolics.Q2
  obtain ⟨eJ⟩ := a.pair_sylow_model s
  have hcJ : (pCore 2 J).index = 168 := by
    change Nat.card (J ⧸ pCore 2 J) = 168
    rw [show J = a.parabolics.K ⊔ d.S from a.pair_radical_eq_sylow_join s,
      Nat.card_congr eJ.toEquiv,Matrix.PSL3Two.card_SL]
  obtain ⟨eP⟩ := a.node_quotient_model s ⟨1,by have := a.dimension; omega⟩
  have hcP : (pCore 2 a.parabolics.P2).index = 6 := by
    change Nat.card (a.parabolics.P2 ⧸ pCore 2 a.parabolics.P2) = 6
    have hc := Nat.card_congr eP.toEquiv
    change Nat.card (a.parabolics.P2 ⧸ pCore 2 a.parabolics.P2) = Nat.card (Equiv.Perm (Fin 3)) at hc
    rw [hc,Nat.card_eq_fintype_card,Fintype.card_perm]
    decide
  have hP : a.parabolics.P2 ≤ J := (a.second_lt_pair_radical s).le
  have hm := relIndex_mul_relIndex a.parabolics.Q2 a.parabolics.P2 J
    (pCoreIn_le 2 _) hP
  have hiQ : a.parabolics.Q2.relIndex a.parabolics.P2 = 6 := by
    change ((pCore 2 a.parabolics.P2).map a.parabolics.P2.subtype).relIndex _ = _
    rw [relIndex_subtype]
    exact hcP
  have hiJ : a.parabolics.Q2.relIndex J = 168 := by
    rw [he]
    change ((pCore 2 J).map J.subtype).relIndex J = _
    rw [relIndex_subtype]
    exact hcJ
  rw [hiQ,hiJ,show a.parabolics.P2.relIndex J = 7 from a.second_index s] at hm
  omega
end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData.NaturalFlag

namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData.NaturalFlag
open CFSG.Quasithin.ChapterA.Section05To06
open CFSG.Quasithin.Chapter15.Section03
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}
variable {d : CaseIComponentData T M Mc V} {t : G}

/-- All remaining structural premises are discharged on the same flag;
only the marked omega-center and two-chief-layer arguments remain. -/
theorem rankTwoInput_of_centralizer_nonblock (a : NaturalFlag d t)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : PreparedChosenModule T M V) (hs : d.HasExchangedLinearSource)
    (hcentral : a.parabolics.Q2 =
      ((a.parabolics.K ⊔ a.parabolics.Q2) ⊓ centralizer
        (SourceInterface.omegaCenterIn d.S : Set G)).pCoreIn 2)
    (hblock : ¬ ChapterC.IsSL3EvenBlock a.parabolics.K 1) :
    NaturalRankTwoInput a.parabolics := {
  sqtk := a.pair_radical_sqtk hG h hs.1
  fitting := a.pair_radical_fitting hG h hs
  product := a.pair_radical_product hs.1
  component := a.pair_radical_component hs.1
  parabolic_proper := a.second_lt_pair_radical hs.1
  parabolic_index := a.second_index hs.1
  model := a.pair_quotient_model hs.1
  sylow := a.pair_radical_sylow hs.1
  core_le_sylow := a.second_core_le_sylow hs.1
  centralizer_core := hcentral
  radical_not_core := a.second_core_ne_pair_core hs.1
  not_linear_block := hblock }
end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData.NaturalFlag
