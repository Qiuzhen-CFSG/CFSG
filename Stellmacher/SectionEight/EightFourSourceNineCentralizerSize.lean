module
public import Stellmacher.SectionEight.EightFourSourceNineSmallRank
public import Theory.GroupTheory.SpecificGroups.KleinFourAut

/-!
# The large centralizer in the last case of Stellmacher (8.4)

A two-group normalizing an elementary subgroup of order four has centralizer
index at most two, since its conjugation image lies in the automorphism group
of order six. Apply this to the actual selected edge-fixed subgroup and the
shifted center/core intersection. The proved rank and actor index give orders
four and eight respectively, so the selected centralizer has at least four
elements. The earlier final-case reduction puts it in both endpoint centers.

The local theorems retain the exact graph, selected seed and source-nine data.
The generic four-group action lemma is unchanged; original canonical theorem
statements are wrappers through the local context and configuration adapters.

Source: Stellmacher, Journal of Algebra 190 (1997), printed p.40, (8.4).
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

/-- The two-group action on an elementary four has image of order at most two. -/
public theorem two_group_normalizing_four_centralizer_index_le_two
    {H : Type u} [Group H] [Finite H] (K D : Subgroup H)
    (helementary : IsElementaryAbelian 2 K) (hfour : Nat.card K = 4)
    (htwo : IsPGroup 2 D) (hnorm : D ≤ Subgroup.normalizer (K : Set H)) :
    (Subgroup.centralizer (K : Set H)).relIndex D ≤ 2 := by
  let _ := helementary
  let _ : Nontrivial K := not_subsingleton_iff_nontrivial.mp (by
    intro hsubsingleton
    have hone : Nat.card K = 1 := Nat.card_eq_one_iff_unique.mpr
      ⟨hsubsingleton, inferInstance⟩
    omega)
  let _ : IsKleinFour K := ⟨hfour, IsElementaryAbelian.exponent_eq_prime⟩
  let action : D →* MulAut K := K.normalizerMonoidHom.comp (Subgroup.inclusion hnorm)
  have hker : action.ker = (Subgroup.centralizer (K : Set H)).subgroupOf D := by
    change K.normalizerMonoidHom.ker.comap (Subgroup.inclusion hnorm) = _
    rw [Subgroup.normalizerMonoidHom_ker]
    rfl
  have hindex : (Subgroup.centralizer (K : Set H)).relIndex D = Nat.card action.range := by
    change ((Subgroup.centralizer (K : Set H)).subgroupOf D).index = _
    rw [← hker, Subgroup.index_ker]
  have hdiv : Nat.card action.range ∣ 6 := by
    rw [← IsKleinFour.card_mulAut K]
    exact Subgroup.card_subgroup_dvd_card _
  obtain ⟨exponent, hcard⟩ :=
    (htwo.of_surjective action.rangeRestrict action.rangeRestrict_surjective).exists_card_eq
  have hle : 2 ^ exponent ≤ 6 := hcard ▸ Nat.le_of_dvd (by decide) hdiv
  have hexponent : exponent ≤ 2 := by
    by_contra hlarge
    have hpow := Nat.pow_le_pow_right (show 1 ≤ 2 by decide) (show 3 ≤ exponent by omega)
    norm_num at hpow
    omega
  rw [hindex]
  rw [hcard] at hdiv ⊢
  interval_cases exponent <;> norm_num at *

section LocalProof

variable {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (hbranch : (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≠ w.oneJFixedPoints S)
    (F : ctx.Γ.Vertex → ctx.Γ.Vertex → Subgroup H)
    (hbase : F ctx.criticalPath.a ctx.criticalPath.firstStep = w.oneJFixedPoints S)
    (hcov : ∀ g d l, F (ctx.Γ.act g d) (ctx.Γ.act g l) = (F d l).conjBy g⁻¹)
    (hsub : ∀ d l, F d l ≤ ZAt ctx.Γ d ⊓ GAt ctx.Γ l)
    (hformula : ∀ d l, F d l = ⨆ (g : H)
      (_ : ctx.Γ.act g ctx.criticalPath.a = d ∧
        ctx.Γ.act g ctx.criticalPath.firstStep = l),
      (w.oneJFixedPoints S).conjBy g⁻¹)
    (configuration : EightFourSourceNineLocalData ctx F)
    (hlen : 2 < ctx.criticalPath.length)

include hcenter w hbranch hbase hcov hsub hformula configuration hlen

/-- Every nonzero transported edge has center order sixteen and fixed subgroup order four. -/
public theorem eight_four_source_nine_edge_cardinalities_local
    (vertex neighbor : ctx.Γ.Vertex) (hnonzero : F vertex neighbor ≠ ⊥) :
    Nat.card (ZAt ctx.Γ vertex) = 16 ∧ Nat.card (F vertex neighbor) = 4 := by
  classical
  obtain ⟨actor, horient⟩ : ∃ actor : H,
      ctx.Γ.act actor ctx.criticalPath.a = vertex ∧
      ctx.Γ.act actor ctx.criticalPath.firstStep = neighbor := by
    by_contra hnone
    apply hnonzero
    rw [hformula vertex neighbor]
    apply le_bot_iff.mp
    exact iSup_le fun actor => iSup_le fun horient => (hnone ⟨actor, horient⟩).elim
  have hF := hcov actor ctx.criticalPath.a ctx.criticalPath.firstStep
  rw [horient.1, horient.2, hbase] at hF
  have hZ := z_act ctx.Γ actor ctx.criticalPath.a
  rw [horient.1] at hZ
  have hrank := eight_four_source_nine_small_rank_local ctx hcenter w hbranch
    F hbase hcov hsub hformula configuration hlen
  have hfour := eight_four_source_nine_fixed_card_four_local ctx hcenter w hbranch
    F hbase hcov hsub hformula configuration hlen
  constructor
  · change Nat.card (z ctx.Γ vertex) = 16
    rw [hZ, Subgroup.card_map_of_injective (MulAut.conj actor⁻¹).injective]
    exact hrank.1
  · rw [hF]
    exact (Subgroup.card_map_of_injective (MulAut.conj actor⁻¹).injective).trans hfour

/-- The actual shifted actor/core intersection has order eight. -/
public theorem eight_four_source_nine_actor_core_card_eight_local :
    let next := ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a'
    Nat.card ↥(ZAt ctx.Γ next ⊓ QAt ctx.Γ ctx.criticalPath.firstStep) = 8 := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let next := Γ.act configuration.y⁻¹ cp.a'
  let D := ZAt Γ next ⊓ QAt Γ cp.firstStep
  have hfour := eight_four_source_nine_shifted_fixed_card_four_local ctx hcenter w hbranch
    F hbase hcov hsub hformula configuration hlen
  have hnonzero : F next configuration.d ≠ ⊥ := by
    intro hzero
    change Nat.card (F next configuration.d) = 4 at hfour
    rw [hzero, Subgroup.card_bot] at hfour
    contradiction
  have hZcard := (eight_four_source_nine_edge_cardinalities_local ctx hcenter w hbranch
    F hbase hcov hsub hformula configuration hlen next configuration.d hnonzero).1
  have hindex : D.relIndex (ZAt Γ next) = 2 :=
    eight_four_source_nine_actor_index_local ctx hcenter w hbranch
      F hbase hcov hsub hformula configuration hlen
  have hprod := (D.subgroupOf (ZAt Γ next)).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (show D ≤ ZAt Γ next from inf_le_left)).toEquiv] at hprod
  change Nat.card D * D.relIndex (ZAt Γ next) = Nat.card (ZAt Γ next) at hprod
  rw [hindex, hZcard] at hprod
  change Nat.card D = 8
  omega

/-- The selected seed has a centralizer of at least four elements in the actor/core intersection. -/
public theorem eight_four_source_nine_seed_centralizer_card_ge_four_local
    (vertex : ctx.Γ.Vertex) (hadj : ctx.Γ.adjacent vertex ctx.criticalPath.firstStep)
    (hescape : ¬ F vertex ctx.criticalPath.firstStep ≤
      GAt ctx.Γ (ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a')) :
    4 ≤ Nat.card ↥((ZAt ctx.Γ (ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a') ⊓
      QAt ctx.Γ ctx.criticalPath.firstStep) ⊓
        Subgroup.centralizer (F vertex ctx.criticalPath.firstStep : Set H)) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let next := Γ.act configuration.y⁻¹ cp.a'
  let K := F vertex cp.firstStep
  let D := ZAt Γ next ⊓ QAt Γ cp.firstStep
  let U := D ⊓ Subgroup.centralizer (K : Set H)
  let h := ctx.sectionSeven
  have hnonzero : K ≠ ⊥ := by
    intro hzero
    apply hescape
    change K ≤ _
    rw [hzero]
    exact bot_le
  have hKcard : Nat.card K = 4 := (eight_four_source_nine_edge_cardinalities_local
    ctx hcenter w hbranch F hbase hcov hsub hformula configuration hlen
      vertex cp.firstStep hnonzero).2
  have hKZ : K ≤ ZAt Γ vertex := (hsub vertex cp.firstStep).trans inf_le_left
  let _ : IsElementaryAbelian 2 (ZAt Γ vertex) :=
    SevenSix.z_isElementaryAbelian_of_neighbor h Γ
      ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr hadj)
  have hKe : IsElementaryAbelian 2 K := by
    refine { toIsMulCommutative := { is_comm := ⟨?_⟩ }, exponent_dvd_p := ?_ }
    · intro first second
      apply Subtype.ext
      change (first : H) * (second : H) = (second : H) * (first : H)
      exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := ZAt Γ vertex)).comm
        ⟨first, hKZ first.property⟩ ⟨second, hKZ second.property⟩)
    · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      intro point
      apply Subtype.ext
      exact elemPow_eq_one_of_isElementaryAbelian (point : H) (hKZ point.property)
  let _ : IsElementaryAbelian 2 (ZAt Γ next) :=
    SevenSix.z_isElementaryAbelian_of_neighbor h Γ
      ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm configuration.hadj))
  have hDtwo : IsPGroup 2 D := (IsElementaryAbelian.isPGroup 2 (ZAt Γ next)).of_injective
    (Subgroup.inclusion (show D ≤ ZAt Γ next from inf_le_left))
    (Subgroup.inclusion_injective _)
  have hnorm : D ≤ Subgroup.normalizer (K : Set H) := inf_le_right.trans
    (eight_four_neighbor_core_normalizes_edge_fixed_local ctx
      F hcov vertex cp.firstStep hadj)
  have hindex : U.relIndex D ≤ 2 := by
    rw [show U = D ⊓ Subgroup.centralizer (K : Set H) from rfl,
      Subgroup.inf_relIndex_left]
    exact two_group_normalizing_four_centralizer_index_le_two K D hKe hKcard hDtwo hnorm
  have hDcard : Nat.card D = 8 := eight_four_source_nine_actor_core_card_eight_local
    ctx hcenter w hbranch F hbase hcov hsub hformula configuration hlen
  have hprod := (U.subgroupOf D).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (show U ≤ D from inf_le_left)).toEquiv] at hprod
  change Nat.card U * U.relIndex D = Nat.card D at hprod
  rw [hDcard] at hprod
  change 4 ≤ Nat.card U
  nlinarith

/-- The two endpoint centers meet in a subgroup of order at least four. -/
public theorem eight_four_source_nine_endpoint_intersection_card_ge_four_local :
    4 ≤ Nat.card ↥(ZAt ctx.Γ ctx.criticalPath.a' ⊓
      ZAt ctx.Γ (ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a')) := by
  obtain ⟨vertex, hadj, hescape⟩ := eight_four_source_nine_exists_escaping_neighbor_local
    ctx hcenter w hbranch F hbase hcov hsub hformula configuration hlen
  exact (eight_four_source_nine_seed_centralizer_card_ge_four_local
    ctx hcenter w hbranch F hbase hcov hsub hformula configuration hlen
      vertex hadj hescape).trans
    (Subgroup.card_le_of_le (eight_four_source_nine_seed_centralizer_le_intersection_local
      ctx hcenter w hbranch F hbase hcov hsub hformula configuration hlen vertex hescape))

end LocalProof

section CanonicalProof

variable {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (hbranch : (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≠ w.oneJFixedPoints S)
    (F : ctx.Γ.Vertex → ctx.Γ.Vertex → Subgroup H)
    (hbase : F ctx.criticalPath.a ctx.criticalPath.firstStep = w.oneJFixedPoints S)
    (hcov : ∀ g d l, F (ctx.Γ.act g d) (ctx.Γ.act g l) = (F d l).conjBy g⁻¹)
    (hsub : ∀ d l, F d l ≤ ZAt ctx.Γ d ⊓ GAt ctx.Γ l)
    (hformula : ∀ d l, F d l = ⨆ (g : H)
      (_ : ctx.Γ.act g ctx.criticalPath.a = d ∧
        ctx.Γ.act g ctx.criticalPath.firstStep = l),
      (w.oneJFixedPoints S).conjBy g⁻¹)
    (configuration : EightFourSourceNineData ctx F)
    (hlen : 2 < ctx.criticalPath.length)

include hcenter w hbranch hbase hcov hsub hformula configuration hlen

public theorem eight_four_source_nine_edge_cardinalities
    (vertex neighbor : ctx.Γ.Vertex) (hnonzero : F vertex neighbor ≠ ⊥) :
    Nat.card (ZAt ctx.Γ vertex) = 16 ∧ Nat.card (F vertex neighbor) = 4 := by
  exact eight_four_source_nine_edge_cardinalities_local ctx.toLocalContext hcenter w hbranch F hbase hcov hsub hformula configuration.toLocal hlen vertex neighbor hnonzero

public theorem eight_four_source_nine_actor_core_card_eight :
    let next := ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a'
    Nat.card ↥(ZAt ctx.Γ next ⊓ QAt ctx.Γ ctx.criticalPath.firstStep) = 8 := by
  exact eight_four_source_nine_actor_core_card_eight_local ctx.toLocalContext hcenter w hbranch F hbase hcov hsub hformula configuration.toLocal hlen

public theorem eight_four_source_nine_seed_centralizer_card_ge_four
    (vertex : ctx.Γ.Vertex) (hadj : ctx.Γ.adjacent vertex ctx.criticalPath.firstStep)
    (hescape : ¬ F vertex ctx.criticalPath.firstStep ≤
      GAt ctx.Γ (ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a')) :
    4 ≤ Nat.card ↥((ZAt ctx.Γ (ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a') ⊓
      QAt ctx.Γ ctx.criticalPath.firstStep) ⊓
        Subgroup.centralizer (F vertex ctx.criticalPath.firstStep : Set H)) := by
  exact eight_four_source_nine_seed_centralizer_card_ge_four_local ctx.toLocalContext hcenter w hbranch F hbase hcov hsub hformula configuration.toLocal hlen vertex hadj hescape

public theorem eight_four_source_nine_endpoint_intersection_card_ge_four :
    4 ≤ Nat.card ↥(ZAt ctx.Γ ctx.criticalPath.a' ⊓
      ZAt ctx.Γ (ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a')) := by
  exact eight_four_source_nine_endpoint_intersection_card_ge_four_local ctx.toLocalContext hcenter w hbranch F hbase hcov hsub hformula configuration.toLocal hlen

end CanonicalProof

end Stellmacher.SectionEight
