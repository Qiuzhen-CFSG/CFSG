module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.CenterOrder

/-!
# Odd five-edge fixers in the cubic A₅ branch

A two-subgroup fixing a nonbacktracking alpha turn lies in the alpha
core: the two edge Sylows have distinct images in A₅, and those images
intersect trivially. At a cubic beta turn the same assertion follows
from the full local permutation kernel and its normal Sylow two-subgroup.
For five consecutive edges, the two internal alpha cores intersect in
Iβ = Zβ. Intersecting with the adjacent beta core gives the source layer,
which has order dividing two and cannot have order two by the cubic path
actor. Thus every two-subgroup of the whole fixer is trivial. Cauchy's
theorem gives odd order for the literal six-vertex intersection.

Only consecutive backtracking is excluded, so the argument also applies
to source paths that close at their last vertex. No tree is assumed.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.6)(b) and (11.7)(f), printed pp.172--175.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile

private theorem a5_two_sylows_pgroup (T R : Sylow 2 (alternatingGroup (Fin 5))) (hne : T ≠ R)
    (A : Subgroup (alternatingGroup (Fin 5))) (hp : IsPGroup 2 A)
    (hAT : A ≤ T) (hAR : A ≤ R) : A = ⊥ := by
  obtain ⟨i,hi⟩ := Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_eq_stabilizer T
  obtain ⟨j,hj⟩ := Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_eq_stabilizer R
  have hij : i ≠ j := by
    intro he
    have hle : (T : Subgroup (alternatingGroup (Fin 5))) ≤ normalizer (R : Set (alternatingGroup (Fin 5))) := by
      rw [hj,←he,←hi]
      exact (T : Subgroup (alternatingGroup (Fin 5))).le_normalizer
    have hh := T.isPGroup'.inf_normalizer_sylow R
    rw [inf_eq_left.mpr hle] at hh
    exact hne (Sylow.ext (T.is_maximal' R.isPGroup' (inf_eq_left.mp hh.symm)).symm)
  have cert : ∀ (x : (alternatingGroup (Fin 5))) (i j : Fin 5), i ≠ j → x.val i = i → x.val j = j → x ^ 3 = 1 := by
    decide +kernel
  apply bot_unique
  intro x hx
  apply mem_bot.mpr
  have hx3 : (⟨x,hx⟩ : A) ^ 3 = 1 := Subtype.ext
    (cert x i j hij (by have hh := (T : Subgroup (alternatingGroup (Fin 5))).le_normalizer (hAT hx); change x ∈ normalizer (T : Set (alternatingGroup (Fin 5))) at hh; rw [hi] at hh; exact hh)
      (by have hh := (R : Subgroup (alternatingGroup (Fin 5))).le_normalizer (hAR hx); change x ∈ normalizer (R : Set (alternatingGroup (Fin 5))) at hh; rw [hj] at hh; exact hh))
  have hcop := hp.orderOf_coprime (by decide : Nat.Coprime 2 3) (⟨x,hx⟩ : A)
  have hh := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
    (dvd_refl (orderOf (⟨x,hx⟩ : A))) (orderOf_dvd_of_pow_eq_one hx3))
  exact congrArg Subtype.val hh

open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- A two-subgroup fixing a nonbacktracking alpha turn lies in the alpha core. -/
theorem source_a5_turn_two_subgroup_le_core (h : LocallyRankOneTriple P B)
    (hB : ∃ R : Sylow 2 B, (R : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a b c : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (hac : (graph (family P)).Adj a c) (hbc : b ≠ c)
    (e : (stabilizer (family P) a ⧸ pCore 2 (stabilizer (family P) a)) ≃* (alternatingGroup (Fin 5)))
    (A : Subgroup G) (hp : IsPGroup 2 A)
    (ha : A ≤ stabilizer (family P) a) (hb : A ≤ stabilizer (family P) b)
    (hc : A ≤ stabilizer (family P) c) : A ≤ Q (family P) a := by
  let := finite_endpoints h
  let H := stabilizer (family P) a
  let E := H ⊓ stabilizer (family P) b
  let E' := H ⊓ stabilizer (family P) c
  let : Finite E := Finite.of_injective (inclusion (show E ≤ H from inf_le_left)) (inclusion_injective _)
  let : Finite E' := Finite.of_injective (inclusion (show E' ≤ H from inf_le_left)) (inclusion_injective _)
  obtain ⟨T,hT⟩ := source_edge_vertex_sylow h hS hab
  obtain ⟨R,hR⟩ := source_edge_vertex_sylow h hS hac
  have hTeq := sylow_image_eq_edge_core H E inf_le_left (source_edge_core_sylow h hB hab) T hT
  have hReq := sylow_image_eq_edge_core H E' inf_le_left (source_edge_core_sylow h hB hac) R hR
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let T' := T.mapSurjective hq
  let R' := R.mapSurjective hq
  have hne : T' ≠ R' := by
    intro he
    have hh := congrArg (fun U : Sylow 2 (alternatingGroup (Fin 5)) => (U : Subgroup (alternatingGroup (Fin 5))).comap q) he
    change ((T : Subgroup H).map q).comap q = ((R : Subgroup H).map q).comap q at hh
    rw [comap_map_eq,comap_map_eq,hk,
      sup_eq_left.mpr (pCore_isPGroup.le_sylow_of_normal T),
      sup_eq_left.mpr (pCore_isPGroup.le_sylow_of_normal R)] at hh
    have hcores : E.pCoreIn 2 = E'.pCoreIn 2 := by rw [←hTeq,←hReq,hh]
    obtain ⟨g,hga,hgb⟩ := locally_transitive (family P) hab hac
    have hEg : E.map (MulAut.conj g).toMonoidHom = E' := by
      change (H ⊓ stabilizer (family P) b).map _ = _
      rw [map_inf _ _ _ (MulAut.conj g).injective,←stabilizer_translate,←stabilizer_translate]
      rw [show g • a = a from hga,hgb]
    have hn : g ∈ normalizer (E.pCoreIn 2 : Set G) := by
      apply mem_normalizer_iff_map_conj_eq.mpr
      change (E.pCoreIn 2).map (MulAut.conj g).toMonoidHom = E.pCoreIn 2
      rw [←Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective
        2 (MulAut.conj g).toMonoidHom (MulAut.conj g).injective,hEg,hcores]
    have hfix := ((source_edge_core_normalizer h hB hab).le ⟨hga,hn⟩).2
    exact hbc (hfix.symm.trans hgb)
  have hAT : A.subgroupOf H ≤ (T : Subgroup H) := by
    have hh := pGroup_le_core_of_core_sylow E A (le_inf ha hb) hp (source_edge_core_sylow h hB hab)
    intro x hx
    have hm := hh hx
    rw [←hTeq,mem_map] at hm
    obtain ⟨y,hy,hyx⟩ := hm
    exact (Subtype.ext hyx : y = x) ▸ hy
  have hAR : A.subgroupOf H ≤ (R : Subgroup H) := by
    have hh := pGroup_le_core_of_core_sylow E' A (le_inf ha hc) hp (source_edge_core_sylow h hB hac)
    intro x hx
    have hm := hh hx
    rw [←hReq,mem_map] at hm
    obtain ⟨y,hy,hyx⟩ := hm
    exact (Subtype.ext hyx : y = x) ▸ hy
  have hzero := a5_two_sylows_pgroup T' R' hne ((A.subgroupOf H).map q)
    (hp.comap_subtype.map q) (map_mono hAT) (map_mono hAR)
  have hker := (Subgroup.map_eq_bot_iff _).mp hzero
  rw [hk] at hker
  intro x hx
  exact mem_map_of_mem H.subtype (hker (show (⟨x,ha hx⟩ : H) ∈ A.subgroupOf H from hx))

/-- At a cubic vertex, fixing two distinct neighbors fixes the entire star.
The normal Sylow in the full local kernel then contains the two-subgroup. -/
theorem source_cubic_turn_two_subgroup_le_core (h : LocallyRankOneTriple P B)
    (hB : ∃ R : Sylow 2 B, (R : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a b c : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (hcard : Nat.card ((graph (family P)).neighborSet b) = 3)
    (A : Subgroup G) (hp : IsPGroup 2 A)
    (ha : A ≤ stabilizer (family P) a) (hb : A ≤ stabilizer (family P) b)
    (hc : A ≤ stabilizer (family P) c) : A ≤ Q (family P) b := by
  let := finite_endpoints h
  let := Nat.finite_of_card_ne_zero (show Nat.card ((graph (family P)).neighborSet b) ≠ 0 by omega)
  let d := Finite.equivFinOfCardEq hcard
  have cert : ∀ (f : Equiv.Perm (Fin 3)) (i j : Fin 3), i ≠ j → f i = i → f j = j → f = 1 := by
    decide +kernel
  apply CommutingTrivial.two_subgroup_le_Q (family P) b (source_kernel_sylow h hB hS b) hp
  intro x hx
  have hf : localAction (family P) b ⟨x,hb hx⟩ = 1 := by
    apply (Equiv.permCongrHom d).injective
    rw [map_one]
    apply cert _ (d ⟨a,hab.symm⟩) (d ⟨c,hbc⟩)
      (fun he => hac (congrArg Subtype.val (d.injective he)))
    · change d ((localAction (family P) b ⟨x,hb hx⟩) (d.symm (d ⟨a,hab.symm⟩))) = d ⟨a,hab.symm⟩
      rw [d.symm_apply_apply]
      exact congrArg d (Subtype.ext (ha hx))
    · change d ((localAction (family P) b ⟨x,hb hx⟩) (d.symm (d ⟨c,hbc⟩))) = d ⟨c,hbc⟩
      rw [d.symm_apply_apply]
      exact congrArg d (Subtype.ext (hc hx))
  have hm : (⟨x,hb hx⟩ : stabilizer (family P) b) ∈ (localAction (family P) b).ker := hf
  rw [←U_eq_localAction_kernel] at hm
  exact hm

/-- A two-subgroup fixing five consecutive edges in the cubic A₅ branch
is trivial. Only consecutive backtracking is excluded. -/
theorem source_cubic_a5_five_edge_two_subgroup_eq_bot (h : LocallyRankOneTriple P B)
    (hB : ∃ R : Sylow 2 B, (R : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v₀ v₁ a b c v₅ : Vertex (family P)}
    (h01 : (graph (family P)).Adj v₀ v₁) (h1a : (graph (family P)).Adj v₁ a)
    (hcrit : IsCriticalPair (family P) a b) (hb : DGS85.b (family P) = 1)
    (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hc5 : (graph (family P)).Adj c v₅)
    (h0a : v₀ ≠ a) (h1b : v₁ ≠ b) (hac : a ≠ c) (hb5 : b ≠ v₅)
    (hcard : Nat.card ((graph (family P)).neighborSet b) = 3)
    (e : (stabilizer (family P) a ⧸ pCore 2 (stabilizer (family P) a)) ≃*
      alternatingGroup (Fin 5))
    (A : Subgroup G) (hp : IsPGroup 2 A)
    (hA0 : A ≤ stabilizer (family P) v₀) (hA1 : A ≤ stabilizer (family P) v₁)
    (hAa : A ≤ stabilizer (family P) a) (hAb : A ≤ stabilizer (family P) b)
    (hAc : A ≤ stabilizer (family P) c) (hA5 : A ≤ stabilizer (family P) v₅) : A = ⊥ := by
  let := finite_endpoints h
  have hab := source_critical_one_adjacent hcrit hb
  obtain ⟨g,hga,hgb⟩ := locally_transitive (family P) hab h1a.symm
  have hgb' : g • b ≠ b := by rw [hgb]; exact h1b
  have hI := source_cubic_a5_neighbor_intersection_eq_center h hB hS hcrit hb hcomm
    hbc hac hcard e g hga hgb'
  have htwo := source_cubic_a5_center_card_two h hB hS hcrit hb hcomm hbc hac hcard e g hga hgb'
  have hnot := source_cubic_a5_layer_card_ne_two h hB hS hcrit hb hcard e
    h1a.symm (Ne.symm h1b) h01.symm (Ne.symm h0a)
  let J := neighborCoreIntersection (family P) b ⊓ Q (family P) v₁
  let : Finite (neighborCoreIntersection (family P) b) := Finite.of_injective
    (inclusion ((neighborCoreIntersection_le _ hab).trans (Q_le_stabilizer _ a))) (inclusion_injective _)
  have hJ : J = ⊥ := by
    have hd := card_dvd_of_le (show J ≤ neighborCoreIntersection (family P) b from inf_le_left)
    have hIcard : Nat.card (neighborCoreIntersection (family P) b) = 2 := by rw [hI,htwo]
    rw [hIcard] at hd
    exact eq_bot_of_card_eq _ ((Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_right hnot)
  have hAQa := source_a5_turn_two_subgroup_le_core h hB hS hab h1a.symm
    (Ne.symm h1b) e A hp hAa hAb hA1
  obtain ⟨r,_,hra⟩ := locally_transitive (family P) hab.symm hbc
  have hstab : stabilizer (family P) c =
      (stabilizer (family P) a).map (MulAut.conj r).toMonoidHom := by
    rw [←hra,stabilizer_translate]
  let es := (MulEquiv.subgroupCongr hstab).trans
    ((stabilizer (family P) a).equivMapOfInjective
      (MulAut.conj r).toMonoidHom (MulAut.conj r).injective).symm
  let ec := (QuotientGroup.congr _ _ es (pCore_map_iso 2 es)).trans e
  have hAQc := source_a5_turn_two_subgroup_le_core h hB hS hbc.symm hc5 hb5 ec A hp hAc hAb hA5
  have hAI : A ≤ neighborCoreIntersection (family P) b := by
    rw [←source_cubic_core_pair_eq_neighbor_intersection h hcrit hb hbc hac hcard]
    exact le_inf hAQa hAQc
  have hcard1 : Nat.card ((graph (family P)).neighborSet v₁) = 3 := by
    rw [←hgb]
    exact (Nat.card_congr ((Subgroup.CosetGeometry.translationGraphIso (family P) g).mapNeighborSet b)).symm.trans hcard
  have hAQ1 := source_cubic_turn_two_subgroup_le_core h hB hS h01 h1a h0a hcard1 A hp hA0 hA1 hAa
  exact bot_unique ((le_inf hAI hAQ1).trans hJ.le)

/-- The pointwise fixer of the five-edge chain has odd order, retaining the
actual vertex stabilizers and allowing a closed source path. -/
theorem source_cubic_a5_five_edge_fixer_odd (h : LocallyRankOneTriple P B)
    (hB : ∃ R : Sylow 2 B, (R : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v₀ v₁ a b c v₅ : Vertex (family P)}
    (h01 : (graph (family P)).Adj v₀ v₁) (h1a : (graph (family P)).Adj v₁ a)
    (hcrit : IsCriticalPair (family P) a b) (hb : DGS85.b (family P) = 1)
    (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hc5 : (graph (family P)).Adj c v₅)
    (h0a : v₀ ≠ a) (h1b : v₁ ≠ b) (hac : a ≠ c) (hb5 : b ≠ v₅)
    (hcard : Nat.card ((graph (family P)).neighborSet b) = 3)
    (e : (stabilizer (family P) a ⧸ pCore 2 (stabilizer (family P) a)) ≃*
      alternatingGroup (Fin 5)) :
    Odd (Nat.card (stabilizer (family P) v₀ ⊓ stabilizer (family P) v₁ ⊓
      stabilizer (family P) a ⊓ stabilizer (family P) b ⊓
      stabilizer (family P) c ⊓ stabilizer (family P) v₅ : Subgroup G)) := by
  let := finite_endpoints h
  let D := stabilizer (family P) v₀ ⊓ stabilizer (family P) v₁ ⊓
    stabilizer (family P) a ⊓ stabilizer (family P) b ⊓
    stabilizer (family P) c ⊓ stabilizer (family P) v₅
  have hD0 : D ≤ stabilizer (family P) v₀ := fun _ hx => hx.1.1.1.1.1
  let : Finite D := Finite.of_injective (inclusion hD0) (inclusion_injective _)
  apply Nat.not_even_iff_odd.mp
  rw [even_iff_two_dvd]
  intro hd
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := D) 2 hd
  let A := zpowers (x : G)
  have hp : IsPGroup 2 A := IsPGroup.of_card_dvd_pow (n := 1) (by
    change Nat.card (zpowers (x : G)) ∣ 2^1
    rw [Nat.card_zpowers,Subgroup.orderOf_coe,hx]; decide)
  have hAD : A ≤ D := zpowers_le.mpr x.property
  have he := source_cubic_a5_five_edge_two_subgroup_eq_bot h hB hS h01 h1a hcrit hb hcomm hbc hc5
    h0a h1b hac hb5 hcard e A hp (hAD.trans hD0)
    (hAD.trans (fun _ hz => hz.1.1.1.1.2)) (hAD.trans (fun _ hz => hz.1.1.1.2))
    (hAD.trans (fun _ hz => hz.1.1.2)) (hAD.trans (fun _ hz => hz.1.2))
    (hAD.trans inf_le_right)
  have hx1 : x = 1 := Subtype.ext (mem_bot.mp (he ▸ mem_zpowers (x : G)))
  simp only [hx1,orderOf_one] at hx
  omega

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
