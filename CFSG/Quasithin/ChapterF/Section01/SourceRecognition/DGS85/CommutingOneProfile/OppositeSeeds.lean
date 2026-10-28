module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.A5CoreGeneration

/-!
# Opposite-seed generation in the cubic A₅ branch

The source beta-core generation formula and the cubic Borel product imply
S = Qα (Zγ ∩ Qβ). Thus the opposite seed maps onto the full Sylow four-group
in the marked A₅ quotient. Two such seeds, conjugated by an alpha element
moving beta, generate the entire alpha stabilizer modulo Qα: distinct
Sylow subgroups in A₅ generate A₅ by unique Borel overgroup control.

This is the mixed-row instance of (11.5) and the generation of W used at
the beginning of (11.6). `NeighborSeparation` applies it to the literal
faithful source graph. The quotient is the actual stabilizer modulo its
two-core; no equality between that core and the full local kernel is used.
Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(11.5)--(11.6), printed p.172.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile

private theorem a5_pair_sylow_generate (T R : Sylow 2 (alternatingGroup (Fin 5)))
    (hne : T ≠ R) : (T : Subgroup (alternatingGroup (Fin 5))) ⊔ (R : Subgroup (alternatingGroup (Fin 5))) = ⊤ := by
  by_contra hn
  have hR := (le_sup_right : (R : Subgroup (alternatingGroup (Fin 5))) ≤ (T : Subgroup (alternatingGroup (Fin 5))) ⊔ (R : Subgroup (alternatingGroup (Fin 5)))).trans
    (Theory.SpecificGroups.Alternating.FiveSylowMaximal.overgroup_le_sylow_normalizer
      T _ le_sup_left hn)
  have hi := R.isPGroup'.inf_normalizer_sylow T
  rw [inf_eq_left.mpr hR] at hi
  exact hne (Sylow.ext (R.is_maximal' T.isPGroup' (inf_eq_left.mp hi.symm)))

private theorem a5_seed_pair_generate {H : Type*} [Group H] [Finite H]
    (e : (H ⧸ pCore 2 H) ≃* alternatingGroup (Fin 5))
    (T : Sylow 2 H) (A : Subgroup H) (hA : A ⊔ pCore 2 H = T)
    (g : H) (hg : g ∉ normalizer (T : Set H)) :
    (A ⊔ A.map (MulAut.conj g).toMonoidHom) ⊔ pCore 2 H = ⊤ := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 H := by
    ext x
    change e ((QuotientGroup.mk' (pCore 2 H)) x) = 1 ↔ _
    rw [map_eq_one_iff e e.injective]
    exact QuotientGroup.eq_one_iff x
  let T' := T.mapSurjective hq
  let R := T.mapSurjective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).surjective
  let R' := R.mapSurjective hq
  have hne : T' ≠ R' := by
    intro he
    apply hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    have hh := congrArg (fun U : Sylow 2 (alternatingGroup (Fin 5)) =>
      (U : Subgroup _).comap q) he
    change ((T : Subgroup H).map q).comap q = ((R : Subgroup H).map q).comap q at hh
    rw [comap_map_eq, comap_map_eq, hk,
      sup_eq_left.mpr (pCore_isPGroup.le_sylow_of_normal T),
      sup_eq_left.mpr (pCore_isPGroup.le_sylow_of_normal R)] at hh
    exact hh.symm
  have hN : (pCore 2 H).map (MulAut.conj g).toMonoidHom = pCore 2 H :=
    mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; trivial)
  have hR : A.map (MulAut.conj g).toMonoidHom ⊔ pCore 2 H = R := by
    rw [←hN, ←Subgroup.map_sup, hA]
    rfl
  have hmapA : A.map q = T' := by
    have hh := congrArg (map q) hA
    rwa [Subgroup.map_sup, ←hk, map_ker_self, sup_bot_eq] at hh
  have hmapR : (A.map (MulAut.conj g).toMonoidHom).map q = R' := by
    have hh := congrArg (map q) hR
    rwa [Subgroup.map_sup, ←hk, map_ker_self, sup_bot_eq] at hh
  apply map_injective_of_ker_le q (hk ▸ le_sup_right) le_top
  rw [Subgroup.map_sup, Subgroup.map_sup, hmapA, hmapR,
    a5_pair_sylow_generate T' R' hne, top_sup_eq, map_top_of_surjective q hq]

open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The opposite seed supplements the alpha core in the full edge Sylow. -/
theorem source_cubic_a5_edge_core_eq_seed_sup_core (h : LocallyRankOneTriple P B)
    (hB : ∃ R : Sylow 2 B, (R : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (hcard : Nat.card ((graph (family P)).neighborSet b) = 3)
    (e : (stabilizer (family P) a ⧸ pCore 2 (stabilizer (family P) a)) ≃*
      alternatingGroup (Fin 5)) :
    (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 =
      (Z (family P) c ⊓ Q (family P) b) ⊔ Q (family P) a := by
  let := finite_endpoints h
  have hab := source_critical_one_adjacent hc hb
  have hprod := source_cubic_edge_core_eq_center_sup_core h hc hb hcard
    (source_kernel_sylow h hB hS b)
  have hgen := source_cubic_a5_core_generation h hB hS hc hb hbc hac hcard e
  have haE : Q (family P) a ≤ stabilizer (family P) a ⊓ stabilizer (family P) b :=
    (source_Z_Q_U h a).2.trans (ballKernel_one_le_edge _ hab)
  let E := stabilizer (family P) a ⊓ stabilizer (family P) b
  let : Finite E := Finite.of_injective (inclusion (show E ≤ stabilizer (family P) a from inf_le_left))
    (inclusion_injective _)
  have haT : Q (family P) a ≤ E.pCoreIn 2 :=
    pGroup_le_core_of_core_sylow E _ haE (isPGroup_pCoreIn 2 _)
    (source_edge_core_sylow h hB hab)
  apply le_antisymm
  · apply hprod.le.trans
    have hz : Z (family P) a ≤ Q (family P) a :=
      (source_Z_Q_U h a).1.trans (map_subtype_le _)
    apply sup_le (hz.trans le_sup_right)
    apply hgen.le.trans
    apply sup_le _ (inf_le_left.trans le_sup_right)
    change (Z (family P) a ⊓ Q (family P) b) ⊔ (Z (family P) c ⊓ Q (family P) b) ≤ _
    exact sup_le (inf_le_left.trans (hz.trans le_sup_right)) le_sup_left
  · exact sup_le (inf_le_right.trans (le_sup_right.trans hprod.symm.le)) haT

/-- Opposite seeds generate the alpha stabilizer modulo its actual two-core. -/
theorem source_cubic_a5_opposite_seed_generation (h : LocallyRankOneTriple P B)
    (hB : ∃ R : Sylow 2 B, (R : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (hcard : Nat.card ((graph (family P)).neighborSet b) = 3)
    (e : (stabilizer (family P) a ⧸ pCore 2 (stabilizer (family P) a)) ≃*
      alternatingGroup (Fin 5))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b) :
    ((Z (family P) c ⊓ Q (family P) b) ⊔
      (Z (family P) (g • c) ⊓ Q (family P) (g • b))) ⊔ Q (family P) a =
        stabilizer (family P) a := by
  let := finite_endpoints h
  let H := stabilizer (family P) a
  let E := stabilizer (family P) a ⊓ stabilizer (family P) b
  let A := Z (family P) c ⊓ Q (family P) b
  have hab := source_critical_one_adjacent hc hb
  obtain ⟨T,hT⟩ := source_edge_vertex_sylow h hS hab
  have hTeq := sylow_image_eq_edge_core H E inf_le_left
    (source_edge_core_sylow h hB hab) T hT
  have hprod := source_cubic_a5_edge_core_eq_seed_sup_core h hB hS hc hb hbc hac hcard e
  have hAH : A ≤ H := inf_le_right.trans ((source_Z_Q_U h b).2.trans
    ((ballKernel_one_le_edge _ hab.symm).trans inf_le_right))
  have hA : A.subgroupOf H ⊔ pCore 2 H = T := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hAH, hTeq]
    exact hprod.symm
  have hnot : normalizer (T : Set H) ≠ ⊤ := by
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
    have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
    intro he
    have hm := T.normalizer_map_surjective q hq
    rw [he,map_top_of_surjective q hq] at hm
    exact (Theory.SpecificGroups.Alternating.FiveSylowMaximal.sylow_normalizer_isCoatom
      (T.mapSurjective hq)).1 hm.symm
  have hnE : E ≤ normalizer ((T : Subgroup H).map H.subtype : Set G) := by
    rw [hTeq]
    exact E.le_normalizer.trans (normalizer_le_normalizer_characteristic_image E (pCore 2 E))
  have hnT : E.subgroupOf H ≤ normalizer (T : Set H) := by
    have ht : ((T : Subgroup H).map H.subtype).comap H.subtype = T :=
      comap_map_eq_self (by simp)
    have hh := (comap_mono hnE).trans (le_normalizer_comap H.subtype)
    rwa [ht] at hh
  have hNE : (normalizer (T : Set H)).map H.subtype = E := by
    have hEN : E ≤ (normalizer (T : Set H)).map H.subtype := by
      rw [←map_subgroupOf_eq_of_le (show E ≤ H from inf_le_left)]
      exact map_mono hnT
    rcases source_edge_maximal h hab _ hEN (map_subtype_le _) with he | he
    · exact he
    · exfalso
      apply hnot
      apply map_injective H.subtype_injective
      rw [←MonoidHom.range_eq_map,range_subtype]
      exact he
  have hg : (⟨g,hga⟩ : H) ∉ normalizer (T : Set H) := by
    intro hn
    have hgE := mem_map_of_mem H.subtype hn
    rw [hNE] at hgE
    exact hgb hgE.2
  have hgen := a5_seed_pair_generate e T (A.subgroupOf H) hA ⟨g,hga⟩ hg
  have hm := congrArg (map H.subtype) hgen
  rw [Subgroup.map_sup, Subgroup.map_sup, map_subgroupOf_eq_of_le hAH,
    ←MonoidHom.range_eq_map,range_subtype] at hm
  have hcmap : ((A.subgroupOf H).map (MulAut.conj (⟨g,hga⟩ : H)).toMonoidHom).map H.subtype =
      A.map (MulAut.conj g).toMonoidHom := by
    rw [map_map]
    have he : H.subtype.comp (MulAut.conj (⟨g,hga⟩ : H)).toMonoidHom =
        (MulAut.conj g).toMonoidHom.comp H.subtype := by ext x; rfl
    rw [he,←map_map,map_subgroupOf_eq_of_le hAH]
  rw [hcmap] at hm
  have hcmap' : A.map (MulAut.conj g).toMonoidHom =
      Z (family P) (g • c) ⊓ Q (family P) (g • b) := by
    change ((Z (family P) c ⊓ Q (family P) b).map _) = _
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective,←Z_translate,←Q_translate]
  rw [hcmap'] at hm
  exact hm

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
