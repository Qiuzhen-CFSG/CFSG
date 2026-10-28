module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReducedCubicApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.Centers
public import Theory.SpecificGroups.Alternating.FourPairAutomorphisms
public import Theory.SpecificGroups.AlternatingSix.SmallIndex
public import Theory.SpecificGroups.Alternating.FiveSylowMaximal

/-!
# Core generation in the cubic A₅ branch

The full edge stabilizer is maximal in the alpha vertex group and normalizes
its Sylow two-subgroup. In the actual A₅ core quotient its image is therefore
an A₄ Sylow normalizer. Every nontrivial normal subgroup of this normalizer
contains its Sylow four-group. The corrected beta span has nontrivial image,
by escape of the opposite seed, so it supplements the alpha core in the edge
Sylow. Intersecting this product with Qβ proves the cubic A₅ instance of
DGS (11.3)(h).

The original mixed A₅/S₃ quotient markings supply every hypothesis of this
instance in the literal reduced completion. The mixed numerical consumer
thus retains only Qα = Zα and the seed-intersection order; core generation
is no longer an input. These are partial Chapter 11 consequences, not the
full profiles or a recognition of the amalgam.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(11.2)(c), (11.3)(h), and (11.7)(c), printed pp.168--175.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile

private theorem a5_sylow_le_normal (T : Sylow 2 (alternatingGroup (Fin 5)))
    (N : Subgroup (alternatingGroup (Fin 5)))
    (hN : N ≤ normalizer (T : Set (alternatingGroup (Fin 5))))
    (hn : normalizer (T : Set (alternatingGroup (Fin 5))) ≤ normalizer (N : Set _))
    (hne : N ≠ ⊥) : (T : Subgroup (alternatingGroup (Fin 5))) ≤ N := by
  let D := normalizer (T : Set (alternatingGroup (Fin 5)))
  obtain ⟨i, hi⟩ := Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_eq_stabilizer T
  let e : D ≃* alternatingGroup (Fin 4) :=
    (MulEquiv.subgroupCongr hi).trans (AlternatingSix.SmallIndex.pointEquiv i)
  let N₀ := N.subgroupOf D
  let : N₀.Normal := (normal_subgroupOf_iff_le_normalizer hN).mpr hn
  let N₁ := N₀.map e.toMonoidHom
  let : N₁.Normal := Normal.map inferInstance _ e.surjective
  have hN₀ : N₀ ≠ ⊥ := by
    intro he
    apply hne
    calc
      N = N₀.map D.subtype := (map_subgroupOf_eq_of_le (show N ≤ D from hN)).symm
      _ = ⊥ := by rw [he,Subgroup.map_bot]
  have hN₁ : N₁ ≠ ⊥ := by
    intro he
    exact hN₀ ((map_eq_bot_iff_of_injective _ e.injective).mp he)
  have hK : AlternatingFourPair.K ≤ N₁ := by
    rcases AlternatingFourPair.normalA4 N₁ with he | he | he
    · exact (hN₁ he).elim
    · exact he ▸ le_rfl
    · exact he ▸ le_top
  let T₀ := (T : Subgroup (alternatingGroup (Fin 5))).subgroupOf D
  have hT₁ : IsPGroup 2 (T₀.map e.toMonoidHom) := T.isPGroup'.comap_subtype.map _
  obtain ⟨R,hR⟩ := hT₁.exists_le_sylow
  rw [alternatingGroup.two_sylow_eq_kleinFour_of_card_eq_four (by norm_num) R] at hR
  have hTN : T₀ ≤ N₀ := by
    apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
    exact hR.trans hK
  intro t ht
  exact hTN (show (⟨t,(T : Subgroup (alternatingGroup (Fin 5))).le_normalizer ht⟩ : D) ∈ T₀ from ht)

private theorem a5_normalizer_supplement {H : Type*} [Group H] [Finite H]
    (q : H →* alternatingGroup (Fin 5)) (hq : Function.Surjective q)
    (T : Sylow 2 H) (E V : Subgroup H)
    (hE : E.map q = normalizer (T.mapSurjective hq : Set (alternatingGroup (Fin 5))))
    (hVE : V ≤ E) (hn : E ≤ normalizer (V : Set H)) (hne : ¬ V ≤ q.ker) :
    (T : Subgroup H) ≤ V ⊔ q.ker := by
  have hNV : V.map q ≤ normalizer (T.mapSurjective hq : Set _) :=
    (map_mono hVE).trans_eq hE
  have hnV : normalizer (T.mapSurjective hq : Set _) ≤ normalizer ((V.map q : Subgroup (alternatingGroup (Fin 5))) : Set (alternatingGroup (Fin 5))) := by
    rw [←hE]
    exact (map_mono hn).trans (le_normalizer_map q)
  have hneV : V.map q ≠ ⊥ := by
    intro he
    exact hne ((Subgroup.map_eq_bot_iff V).mp he)
  have hTV := a5_sylow_le_normal (T.mapSurjective hq) (V.map q) hNV hnV hneV
  have hh : (T : Subgroup H) ≤ (V.map q).comap q := map_le_iff_le_comap.mp hTV
  simpa only [comap_map_eq] using hh

private theorem a5_maximal_supplement {H : Type*} [Group H] [Finite H]
    (q : H →* alternatingGroup (Fin 5)) (hq : Function.Surjective q)
    (T : Sylow 2 H) (E V : Subgroup H)
    (hnT : E ≤ normalizer (T : Set H))
    (hmax : ∀ D : Subgroup H, E ≤ D → D = E ∨ D = ⊤)
    (hVE : V ≤ E) (hn : E ≤ normalizer (V : Set H)) (hne : ¬ V ≤ q.ker) :
    (T : Subgroup H) ≤ V ⊔ q.ker := by
  have hnot : normalizer (T : Set H) ≠ ⊤ := by
    intro he
    have hm := T.normalizer_map_surjective q hq
    rw [he,map_top_of_surjective q hq] at hm
    exact (Theory.SpecificGroups.Alternating.FiveSylowMaximal.sylow_normalizer_isCoatom
      (T.mapSurjective hq)).1 hm.symm
  have hE : E = normalizer (T : Set H) := by
    rcases hmax _ hnT with he | he
    · exact he.symm
    · exact (hnot he).elim
  apply a5_normalizer_supplement q hq T E V
    (hE ▸ T.normalizer_map_surjective q hq) hVE hn hne

open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem source_a5_edge_supplement (h : LocallyRankOneTriple P B)
    (hB : ∃ R : Sylow 2 B, (R : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a b : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (e : (stabilizer (family P) a ⧸ pCore 2 (stabilizer (family P) a)) ≃*
      alternatingGroup (Fin 5))
    (V : Subgroup G) (hVE : V ≤ stabilizer (family P) a ⊓ stabilizer (family P) b)
    (hnV : stabilizer (family P) a ⊓ stabilizer (family P) b ≤ normalizer (V : Set G))
    (heV : ¬ V ≤ Q (family P) a) :
    (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 ≤ V ⊔ Q (family P) a := by
  let := finite_endpoints h
  let H := stabilizer (family P) a
  let E := stabilizer (family P) a ⊓ stabilizer (family P) b
  let E₀ := E.subgroupOf H
  let V₀ := V.subgroupOf H
  have hEH : E ≤ H := inf_le_left
  have hVH : V ≤ H := hVE.trans hEH
  obtain ⟨T,hT⟩ := source_edge_vertex_sylow h hS hab
  have hTeq := sylow_image_eq_edge_core H E hEH (source_edge_core_sylow h hB hab) T hT
  have hnE : E ≤ normalizer ((T : Subgroup H).map H.subtype : Set G) := by
    rw [hTeq]
    exact E.le_normalizer.trans (normalizer_le_normalizer_characteristic_image E (pCore 2 E))
  have hnT : E₀ ≤ normalizer (T : Set H) := by
    have ht : ((T : Subgroup H).map H.subtype).comap H.subtype = (T : Subgroup H) := by
      exact comap_map_eq_self (by simp)
    have hh := (comap_mono hnE).trans (le_normalizer_comap H.subtype)
    rwa [ht] at hh
  have hmax : ∀ D : Subgroup H, E₀ ≤ D → D = E₀ ∨ D = ⊤ := by
    intro D hD
    have hED : E ≤ D.map H.subtype := by
      rw [←map_subgroupOf_eq_of_le hEH]
      exact map_mono hD
    rcases source_edge_maximal h hab (D.map H.subtype) hED (map_subtype_le D) with hd | hd
    · left
      apply map_injective H.subtype_injective
      exact hd.trans (map_subgroupOf_eq_of_le hEH).symm
    · right
      apply map_injective H.subtype_injective
      rw [←MonoidHom.range_eq_map, range_subtype]
      exact hd
  let q : H →* alternatingGroup (Fin 5) := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = pCore 2 H := by
    ext x
    change e ((QuotientGroup.mk' (pCore 2 H)) x) = 1 ↔ _
    rw [←e.map_one, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  have heV₀ : ¬ V₀ ≤ q.ker := by
    rw [hker]
    intro hh
    apply heV
    have hm := map_mono (f := H.subtype) hh
    rw [map_subgroupOf_eq_of_le hVH] at hm
    exact hm
  have hh := a5_maximal_supplement q hq T E₀ V₀ hnT hmax
    (comap_mono hVE) ((comap_mono hnV).trans (le_normalizer_comap H.subtype)) heV₀
  have hm := map_mono (f := H.subtype) hh
  rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hVH,hker,hTeq] at hm
  exact hm


/-- The cubic A₅ instance of source (11.3)(h), with the actual alpha quotient. -/
theorem source_cubic_a5_core_generation (h : LocallyRankOneTriple P B)
    (hB : ∃ R : Sylow 2 B, (R : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (hcard : Nat.card ((graph (family P)).neighborSet b) = 3)
    (e : (stabilizer (family P) a ⧸ pCore 2 (stabilizer (family P) a)) ≃*
      alternatingGroup (Fin 5)) :
    Q (family P) b = pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b) ⊔
      (Q (family P) a ⊓ Q (family P) b) := by
  let := finite_endpoints h
  have hab := source_critical_one_adjacent hc hb
  let V := betaSpan (stabilizer (family P) b) (Z (family P) a)
  have hVQ : V ≤ Q (family P) b := betaSpan_le_core _ _
  have hQaE : Q (family P) a ≤ stabilizer (family P) a ⊓ stabilizer (family P) b :=
    (source_Z_Q_U h a).2.trans (ballKernel_one_le_edge _ hab)
  have hQbE : Q (family P) b ≤ stabilizer (family P) a ⊓ stabilizer (family P) b := by
    rw [inf_comm]
    exact (source_Z_Q_U h b).2.trans (ballKernel_one_le_edge _ hab.symm)
  have hnV : stabilizer (family P) a ⊓ stabilizer (family P) b ≤ normalizer (V : Set G) :=
    inf_le_right.trans (le_normalizer_conjugateSpanBy _ _)
  have heV : ¬ V ≤ Q (family P) a := by
    have hn : ¬ IsPGroup 2 (Z (family P) c ⊔ Z (family P) a : Subgroup G) := by
      rw [sup_comm]
      exact source_cubic_centers_not_isPGroup h hc hb hbc hac hcard
    have he := source_seed_not_le_opposite_core h hbc.symm hab.symm hn
    intro hh
    exact he ((show Z (family P) c ⊓ Q (family P) b ≤ V from
      le_sup_right.trans (source_pairSpan_le_betaSpan h hab hbc)).trans hh)
  have hsub := source_a5_edge_supplement h hB hS hab e V (hVQ.trans hQbE) hnV heV
  let E := stabilizer (family P) a ⊓ stabilizer (family P) b
  let : Finite E := Finite.of_injective (inclusion (show E ≤ stabilizer (family P) a from inf_le_left))
    (inclusion_injective _)
  have hQsub : Q (family P) b ≤ V ⊔ Q (family P) a :=
    (pGroup_le_core_of_core_sylow E _ hQbE (isPGroup_pCoreIn 2 _) (source_edge_core_sylow h hB hab)).trans hsub
  have hgen : Q (family P) b = V ⊔ (Q (family P) a ⊓ Q (family P) b) := by
    apply le_antisymm ?_ (sup_le hVQ inf_le_right)
    intro x hx
    have hx' : x ∈ (V : Set G) * (Q (family P) a : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left V (Q (family P) a) (hQaE.trans hnV)]
      exact hQsub hx
    obtain ⟨v,hv,y,hy,rfl⟩ := hx'
    have hyQ : y ∈ Q (family P) b := by
      have hh := (Q (family P) b).mul_mem ((Q (family P) b).inv_mem (hVQ hv)) hx
      simpa only [inv_mul_cancel_left] using hh
    exact mul_mem (mem_sup_left hv) (mem_sup_right ⟨hy,hyQ⟩)
  rw [show V = pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b) from
    source_cubic_betaSpan_eq_pairSpan h hc hb hbc hac hcard] at hgen
  exact hgen


variable [Finite G] (K U₀ S : Subgroup G)
local notation "F" => Reduction.reducedFamily ![K,U₀] S
local notation "M" => Reduction.G₀ ![K,U₀] S
local notation "α" => base F false
local notation "β" => base F true

/-- The original mixed markings discharge the quotient and graph hypotheses
of the beta-core generation formula in the literal reduced completion. -/
theorem mixed_binary_graph_core_generation (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1)
    (c : Vertex F) (hbc : (graph F).Adj β c) (hac : α ≠ c) :
    Q F β = pairSpan (Z F α) (Z F c) (Q F β) ⊔ (Q F α ⊓ Q F β) := by
  have he : Nonempty ((Reduction.P₀ ![K,U₀] S 0 ⧸ pCore 2 (Reduction.P₀ ![K,U₀] S 0)) ≃*
      alternatingGroup (Fin 5)) := by
    rw [Reduction.P₀_eq_source h 0]
    exact h.mixed_reduced_first_quotient eK eU
  let e₀ := subgroupOfEquivOfLe (show Reduction.P₀ ![K,U₀] S 0 ≤ M from le_sup_left)
  let eq₀ := QuotientGroup.congr _ _ e₀ (pCore_map_iso 2 e₀)
  have hs : stabilizer F α = (Reduction.P₀ ![K,U₀] S 0).subgroupOf M :=
    Subgroup.CosetGeometry.stabilizer_base _ _
  let es := MulEquiv.subgroupCongr hs
  let eqs := QuotientGroup.congr _ _ es (pCore_map_iso 2 es)
  let e := (eqs.trans eq₀).trans he.some
  exact source_cubic_a5_core_generation (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h)
    hc hb hbc hac (mixed_reduced_neighbor_cards K U₀ S h eK eU β) e

/-- The actual mixed seed orders, with beta-core generation discharged.
The alpha-core identity and seed-intersection order remain earlier-source inputs. -/
theorem mixed_binary_graph_seed_orders_of_intersection (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1)
    (c : Vertex F) (hbc : (graph F).Adj β c) (hac : α ≠ c)
    (hQa : Q F α = Z F α)
    (hinter : Nat.card ((Z F α ⊓ Q F β) ⊓ (Z F c ⊓ Q F β) : Subgroup M) = 2) :
    Nat.card (Z F α) = 16 ∧ Nat.card (Z F α ⊓ Q F β : Subgroup M) = 8 ∧
      Nat.card (Q F β) = 32 :=
  mixed_binary_graph_seed_orders K U₀ S h eK eU hc hb c hbc
    (mixed_binary_graph_core_generation K U₀ S h eK eU hc hb c hbc hac) hQa hinter

/-- The literal mixed size application now needs only the alpha-core identity
and seed-intersection order from the remaining Chapter 11 local argument. -/
theorem mixed_binary_graph_row_size_of_intersection (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1)
    (c : Vertex F) (hbc : (graph F).Adj β c) (hac : α ≠ c)
    (hQa : Q F α = Z F α)
    (hinter : Nat.card ((Z F α ⊓ Q F β) ⊓ (Z F c ⊓ Q F β) : Subgroup M) = 2) :
    Nat.card (twoCore (commonBorel ![K,U₀] S)) = 64 ∧
      (Nat.card S = 64 ∨ Nat.card S = 128) :=
  mixed_binary_graph_row_size_of_cubic K U₀ S h eK eU hc hb c hbc
    (mixed_binary_graph_core_generation K U₀ S h eK eU hc hb c hbc hac) hQa hinter

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
