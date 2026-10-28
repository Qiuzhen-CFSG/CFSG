module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.SylowModels.ModelFacts
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Theory.GroupTheory.NormalizerSylowCardinality

/-!
# Constructing the ambient geometry from intrinsic Sylow calculations

The conjugation action gives the bound |T| ≤ |Aut(L)|₂ |T_C|. When L is
centerless, every subgroup of L is disjoint from T_C. Relative normality
makes T normalize T_L. In the sporadic cases the normal p-subgroup theorem
constructs an actual order-two subgroup of T_L ∩ Z(T); its centrality also
puts it inside the center of the intrinsic Sylow subgroup of L.

The two final reductions turn a proved model center embedding and strict
Sylow-order comparison into the exact ExcludedSylowGeometry contract.
The unitary reduction chooses V = T_L; the sporadic reduction chooses V
of order two. Neither reduction asserts the missing concrete model facts.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 16.3.4, printed p.1178 / PDF p.1195.
-/

public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.SylowModels
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L K : Subgroup G} {z : G}

/-- The conjugation image of T bounds |T:T_C| by |Aut(L)|₂. -/
theorem exists_aut_sylow_card_bound
    (hn : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    ∃ A : Sylow 2 (MulAut L),
      Nat.card T ≤ Nat.card A * Nat.card (commutingSylow T L) :=
  Subgroup.exists_sylow_aut_card_bound (T : Subgroup G) L T.isPGroup' hn

omit [Finite G] in
/-- Centerlessness makes the component disjoint from its ambient centralizer. -/
theorem disjoint_commutingSylow_of_centerless (hZ : center L = ⊥)
    {V : Subgroup G} (hVL : V ≤ L) : Disjoint (commutingSylow T L) V := by
  apply disjoint_def.mpr
  intro x hxC hxV
  have hxL := hVL hxV
  have hz : (⟨x, hxL⟩ : L) ∈ center L := by
    apply mem_center_iff.mpr
    intro l
    apply Subtype.ext
    exact mem_centralizer_iff.mp hxC.2 l l.property
  rw [hZ, mem_bot] at hz
  exact congrArg Subtype.val hz

omit [Finite G] in
/-- Normalizing L also normalizes the actual intersection T_L. -/
theorem normalizes_componentSylow
    (hn : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    (T : Subgroup G) ≤ normalizer (componentSylow T L : Set G) :=
  (le_inf (T : Subgroup G).le_normalizer hn).trans inf_normalizer_le_normalizer_inf

/-- The component Sylow from subnormality has ambient image exactly T_L. -/
theorem exists_componentSylow_image (h : CentralComponentSetup T z L) :
    ∃ P : Sylow 2 L, (P : Subgroup L).map L.subtype = componentSylow T L := by
  obtain ⟨P, hP⟩ := h.exists_component_sylow
  refine ⟨P, ?_⟩
  rw [hP]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, y.property⟩
  · intro hx
    exact ⟨⟨x, hx.2⟩, hx.1, rfl⟩

/-- The nontrivial normal subgroup T_L of T contains a central subgroup of order two. -/
theorem exists_central_involution_subgroup
    (h : CentralComponentSetup T z L)
    (hn : (T : Subgroup G) ≤ normalizer (L : Set G))
    (heven : Even (Nat.card L)) :
    ∃ V : Subgroup G, Nat.card V = 2 ∧ V ≤ componentSylow T L ∧
      V ≤ (center T).map (T : Subgroup G).subtype := by
  obtain ⟨P, hP⟩ := h.exists_component_sylow
  let N := L.subgroupOf (T : Subgroup G)
  let : N.Normal := normal_subgroupOf_of_le_normalizer hn
  have hN : Nontrivial N := by
    let : Nontrivial P := (nontrivial_iff_ne_bot _).mpr
      (P.ne_bot_of_dvd_card (even_iff_two_dvd.mp heven))
    obtain ⟨x, hx⟩ := exists_ne (1 : P)
    have hxT : ((x : L) : G) ∈ T := by
      have hp : (x : L) ∈ (P : Subgroup L) := x.property
      rw [hP] at hp
      exact hp
    let y : N := ⟨⟨x, hxT⟩, (x : L).property⟩
    refine ⟨⟨y, 1, ?_⟩⟩
    intro he
    exact hx (Subtype.ext (Subtype.ext
      (congrArg (fun a : N => ((a : T) : G)) he)))
  let : Fact (IsPGroup 2 T) := ⟨T.isPGroup'⟩
  obtain ⟨W, _, hWN, hc, hWZ⟩ :=
    exists_central_subgroup_card_eq_prime_in_normal (p := 2) N hN
  refine ⟨W.map (T : Subgroup G).subtype, ?_, ?_, map_mono hWZ⟩
  · rwa [card_map_of_injective (T : Subgroup G).subtype_injective]
  · rintro x ⟨w, hw, rfl⟩
    exact ⟨w.property, hWN hw⟩

omit [Finite G] in
/-- An ambient central subgroup contained in T_L is central in its intrinsic Sylow model. -/
theorem le_componentSylow_center {P : Sylow 2 L}
    (hP : (P : Subgroup L).map L.subtype = componentSylow T L)
    {V : Subgroup G} (hVL : V ≤ componentSylow T L)
    (hVZ : V ≤ (center T).map (T : Subgroup G).subtype) :
    V ≤ ((center P).map (P : Subgroup L).subtype).map L.subtype := by
  intro x hx
  have hxTL := hVL hx
  have hxP : (⟨x, hxTL.2⟩ : L) ∈ (P : Subgroup L) := by
    have hm : x ∈ (P : Subgroup L).map L.subtype := hP.symm ▸ hxTL
    obtain ⟨y, hy, he⟩ := hm
    have hyx : y = ⟨x, hxTL.2⟩ := Subtype.ext he
    exact hyx ▸ hy
  have hxZ : (⟨x, hxTL.1⟩ : T) ∈ center T := by
    obtain ⟨a, ha, he⟩ := hVZ hx
    have he' : a = ⟨x, hxTL.1⟩ := Subtype.ext he
    exact he' ▸ ha
  refine ⟨⟨x, hxTL.2⟩, ⟨⟨⟨x, hxTL.2⟩, hxP⟩, ?_, rfl⟩, rfl⟩
  apply mem_center_iff.mpr
  intro y
  have hyTL : ((y : L) : G) ∈ componentSylow T L :=
    hP ▸ mem_map_of_mem L.subtype y.property
  apply Subtype.ext
  apply Subtype.ext
  change ((y : L) : G) * x = x * ((y : L) : G)
  exact congrArg (fun a : T => (a : G)) (mem_center_iff.mp hxZ ⟨y, hyTL.1⟩)

/-- The order gap and a full Sylow-center embedding give the required strict ambient inequality. -/
theorem geometry_of_center_embedding
    (hn : (T : Subgroup G) ≤ normalizer (L : Set G))
    (gap : SylowOrderGap L K) {V : Subgroup G}
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hd : Disjoint (commutingSylow T L) V)
    (lift : SylowCenterEmbedding K V) : ExcludedSylowGeometry T L K := by
  obtain ⟨S, hS⟩ := lift
  obtain ⟨A, hA⟩ := exists_aut_sylow_card_bound hn
  refine ⟨V, (S : Subgroup K).map K.subtype, hTV, hd, ⟨S, rfl⟩, hS, ?_⟩
  rw [card_map_of_injective K.subtype_injective]
  exact hA.trans_lt (Nat.mul_lt_mul_of_pos_right (gap A S) Nat.card_pos)

/-- Construct the unitary geometry, with V exactly T_L, from the two intrinsic model facts. -/
theorem geometry_of_fullSylowCenterLifting
    (h : CentralComponentSetup T z L)
    (hn : (L.subgroupOf (involutionCentralizer z)).Normal)
    (hZ : center L = ⊥) (gap : SylowOrderGap L K)
    (lift : FullSylowCenterLifting L K) : ExcludedSylowGeometry T L K := by
  have hTN := h.sylow_le_normalizer_of_normal hn
  obtain ⟨P, hP⟩ := exists_componentSylow_image h
  apply geometry_of_center_embedding hTN gap (V := componentSylow T L)
    (normalizes_componentSylow hTN)
    (disjoint_commutingSylow_of_centerless hZ inf_le_right)
  rw [← hP]
  exact lift P

/-- Construct the sporadic geometry using an order-two subgroup of T_L ∩ Z(T). -/
theorem geometry_of_involutionCenterLifting
    (h : CentralComponentSetup T z L)
    (hn : (L.subgroupOf (involutionCentralizer z)).Normal)
    (heven : Even (Nat.card L)) (hZ : center L = ⊥)
    (gap : SylowOrderGap L K) (lift : InvolutionCenterLifting L K) :
    ExcludedSylowGeometry T L K := by
  have hTN := h.sylow_le_normalizer_of_normal hn
  obtain ⟨V, hcard, hVL, hVZ⟩ := exists_central_involution_subgroup h hTN heven
  obtain ⟨P, hP⟩ := exists_componentSylow_image h
  have hTV : (T : Subgroup G) ≤ normalizer (V : Set G) := by
    apply le_trans _ (centralizer_le_normalizer (V : Set G))
    intro t ht v hv
    obtain ⟨w, hw, he⟩ := hVZ hv
    have heq := congrArg Subtype.val (mem_center_iff.mp hw ⟨t, ht⟩)
    change t * (w : G) = (w : G) * t at heq
    change (w : G) = v at he
    rw [he] at heq
    exact heq.symm
  exact geometry_of_center_embedding hTN gap hTV
    (disjoint_commutingSylow_of_centerless hZ (hVL.trans inf_le_right))
    (lift P V (le_componentSylow_center hP hVL hVZ) hcard)

end CFSG.Quasithin.Chapter16.FourGroupTransfer.SylowModels
