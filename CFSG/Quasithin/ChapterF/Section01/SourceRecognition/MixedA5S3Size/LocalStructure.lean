module

public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.MixedA5S3Size.Basic
public import Theory.SpecificGroups.Alternating.FiveBorelOvergroups
public import Theory.SpecificGroups.Alternating.FiveTwoCoreExtension
public import Theory.GroupTheory.SylowNormalizerCommutingFamily

/-!
# The actual local structure of the mixed A₅/S₃ pair

Transporting Sylow normalizers through the literal two-core quotients gives
Borel indices five and three. The common Borel has order 3|S|, and the
parabolic orders are 15|S| and 9|S|. The cubic endpoint also makes the first
parabolic equal KS. Its faithful quotient action identifies its core quotient
with A₅ or S₅; consequently |S| is four or eight times its core order.

These are local consequences of corrected F.1.1. They retain the whole
Borel and allow S outside both factors. They do not bound the first core
or construct the mixed Borel recognition witness. Those whole-pair steps
remain with the mixed F.1.12 assembly.

Source: Aschbacher--Smith, F.1.1, F.1.12(I), and original 9.3.1,
printed pp.259, 262--264 and 732 of refs/quasithin.pdf.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source
variable {G : Type*} [Group G] [Finite G]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem a5_sylow_indices {H : Type*} [Group H] [Finite H]
    (e : (H ⧸ pCore 2 H) ≃* alternatingGroup (Fin 5)) (P : Sylow 2 H) :
    (normalizer (P : Set H)).index = 5 ∧ (P : Subgroup H).index = 15 := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 H := by
    ext x
    change e (QuotientGroup.mk' _ x) = 1 ↔ x ∈ pCore 2 H
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  have hkP : q.ker ≤ (P : Subgroup H) := by
    rw [hk]
    exact pCore_isPGroup.le_sylow_of_normal P
  let Q := P.mapSurjective hq
  have hN : (normalizer (Q : Set (alternatingGroup (Fin 5)))).index = 5 := by
    obtain ⟨i, hi⟩ :=
      Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_eq_stabilizer Q
    have hc : Nat.card (MulAction.stabilizer (alternatingGroup (Fin 5)) i) = 12 := by
      rw [Nat.card_eq_fintype_card]
      clear Q hi
      revert i
      decide +kernel
    have hm := (MulAction.stabilizer (alternatingGroup (Fin 5)) i).index_mul_card
    rw [hc, nat_card_alternatingGroup] at hm
    norm_num [Nat.factorial] at hm
    rw [hi]
    omega
  have hP : (Q : Subgroup (alternatingGroup (Fin 5))).index = 15 := by
    have hc : Nat.card Q = 4 := by
      rw [Q.card_eq_multiplicity, nat_card_alternatingGroup, Nat.card_fin]
      decide +kernel
    have hm := (Q : Subgroup (alternatingGroup (Fin 5))).index_mul_card
    rw [hc, nat_card_alternatingGroup] at hm
    norm_num [Nat.factorial] at hm
    omega
  constructor
  · change (normalizer ((P : Subgroup H) : Set H)).index = 5
    rw [← index_map_eq _ hq (hkP.trans (P : Subgroup H).le_normalizer)]
    change ((normalizer (P : Set H)).map q).index = 5
    rw [P.normalizer_map_surjective q hq]
    exact hN
  · rw [← index_map_eq _ hq hkP]
    exact hP

omit [Finite G] in
private theorem local_sylow_normalizer (h : HypothesisF11 L S) (i : Fin 2) :
    ∃ P : Sylow 2 (L i),
      (P : Subgroup (L i)).map (L i).subtype = S ⊓ L i ∧
      (normalizer (P : Set (L i))).map (L i).subtype = borel (L i) S := by
  obtain ⟨P, hP⟩ := h.sylow i
  refine ⟨P, hP, ?_⟩
  have hP' : (P : Subgroup (L i)) = (S ⊓ L i).subgroupOf (L i) := by
    apply map_injective (L i).subtype_injective
    rw [hP, map_subgroupOf_eq_of_le inf_le_right]
  change (normalizer ((P : Subgroup (L i)) : Set (L i))).map (L i).subtype = _
  rw [hP', ← subgroupOf_normalizer_eq (show S ⊓ L i ≤ L i from inf_le_right),
    subgroupOf_map_subtype]
  exact inf_comm _ _

/-- The A₅ endpoint has local Borel index five and local Sylow index fifteen. -/
theorem HypothesisF11.a5_borel_local_indices (h : HypothesisF11 L S) (i : Fin 2)
    (e : (L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)) :
    (borel (L i) S).relIndex (L i) = 5 ∧ S.relIndex (L i) = 15 := by
  obtain ⟨P, hP, hN⟩ := local_sylow_normalizer h i
  have htop : (⊤ : Subgroup (L i)).map (L i).subtype = L i := by
    rw [← MonoidHom.range_eq_map, range_subtype]
  have hn := relIndex_map_map_of_injective (normalizer (P : Set (L i))) ⊤
    (L i).subtype_injective
  have hp := relIndex_map_map_of_injective (P : Subgroup (L i)) ⊤
    (L i).subtype_injective
  rw [hN, htop, relIndex_top_right] at hn
  rw [hP, htop, inf_relIndex_right, relIndex_top_right] at hp
  exact ⟨hn.trans (a5_sylow_indices e P).1, hp.trans (a5_sylow_indices e P).2⟩

omit [Finite G] in
private theorem commonBorel_local_intersection (h : HypothesisF11 L S) (i : Fin 2) :
    commonBorel L S ⊓ L i = borel (L i) S := by
  rw [h.commonBorel_eq_normalizer i]
  apply le_antisymm
  · exact fun _ hx => ⟨hx.2, hx.1.2⟩
  · exact fun _ hx => ⟨⟨mem_sup_left (mem_sup_left hx.1), hx.2⟩, hx.1⟩

private theorem commonBorel_parabolic_index (h : HypothesisF11 L S) (i : Fin 2) :
    (commonBorel L S).relIndex (parabolic L S i) = (borel (L i) S).relIndex (L i) := by
  rw [parabolic_eq_sup_commonBorel,
    relIndex_sup_of_normalizes _ _ (h.commonBorel_normalizes_local i)]
  rw [← inf_relIndex_right (commonBorel L S) (L i), commonBorel_local_intersection h i]

/-- The literal mixed pair has Borel indices five and three in its parabolics. -/
theorem HypothesisF11.mixed_borel_parabolic_indices {K U : Subgroup G}
    (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) :
    (commonBorel ![K,U] S).relIndex (parabolic ![K,U] S 0) = 5 ∧
    (commonBorel ![K,U] S).relIndex (parabolic ![K,U] S 1) = 3 := by
  constructor
  · exact (commonBorel_parabolic_index h 0).trans (h.a5_borel_local_indices 0 eK).1
  · rw [commonBorel_parabolic_index h 1, h.cubic_borel_eq_localSylow 1 eU]
    obtain ⟨P, hP⟩ := (show ∃ P : Sylow 2 U,
      (P : Subgroup U).map U.subtype = S ⊓ U from h.sylow 1)
    have htop : (⊤ : Subgroup U).map U.subtype = U := by rw [← MonoidHom.range_eq_map, range_subtype]
    have hp := relIndex_map_map_of_injective (P : Subgroup U) ⊤ U.subtype_injective
    rw [hP, htop, relIndex_top_right] at hp
    exact hp.trans (SymmetricThreeTwoCore.sylow_index_three eU P)

/-- The whole mixed Borel retains a factor of three above the original S. -/
theorem HypothesisF11.mixed_sylow_borel_index {K U : Subgroup G}
    (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) :
    S.relIndex (commonBorel ![K,U] S) = 3 := by
  have hn : S ≤ normalizer (borel K S : Set G) := h.S_normalizes_borel 0
  rw [h.commonBorel_eq_of_cubic_second eU, relIndex_sup_of_normalizes _ _ hn]
  have hi : (borel K S).relIndex K = 5 ∧ S.relIndex K = 15 :=
    h.a5_borel_local_indices 0 eK
  have hm := relIndex_inf_mul_relIndex S (borel K S) K
  rw [inf_of_le_left (borel_le K S)] at hm
  have hinf : S ⊓ borel K S = S ⊓ K :=
    le_antisymm (inf_le_inf_left _ (borel_le _ _))
      (le_inf inf_le_left (localSylow_le_borel _ _))
  rw [hinf, inf_relIndex_right, hi.1, hi.2] at hm
  omega

/-- The first actual parabolic has core quotient A₅ or S₅, even when S is outside K. -/
theorem HypothesisF11.mixed_first_parabolic_quotient {K U S : Subgroup G}
    (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) :
    Nonempty ((parabolic ![K,U] S 0 ⧸ pCore 2 (parabolic ![K,U] S 0)) ≃*
      alternatingGroup (Fin 5)) ∨
    Nonempty ((parabolic ![K,U] S 0 ⧸ pCore 2 (parabolic ![K,U] S 0)) ≃*
      Equiv.Perm (Fin 5)) := by
  have he : parabolic ![K,U] S 0 = K ⊔ S := by
    change K ⊔ S ⊔ borel U S = K ⊔ S
    have hb : borel U S = S ⊓ U := h.cubic_borel_eq_localSylow 1 eU
    rw [hb]
    exact sup_eq_left.mpr (inf_le_left.trans le_sup_right)
  rw [he]
  exact Theory.SpecificGroups.Alternating.FiveExtensionAction.core_quotient_of_two_supplement K S (h.S_normalizes 0) h.S_isP eK


/-- The two possible indices of the first parabolic core. -/
theorem HypothesisF11.mixed_first_parabolic_core_index {K U : Subgroup G}
    (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) :
    (pCore 2 (parabolic ![K,U] S 0)).index = 60 ∨
      (pCore 2 (parabolic ![K,U] S 0)).index = 120 := by
  rw [index_eq_card]
  rcases h.mixed_first_parabolic_quotient eK eU with he | he
  · left
    rw [Nat.card_congr he.some.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  · right
    rw [Nat.card_congr he.some.toEquiv]
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

/-- The original overlap and parabolic orders, without recognizing the mixed pair. -/
theorem HypothesisF11.mixed_local_orders {K U : Subgroup G}
    (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) :
    Nat.card (commonBorel ![K,U] S) = 3 * Nat.card S ∧
    Nat.card (parabolic ![K,U] S 0) = 15 * Nat.card S ∧
    Nat.card (parabolic ![K,U] S 1) = 9 * Nat.card S := by
  have card_index (A B : Subgroup G) (hAB : A ≤ B) :
      Nat.card A * A.relIndex B = Nat.card B := by
    simpa only [relIndex_bot_left] using
      relIndex_mul_relIndex (⊥ : Subgroup G) A B bot_le hAB
  have hB := card_index S (commonBorel ![K,U] S) le_sup_right
  have hP := card_index (commonBorel ![K,U] S) (parabolic ![K,U] S 0)
    (commonBorel_le_parabolic 0)
  have hQ := card_index (commonBorel ![K,U] S) (parabolic ![K,U] S 1)
    (commonBorel_le_parabolic 1)
  rw [h.mixed_sylow_borel_index eK eU] at hB
  rw [(h.mixed_borel_parabolic_indices eK eU).1] at hP
  rw [(h.mixed_borel_parabolic_indices eK eU).2] at hQ
  omega

/-- The exact weighted core sizes controlling the original Sylow order. -/
theorem HypothesisF11.mixed_first_core_size_cases {K U : Subgroup G}
    (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) :
    let Q := pCore 2 (parabolic ![K,U] S 0)
    (Q.index = 60 ∧ Nat.card S = 4 * Nat.card Q) ∨
      (Q.index = 120 ∧ Nat.card S = 8 * Nat.card Q) := by
  let Q := pCore 2 (parabolic ![K,U] S 0)
  change (Q.index = 60 ∧ Nat.card S = 4 * Nat.card Q) ∨
    (Q.index = 120 ∧ Nat.card S = 8 * Nat.card Q)
  have hc := Q.index_mul_card
  rw [(h.mixed_local_orders eK eU).2.1] at hc
  rcases h.mixed_first_parabolic_core_index eK eU with hi | hi
  · exact Or.inl ⟨hi, by change Q.index = 60 at hi; rw [hi] at hc; omega⟩
  · exact Or.inr ⟨hi, by change Q.index = 120 at hi; rw [hi] at hc; omega⟩

end CFSG.Quasithin.ChapterF.Source
