module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.NonseedEight
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PointCoreE8Count
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PointCoreSeedCoverage
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Data.Set.Card.Arithmetic
public import Mathlib.Algebra.Pointwise.Stabilizer

/-!
# The two elementary-eight orbits in the original point core

The five original seeds partition the noncentral point-core involutions.
An elementary eight outside this seed orbit meets three seeds in planes.
The full five-point action bounds its stabilizer; the intrinsic elementary-
eight census then supplies the exact second orbit and normalizer order.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

private local instance pointCoreSubgroupAction :
    MulAction (involutionCentralizer z) (Subgroup G) :=
  MulAction.compHom (Subgroup G) (MulAut.conj.comp (involutionCentralizer z).subtype)

/-- The literal conjugates of the seed under its marked involution centralizer. -/
@[expose] def pointCoreSeedOrbit (z : G) (V : Subgroup G) : Set (Subgroup G) :=
  Set.range fun g : involutionCentralizer z => V.map (MulAut.conj (g : G)).toMonoidHom

omit [Finite G] in
private theorem seedOrbit_eq_orbit : pointCoreSeedOrbit z V =
    MulAction.orbit (involutionCentralizer z) V := rfl

omit [Finite G] in
private theorem subgroup_stabilizer (E : Subgroup G) :
    MulAction.stabilizer (involutionCentralizer z) E =
      (normalizer (E : Set G)).subgroupOf (involutionCentralizer z) := by
  ext g
  change E.map (MulAut.conj (g : G)).toMonoidHom = E ↔
    (g : G) ∈ normalizer (E : Set G)
  exact mem_normalizer_iff_map_conj_eq.symm

/-- The original marked centralizer has exactly five seed conjugates. -/
theorem TypeAt.point_core_seed_orbit_card (h : TypeAt z V) :
    (pointCoreSeedOrbit z V).ncard = 5 := by
  rw [seedOrbit_eq_orbit]
  have hc := Nat.card_congr
    (MulAction.orbitProdStabilizerEquivGroup (involutionCentralizer z) V)
  rw [Nat.card_prod, subgroup_stabilizer, ← card_subtype, subgroupOf_map_subtype,
    inf_comm, h.local_intersection_card, h.centralizer_card] at hc
  change (MulAction.orbit (involutionCentralizer z) V).ncard * 1536 = 7680 at hc
  omega

private theorem seed_labeling (h : TypeAt z V) :
    ∃ (f : involutionCentralizer z →* Equiv.Perm (Fin 5))
      (S : Fin 5 → Subgroup G), Function.Surjective f ∧
      f.ker = pCore 2 (involutionCentralizer z) ∧ Function.Injective S ∧
      Set.range S = pointCoreSeedOrbit z V ∧
      ∀ (g : involutionCentralizer z) (i : Fin 5), S (f g i) = g • S i := by
  classical
  obtain ⟨f, i, hf, hk, hi⟩ := h.exists_overlap_five_marking
  have hex (j : Fin 5) : ∃ g : involutionCentralizer z, f g i = j := by
    obtain ⟨g, hg⟩ := hf (Equiv.swap i j)
    exact ⟨g, by rw [hg]; simp⟩
  choose rep hrep using hex
  let S : Fin 5 → Subgroup G := fun j => rep j • V
  have hsame (g k : involutionCentralizer z) : g • V = k • V ↔ f g i = f k i := by
    have hs : (k⁻¹ * g) • V = V ↔ f (k⁻¹ * g) i = i := by
      change k⁻¹ * g ∈ MulAction.stabilizer (involutionCentralizer z) V ↔ _
      rw [subgroup_stabilizer, hi]
      rfl
    simp only [mul_smul, inv_smul_eq_iff, map_mul, map_inv, Equiv.Perm.mul_apply] at hs
    change (g • V = k • V ↔ (f k).symm (f g i) = i) at hs
    exact hs.trans (Equiv.symm_apply_eq (f k))
  refine ⟨f, S, hf, hk, ?_, ?_, ?_⟩
  · intro j k he
    have hh := (hsame (rep j) (rep k)).mp he
    simpa only [hrep] using hh
  · ext E
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨rep j, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨f g i, (hsame _ _).mpr (hrep _)⟩
  · intro g j
    change rep (f g j) • V = g • (rep j • V)
    rw [← mul_smul]
    apply (hsame _ _).mpr
    rw [hrep, map_mul, Equiv.Perm.mul_apply, hrep]

private theorem pointCore_eight_conjugate (_h : TypeAt z V) (E : pointCoreEights z)
    (g : involutionCentralizer z) :
    g • E.val ≤ (involutionCentralizer z).pCoreIn 2 ∧ z ∈ g • E.val ∧
      IsElementaryAbelian 2 (g • E.val : Subgroup G) ∧
      Nat.card (g • E.val : Subgroup G) = 8 := by
  let : IsElementaryAbelian 2 E.val := E.property.2.2.1
  refine ⟨?_, ?_, IsElementaryAbelian.map _, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨xH, hxH, rfl⟩ := E.property.1 hx
    exact ⟨g * xH * g⁻¹,
      (inferInstance : (pCore 2 (involutionCentralizer z)).Normal).conj_mem _ hxH g, rfl⟩
  · refine ⟨z, E.property.2.1, ?_⟩
    change (g : G) * z * (g : G)⁻¹ = z
    rw [mem_centralizer_singleton_iff.mp g.property, mul_inv_cancel_right]
  · change Nat.card (E.val.map (MulAut.conj (g : G)).toMonoidHom) = 8
    rw [card_map_of_injective (MulAut.conj (g : G)).injective, E.property.2.2.2]

private theorem seed_member (h : TypeAt z V) {E : Subgroup G}
    (hE : E ∈ pointCoreSeedOrbit z V) :
    E ≤ (involutionCentralizer z).pCoreIn 2 ∧ z ∈ E ∧
      IsElementaryAbelian 2 E ∧ Nat.card E = 8 := by
  obtain ⟨g, rfl⟩ := hE
  have hVQ : V ≤ (involutionCentralizer z).pCoreIn 2 := by
    change V ≤ (pCore 2 (involutionCentralizer z)).map (involutionCentralizer z).subtype
    rw [← h.centralizer_fitting]
    exact h.seed_le_core
  exact pointCore_eight_conjugate h
    ⟨V, hVQ, h.involution_mem_seed, h.elementary, h.seed_card⟩ g

/-- Distinct literal seeds in the original centralizer orbit meet in the
marked involution line. -/
theorem TypeAt.point_core_seed_pair_intersection (h : TypeAt z V) {E F : Subgroup G}
    (hE : E ∈ pointCoreSeedOrbit z V) (hF : F ∈ pointCoreSeedOrbit z V)
    (hne : E ≠ F) : E ⊓ F = zpowers z := by
  obtain ⟨g, rfl⟩ := hE
  obtain ⟨k, rfl⟩ := hF
  have hn : ((g⁻¹ * k : involutionCentralizer z) : G) ∉ normalizer (V : Set G) := by
    intro hh
    have he : (g⁻¹ * k) • V = V := mem_normalizer_iff_map_conj_eq.mp hh
    have he' := congrArg (fun E : Subgroup G => g • E) he
    simp only [← mul_smul, mul_inv_cancel_left] at he'
    exact hne he'.symm
  have hi := h.seed_conjugate_intersection (g⁻¹ * k)
    (g⁻¹ * k).property hn
  have hh := congrArg (fun E : Subgroup G => g • E) hi
  have hz : g • zpowers z = zpowers z := by
    change (zpowers z).map (MulAut.conj (g : G)).toMonoidHom = _
    rw [MonoidHom.map_zpowers]
    congr 1
    change (g : G) * z * (g : G)⁻¹ = z
    rw [mem_centralizer_singleton_iff.mp g.property, mul_inv_cancel_right]
  change (g • V : Subgroup G) ⊓ (k • V) = _
  change g • (V ⊓ ((g⁻¹ * k) • V)) = g • zpowers z at hh
  rw [show g • (V ⊓ ((g⁻¹ * k) • V)) = g • V ⊓ g • ((g⁻¹ * k) • V) from
    map_inf _ _ _ (MulAut.conj (g : G)).injective] at hh
  simpa only [← mul_smul, mul_inv_cancel_left, hz] using hh

private theorem nonseed_intersection_card (h : TypeAt z V)
    (E : pointCoreEights z) (hEn : E.val ∉ pointCoreSeedOrbit z V)
    (S : Subgroup G) (hS : S ∈ pointCoreSeedOrbit z V) :
    Nat.card (E.val ⊓ S : Subgroup G) = 2 ∨
      Nat.card (E.val ⊓ S : Subgroup G) = 4 := by
  have hSm := seed_member h hS
  have hlo : 2 ≤ Nat.card (E.val ⊓ S : Subgroup G) := by
    have hh := card_le_of_le (zpowers_le.mpr
      (show z ∈ E.val ⊓ S from ⟨E.property.2.1, hSm.2.1⟩))
    simpa only [Nat.card_zpowers, h.involution] using hh
  have hd : Nat.card (E.val ⊓ S : Subgroup G) ∣ 8 := by
    simpa only [E.property.2.2.2] using card_dvd_of_le
      (show E.val ⊓ S ≤ E.val from inf_le_left)
  have hc := (Nat.mem_divisors (m := 8) (n := Nat.card (E.val ⊓ S : Subgroup G))).mpr
    ⟨hd, by decide⟩
  rw [show Nat.divisors 8 = {1, 2, 4, 8} from by decide] at hc
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc
  have hn8 : Nat.card (E.val ⊓ S : Subgroup G) ≠ 8 := by
    intro hc8
    have hES : E.val ⊓ S = E.val := eq_of_le_of_card_ge inf_le_left
      (by rw [hc8, E.property.2.2.2])
    have hEeq : E.val = S := eq_of_le_of_card_ge
      (hES ▸ (show E.val ⊓ S ≤ S from inf_le_right))
      (by rw [E.property.2.2.2, hSm.2.2.2])
    exact hEn (hEeq.symm ▸ hS)
  omega

private theorem nonseed_signature_card (h : TypeAt z V)
    (E : pointCoreEights z) (hEn : E.val ∉ pointCoreSeedOrbit z V)
    (S : Fin 5 → Subgroup G) (hSi : Function.Injective S)
    (hSr : Set.range S = pointCoreSeedOrbit z V) :
    (Finset.univ.filter fun i => Nat.card (E.val ⊓ S i : Subgroup G) = 4).card = 3 := by
  classical
  let U : Fin 5 → Set G := fun i => (E.val ⊓ S i : Set G) \ (zpowers z : Set G)
  have hS (i : Fin 5) : S i ∈ pointCoreSeedOrbit z V := hSr ▸ Set.mem_range_self i
  have hzS (i : Fin 5) : z ∈ S i := (seed_member h (hS i)).2.1
  have hU (i : Fin 5) : (U i).ncard =
      if Nat.card (E.val ⊓ S i : Subgroup G) = 4 then 2 else 0 := by
    have hh := Set.ncard_sdiff_add_ncard_of_subset (show (zpowers z : Set G) ⊆
      (E.val ⊓ S i : Set G) from (show zpowers z ≤ E.val ⊓ S i from
        zpowers_le.mpr ⟨E.property.2.1, hzS i⟩))
    change (U i).ncard + Nat.card (zpowers z) = Nat.card (E.val ⊓ S i : Subgroup G) at hh
    rw [Nat.card_zpowers, h.involution] at hh
    rcases nonseed_intersection_card h E hEn (S i) (hS i) with hc | hc
    · rw [hc, if_neg (by decide)]
      omega
    · rw [hc, if_pos rfl]
      omega
  have hd : Pairwise (fun i j => Disjoint (U i) (U j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hh : x ∈ S i ⊓ S j := ⟨hx.1.2, hy.1.2⟩
    rw [h.point_core_seed_pair_intersection (hS i) (hS j) (hSi.ne hij)] at hh
    exact hx.2 hh
  have hu : (⋃ i, U i) = (E.val : Set G) \ (zpowers z : Set G) := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hx⟩ := Set.mem_iUnion.mp hx
      exact ⟨hx.1.1, hx.2⟩
    · rintro ⟨hxE, hxz⟩
      have hx1 : x ≠ 1 := fun he => hxz (he ▸ (zpowers z).one_mem)
      let : IsElementaryAbelian 2 E.val := E.property.2.2.1
      have hx2 : orderOf x = 2 := orderOf_eq_prime
        (elemPow_eq_one_of_isElementaryAbelian x hxE) hx1
      obtain ⟨g, hxg⟩ := h.centralizer_core_involution_seed_conjugate x
        (E.property.1 hxE) hx2
      obtain ⟨i, hi⟩ := hSr.symm ▸ (show V.map (MulAut.conj (g : G)).toMonoidHom ∈
        pointCoreSeedOrbit z V from ⟨g, rfl⟩)
      apply Set.mem_iUnion.mpr
      exact ⟨i, ⟨⟨hxE, hi.symm ▸ hxg⟩, hxz⟩⟩
  have hout : ((E.val : Set G) \ (zpowers z : Set G)).ncard = 6 := by
    have hh := Set.ncard_sdiff_add_ncard_of_subset
      (show (zpowers z : Set G) ⊆ (E.val : Set G) from zpowers_le.mpr E.property.2.1)
    change _ + Nat.card (zpowers z) = Nat.card E.val at hh
    rw [Nat.card_zpowers, h.involution, E.property.2.2.2] at hh
    omega
  have hsum := Set.ncard_iUnion_of_finite (fun i => Set.toFinite (U i)) hd
  rw [hu, hout, finsum_eq_sum_of_fintype] at hsum
  simp_rw [hU] at hsum
  have hs : (∑ i : Fin 5, if Nat.card (E.val ⊓ S i : Subgroup G) = 4 then 2 else 0) =
      (Finset.univ.filter fun i => Nat.card (E.val ⊓ S i : Subgroup G) = 4).card * 2 := by
    simp only [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
  omega


private theorem five_triple_certificate : ∀ T : Finset (Fin 5), T.card = 3 →
    Fintype.card {g : Equiv.Perm (Fin 5) // ∀ i, g i ∈ T ↔ i ∈ T} = 12 := by
  decide +kernel

private theorem five_triple_stabilizer_card (T : Finset (Fin 5)) (hT : T.card = 3) :
    Nat.card (MulAction.stabilizer (Equiv.Perm (Fin 5)) (T : Set (Fin 5))) = 12 := by
  classical
  let e : MulAction.stabilizer (Equiv.Perm (Fin 5)) (T : Set (Fin 5)) ≃
      {g : Equiv.Perm (Fin 5) // ∀ i, g i ∈ T ↔ i ∈ T} :=
    Equiv.subtypeEquivRight fun g => MulAction.mem_stabilizer_set
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  exact five_triple_certificate T hT

private theorem nonseed_marking (h : TypeAt z V) (E : pointCoreEights z)
    (hEn : E.val ∉ pointCoreSeedOrbit z V) :
    ∃ (f : involutionCentralizer z →* Equiv.Perm (Fin 5))
      (S : Fin 5 → Subgroup G) (T : Finset (Fin 5)),
      Function.Surjective f ∧ f.ker = pCore 2 (involutionCentralizer z) ∧
      Function.Injective S ∧ Set.range S = pointCoreSeedOrbit z V ∧
      (∀ (g : involutionCentralizer z) (i : Fin 5), S (f g i) = g • S i) ∧
      T = Finset.univ.filter (fun i => Nat.card (E.val ⊓ S i : Subgroup G) = 4) ∧
      T.card = 3 ∧
      ((normalizer (E.val : Set G)).subgroupOf (involutionCentralizer z)).map f ≤
        MulAction.stabilizer (Equiv.Perm (Fin 5)) (T : Set (Fin 5)) := by
  classical
  obtain ⟨f, S, hf, hk, hSi, hSr, hSe⟩ := seed_labeling h
  let T := Finset.univ.filter (fun i => Nat.card (E.val ⊓ S i : Subgroup G) = 4)
  refine ⟨f, S, T, hf, hk, hSi, hSr, hSe, rfl,
    nonseed_signature_card h E hEn S hSi hSr, ?_⟩
  rintro _ ⟨g, hg, rfl⟩
  apply MulAction.mem_stabilizer_set.mpr
  intro i
  change f g i ∈ T ↔ i ∈ T
  simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
  have hgE : g • E.val = E.val := mem_normalizer_iff_map_conj_eq.mp hg
  have hc : Nat.card (E.val ⊓ S (f g i) : Subgroup G) =
      Nat.card (E.val ⊓ S i : Subgroup G) := by
    rw [hSe, ← hgE]
    change Nat.card (E.val.map (MulAut.conj (g : G)).toMonoidHom ⊓
      (S i).map (MulAut.conj (g : G)).toMonoidHom : Subgroup G) = _
    rw [← map_inf _ _ _ (MulAut.conj (g : G)).injective,
      card_map_of_injective (MulAut.conj (g : G)).injective]
    rw [hgE]
  rw [hc]

private theorem nonseed_normalizer_bound (h : TypeAt z V) (E : pointCoreEights z)
    (hEn : E.val ∉ pointCoreSeedOrbit z V) :
    Nat.card ((normalizer (E.val : Set G)).subgroupOf (involutionCentralizer z)) ≤ 768 := by
  obtain ⟨f, S, T, hf, hk, hSi, hSr, hSe, hT, hTc, hN⟩ := nonseed_marking h E hEn
  let N := (normalizer (E.val : Set G)).subgroupOf (involutionCentralizer z)
  have hNc : Nat.card (N.map f) ≤ 12 := by
    exact (card_le_of_le hN).trans_eq (five_triple_stabilizer_card T hTc)
  have hk64 : Nat.card f.ker = 64 := by
    rw [hk, ← h.centralizer_fitting]
    exact h.centralizer_core_card
  have hkc : Nat.card (f.ker.subgroupOf N) ≤ 64 := by
    rw [← card_subtype N (f.ker.subgroupOf N), subgroupOf_map_subtype]
    exact (card_le_of_le (show f.ker ⊓ N ≤ f.ker from inf_le_left)).trans_eq hk64
  have hh := (f.ker.subgroupOf N).card_mul_index
  change Nat.card (f.ker.subgroupOf N) * f.ker.relIndex N = Nat.card N at hh
  rw [relIndex_ker] at hh
  calc
    Nat.card N = Nat.card (f.ker.subgroupOf N) * Nat.card (N.map f) := hh.symm
    _ ≤ 64 * 12 := Nat.mul_le_mul hkc hNc
    _ = 768 := by decide

private theorem nonseed_orbit_data (h : TypeAt z V) (E : pointCoreEights z)
    (hEn : E.val ∉ pointCoreSeedOrbit z V) :
    (MulAction.orbit (involutionCentralizer z) E.val).ncard = 10 ∧
      Nat.card ((normalizer (E.val : Set G)).subgroupOf (involutionCentralizer z)) = 768 ∧
      {F : Subgroup G | F ≤ (involutionCentralizer z).pCoreIn 2 ∧ z ∈ F ∧
        IsElementaryAbelian 2 F ∧ Nat.card F = 8} =
        MulAction.orbit (involutionCentralizer z) E.val ∪ pointCoreSeedOrbit z V := by
  let X : Set (Subgroup G) := {F | F ≤ (involutionCentralizer z).pCoreIn 2 ∧ z ∈ F ∧
    IsElementaryAbelian 2 F ∧ Nat.card F = 8}
  let O := MulAction.orbit (involutionCentralizer z) E.val
  have hd : Disjoint O (pointCoreSeedOrbit z V) := by
    apply Set.disjoint_left.mpr
    rintro F ⟨g, hg⟩ ⟨k, hk⟩
    apply hEn
    refine ⟨g⁻¹ * k, ?_⟩
    change (g⁻¹ * k) • V = E.val
    change k • V = F at hk
    rw [mul_smul, hk, ← hg, inv_smul_smul]
  have hsub : O ∪ pointCoreSeedOrbit z V ⊆ X := by
    rintro F (hF | hF)
    · obtain ⟨g, rfl⟩ := hF
      exact pointCore_eight_conjugate h E g
    · exact seed_member h hF
  have hcount : X.ncard ≤ 15 := h.point_core_eights_count
  have hupper : O.ncard ≤ 10 := by
    have hh := (Set.ncard_le_ncard hsub).trans hcount
    rw [Set.ncard_union_eq hd, h.point_core_seed_orbit_card] at hh
    omega
  have hbound := nonseed_normalizer_bound h E hEn
  have hc := Nat.card_congr
    (MulAction.orbitProdStabilizerEquivGroup (involutionCentralizer z) E.val)
  rw [Nat.card_prod, subgroup_stabilizer, h.centralizer_card] at hc
  change O.ncard * Nat.card
    ((normalizer (E.val : Set G)).subgroupOf (involutionCentralizer z)) = 7680 at hc
  have hlower : 10 ≤ O.ncard := by nlinarith
  have hO : O.ncard = 10 := by omega
  have hN : Nat.card ((normalizer (E.val : Set G)).subgroupOf
      (involutionCentralizer z)) = 768 := by rw [hO] at hc; omega
  refine ⟨hO, hN, ?_⟩
  apply (Set.eq_of_subset_of_ncard_le hsub ?_).symm
  rw [Set.ncard_union_eq hd, h.point_core_seed_orbit_card, hO]
  exact hcount

/-- Every two elementary eights outside the five original seeds are
conjugate under the original marked involution centralizer. -/
theorem TypeAt.point_core_nonseed_eights_transitive (h : TypeAt z V)
    (E F : pointCoreEights z)
    (hEn : E.val ∉ pointCoreSeedOrbit z V) (hFn : F.val ∉ pointCoreSeedOrbit z V) :
    ∃ g : involutionCentralizer z,
      E.val.map (MulAut.conj (g : G)).toMonoidHom = F.val := by
  have hf : F.val ∈ MulAction.orbit (involutionCentralizer z) E.val ∪
      pointCoreSeedOrbit z V := (nonseed_orbit_data h E hEn).2.2 ▸ F.property
  exact hf.resolve_right hFn

/-- The literal centralizer-normalizer intersection of a nonseed elementary
eight has order768. -/
theorem TypeAt.point_core_nonseed_eight_normalizer_card (h : TypeAt z V)
    (E : pointCoreEights z) (hEn : E.val ∉ pointCoreSeedOrbit z V) :
    Nat.card (involutionCentralizer z ⊓ normalizer (E.val : Set G) : Subgroup G) = 768 := by
  have hh := (nonseed_orbit_data h E hEn).2.1
  rw [← card_subtype, subgroupOf_map_subtype, inf_comm] at hh
  exact hh

/-- Exactly fifteen elementary eights in the original point core contain
the marked involution. -/
theorem TypeAt.point_core_eights_card (h : TypeAt z V) :
    Nat.card (pointCoreEights z) = 15 := by
  obtain ⟨E, hEQ, hzE, hEE, hE8, _, hEn⟩ := h.exists_nonseed_point_core_eight
  let E' : pointCoreEights z := ⟨E, hEQ, hzE, hEE, hE8⟩
  have hn : E'.val ∉ pointCoreSeedOrbit z V := by
    rintro ⟨g, hg⟩
    exact hEn g hg.symm
  have ho := nonseed_orbit_data h E' hn
  change ({F : Subgroup G | F ≤ (involutionCentralizer z).pCoreIn 2 ∧ z ∈ F ∧
    IsElementaryAbelian 2 F ∧ Nat.card F = 8} : Set (Subgroup G)).ncard = 15
  rw [ho.2.2, Set.ncard_union_eq]
  · rw [ho.1, h.point_core_seed_orbit_card]
  · apply Set.disjoint_left.mpr
    rintro F ⟨g, hg⟩ ⟨k, hk⟩
    apply hn
    refine ⟨g⁻¹ * k, ?_⟩
    change (g⁻¹ * k) • V = E'.val
    change k • V = F at hk
    rw [mul_smul, hk, ← hg, inv_smul_smul]

/-- The nonseed normalizer is the full inverse image of the stabilizer of
its three intersecting original seeds. The labeling is equivariant for
literal ambient conjugation and retains the actual intersection signature. -/
theorem TypeAt.point_core_nonseed_eight_marking (h : TypeAt z V)
    (E : pointCoreEights z) (hEn : E.val ∉ pointCoreSeedOrbit z V) :
    ∃ (f : involutionCentralizer z →* Equiv.Perm (Fin 5))
      (S : Fin 5 → Subgroup G) (T : Finset (Fin 5)),
      Function.Surjective f ∧ f.ker = pCore 2 (involutionCentralizer z) ∧
      Function.Injective S ∧ Set.range S = pointCoreSeedOrbit z V ∧
      (∀ (g : involutionCentralizer z) (i : Fin 5),
        S (f g i) = (S i).map (MulAut.conj (g : G)).toMonoidHom) ∧
      T = Finset.univ.filter (fun i => Nat.card (E.val ⊓ S i : Subgroup G) = 4) ∧
      T.card = 3 ∧
      (normalizer (E.val : Set G)).subgroupOf (involutionCentralizer z) =
        (MulAction.stabilizer (Equiv.Perm (Fin 5)) (T : Set (Fin 5))).comap f ∧
      ((normalizer (E.val : Set G)).subgroupOf (involutionCentralizer z)).map f =
        MulAction.stabilizer (Equiv.Perm (Fin 5)) (T : Set (Fin 5)) := by
  classical
  obtain ⟨f, S, T, hf, hk, hSi, hSr, hSe, hT, hTc, hN⟩ := nonseed_marking h E hEn
  let D := MulAction.stabilizer (Equiv.Perm (Fin 5)) (T : Set (Fin 5))
  let N := (normalizer (E.val : Set G)).subgroupOf (involutionCentralizer z)
  have hNc : Nat.card N = 768 := (nonseed_orbit_data h E hEn).2.1
  have hDc : Nat.card D = 12 := five_triple_stabilizer_card T hTc
  have hDi : D.index = 10 := by
    have hh := D.card_mul_index
    rw [hDc, Nat.card_perm, show Nat.card (Fin 5) = 5 from by simp] at hh
    norm_num [Nat.factorial] at hh
    omega
  have hCi : (D.comap f).index = 10 := by
    rw [index_comap_of_surjective _ hf, hDi]
  have hCc : Nat.card (D.comap f) = 768 := by
    have hh := (D.comap f).card_mul_index
    rw [hCi, h.centralizer_card] at hh
    omega
  have he : N = D.comap f := eq_of_le_of_card_ge
    (map_le_iff_le_comap.mp hN) (by rw [hNc, hCc])
  refine ⟨f, S, T, hf, hk, hSi, hSr, hSe, hT, hTc, he, ?_⟩
  change N.map f = D
  rw [he, map_comap_eq_self_of_surjective hf]

end CFSG.Quasithin.HigmanSims
