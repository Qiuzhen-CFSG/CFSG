module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.LocalSubgroups.Definitions
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer

/-!
# The order and kernel of the derived F-normalizer

The normalizer of F has order 1920. Its stabilizer of the marked involution
has order 128, so conjugation is transitive on the fifteen nonidentity
elements of F. Each stabilizer is a two-group; hence an order-three actor
fixes only 1 on F. This reuses the stabilizer argument of
`FusedNine/IntersectionFixedPoints.lean` at a public interface needed here.

The common actor consequently puts F in `(N(F))'`. The genuine quotient
map `N(F) → S5` sends the derived subgroup onto A5, and its kernel F already
lies in that derived subgroup. Therefore the derived subgroup is exactly the
preimage of A5 and has order `16 * 60 = 960`. The same quotient puts the
common actor, and hence all of EQ*, inside it.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 8, Lemma 17, pp.16--17, using the Section 2
F-normalizer structure; DOI 10.1016/0021-8693(68)90002-1.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.LocalSubgroups
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

omit [Finite G] in
/-- The split F-normalizer has order 1920. -/
public theorem normalizer_F_card (L : LocalAnalysisData D k) :
    Nat.card (normalizer (CaseII.F D k : Set G)) = 1920 := by
  obtain ⟨K, hK, ⟨eK⟩⟩ := L.normalizer_F
  have hR : Nat.card ((CaseII.F D k).subgroupOf
      (normalizer (CaseII.F D k : Set G))) = 16 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (CaseII.F D k).le_normalizer).toEquiv,
      CaseII.F_card]
  have hC : Nat.card K = 120 := by
    rw [Nat.card_congr eK.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
    decide
  rw [← hK.card_mul_card, hR, hC]

/-- Every order-three element of N(F) fixes only the identity on F. -/
public theorem F_three_fixed_point_free (L : LocalAnalysisData D k)
    (x : G) (hxF : x ∈ normalizer (CaseII.F D k : Set G)) (hx : orderOf x = 3) :
    ∀ f ∈ CaseII.F D k, Commute x f → f = 1 := by
  let N := normalizer (CaseII.F D k : Set G)
  let z : CaseII.F D k := ⟨D.z, by
    rw [← CaseII.into_z_zero D k, ← CaseII.modelF_map D k]
    exact mem_map_of_mem _ CaseII.modelF_generators.1⟩
  have hz : z ≠ 1 := fun h => D.z_ne_one (congrArg Subtype.val h)
  have hstab : MulAction.stabilizer N z =
      (N ⊓ D.centralizer).subgroupOf N := by
    ext n
    rw [MulAction.mem_stabilizer_iff, Subtype.ext_iff]
    change (n : G) * D.z * (n : G)⁻¹ = D.z ↔
      (n : G) ∈ N ∧ (n : G) ∈ D.centralizer
    rw [mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
    exact ⟨fun h => ⟨n.property, h⟩, fun h => h.2⟩
  have hstabcard : Nat.card (MulAction.stabilizer N z) = 128 := by
    rw [hstab, Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv,
      CaseII.normalizer_F_inf_centralizer]
    exact (Nat.card_congr ((CaseII.caseIISylow D k).equiv D.sylow).toEquiv).trans
      D.sylow_card
  have horbitsub : MulAction.orbit N z ⊆ ({1}ᶜ : Set (CaseII.F D k)) := by
    intro f hf hf1
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hf
    exact hz ((MulAction.injective g) (by simpa using hf1))
  have horbit : MulAction.orbit N z = ({1}ᶜ : Set (CaseII.F D k)) := by
    apply Set.eq_of_subset_of_ncard_le horbitsub
    have hc := (MulAction.stabilizer N z).card_mul_index
    rw [hstabcard, MulAction.index_stabilizer, normalizer_F_card D k L] at hc
    rw [Set.ncard_compl, Set.ncard_singleton, CaseII.F_card]
    omega
  intro f hf hxf
  by_contra hf1
  let fF : CaseII.F D k := ⟨f, hf⟩
  have hfO : fF ∈ MulAction.orbit N z := by
    rw [horbit]
    exact fun h => hf1 (congrArg Subtype.val h)
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hfO
  have hfcard : Nat.card (MulAction.stabilizer N fF) = 128 := by
    rw [← Nat.card_congr (MulAction.stabilizerEquivStabilizer hg.symm).toEquiv,
      hstabcard]
  let q : N := ⟨x, hxF⟩
  have hq : q ∈ MulAction.stabilizer N fF := by
    apply MulAction.mem_stabilizer_iff.mpr
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr hxf.eq
  have hq3 : orderOf q = 3 := (orderOf_coe q).symm.trans hx
  have hd := (MulAction.stabilizer N fF).orderOf_dvd_natCard hq
  rw [hq3, hfcard] at hd
  norm_num at hd


/-- The same common actor puts F inside the derived F-normalizer. -/
public theorem F_le_X (L : LocalAnalysisData D k) (w : FusedNineIntersectionActor D k) :
    CaseII.F D k ≤ X D k :=
  le_commutator_of_fixedPointFree (CaseII.F D k) (normalizer (CaseII.F D k : Set G))
    le_normalizer w.actor w.normalizes_F w.normalizes_F
    (F_three_fixed_point_free D k L w.actor w.normalizes_F w.actor_order)

/-- An actual S5 quotient map identifies the derived normalizer with the preimage of A5. -/
public theorem exists_FNormalizerProjection (L : LocalAnalysisData D k)
    (w : FusedNineIntersectionActor D k) :
    ∃ f : normalizer (CaseII.F D k : Set G) →* Equiv.Perm (Fin 5),
      Function.Surjective f ∧
      f.ker = (CaseII.F D k).subgroupOf (normalizer (CaseII.F D k : Set G)) ∧
      _root_.commutator (normalizer (CaseII.F D k : Set G)) =
        (alternatingGroup (Fin 5)).comap f := by
  let N := normalizer (CaseII.F D k : Set G)
  let R := (CaseII.F D k).subgroupOf N
  obtain ⟨K, hK, ⟨eK⟩⟩ := L.normalizer_F
  let e : N ⧸ R ≃* Equiv.Perm (Fin 5) := hK.symm.QuotientMulEquiv.trans eK
  let f : N →* Equiv.Perm (Fin 5) := e.toMonoidHom.comp (QuotientGroup.mk' R)
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective R)
  have hker : f.ker = R := by
    ext x
    change e (QuotientGroup.mk' R x) = 1 ↔ x ∈ R
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  have hR : R ≤ _root_.commutator N := by
    intro x hx
    have h := F_le_X D k L w hx
    rw [X_eq_map_commutator] at h
    obtain ⟨y, hy, he⟩ := h
    exact (Subtype.val_injective he) ▸ hy
  have hm : (_root_.commutator N).map f = alternatingGroup (Fin 5) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hf]
    exact alternatingGroup.commutator_perm_eq (by simp)
  refine ⟨f, hf, hker, ?_⟩
  rw [← hm]
  exact (comap_map_eq_self (hker ▸ hR)).symm

/-- The actual derived subgroup of N(F) has order 960. -/
public theorem X_card (L : LocalAnalysisData D k) (w : FusedNineIntersectionActor D k) :
    Nat.card (X D k) = 960 := by
  let N := normalizer (CaseII.F D k : Set G)
  let R := (CaseII.F D k).subgroupOf N
  let C := _root_.commutator N
  obtain ⟨f, hf, hker, hC⟩ := exists_FNormalizerProjection D k L w
  change C = (alternatingGroup (Fin 5)).comap f at hC
  have hR : R ≤ C := by
    rw [hC]
    intro x hx
    change f x ∈ alternatingGroup (Fin 5)
    have hxker : x ∈ f.ker := hker ▸ hx
    rw [MonoidHom.mem_ker.mp hxker]
    exact one_mem _
  have hRC : Nat.card (R.subgroupOf C) = 16 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hR).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe (CaseII.F D k).le_normalizer).toEquiv,
      CaseII.F_card]
  have hmap : C.map f = alternatingGroup (Fin 5) := by
    rw [hC, map_comap_eq_self]
    rw [MonoidHom.range_eq_top.mpr hf]
    exact le_top
  have hmapcard : Nat.card (C.map f) = 60 := by
    rw [hmap, nat_card_alternatingGroup]
    norm_num
  have hi := relIndex_ker C f
  rw [hker] at hi
  have hm := (R.subgroupOf C).card_mul_index
  change Nat.card (R.subgroupOf C) * R.relIndex C = Nat.card C at hm
  rw [hi, hRC, hmapcard] at hm
  rw [X_eq_map_commutator, card_map_of_injective Subtype.val_injective]
  exact hm.symm

/-- The source common order-three actor lies in the derived F-normalizer. -/
public theorem actor_mem_X (L : LocalAnalysisData D k) (w : FusedNineIntersectionActor D k) :
    w.actor ∈ X D k := by
  let N := normalizer (CaseII.F D k : Set G)
  let q : N := ⟨w.actor, w.normalizes_F⟩
  obtain ⟨f, hf, hker, hC⟩ := exists_FNormalizerProjection D k L w
  have hq : q ∈ _root_.commutator N := by
    rw [hC]
    change f q ∈ alternatingGroup (Fin 5)
    apply Equiv.Perm.mem_alternatingGroup.mpr
    have h3 : (Equiv.Perm.sign (f q)) ^ 3 = 1 := by
      rw [← map_pow, ← map_pow]
      have hq3 : q ^ 3 = 1 := by
        apply Subtype.ext
        exact w.actor_order ▸ pow_orderOf_eq_one w.actor
      rw [hq3, map_one, map_one]
    have h2 : (Equiv.Perm.sign (f q)) ^ 2 = 1 := by
      simp [pow_two, Int.units_mul_self]
    simpa only [pow_succ, h2, one_mul] using h3
  rw [X_eq_map_commutator]
  exact mem_map_of_mem _ hq

/-- The whole Frobenius subgroup EQ* lies in the derived F-normalizer. -/
public theorem B_le_X (L : LocalAnalysisData D k) (w : FusedNineIntersectionActor D k) :
    B D k w ≤ X D k :=
  sup_le (E_le_X_of_actor D k w) (zpowers_le.mpr (actor_mem_X D k L w))

end Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.LocalSubgroups
