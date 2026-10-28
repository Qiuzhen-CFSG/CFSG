module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.MathieuLocalSections.Placement.Reduction
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Mathlib.FieldTheory.Finite.Basic
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.MathieuLocalSections.Placement.Intransitivity.AlternatingIndices

/-!
# Intransitivity of normalized L₄(2) joins in M₂₄

Let H = ⟨B,S⟩, with S normalizing B and B/O₂(B) isomorphic to L₄(2).
Normalization gives B normal in H and [H:B] a power of two. If H were
transitive on the native 24 points, a point stabilizer K would have index
24. The relative index formula shows that [B:K ∩ B] divides 24 and is
divisible by three. Passing to B/O₂(B) only removes a power-of-two factor,
so the image of K ∩ B still has index dividing 24 and divisible by three.

Field transport and the actual exceptional isomorphism L₄(2) ≅ A₈ give
an A₈ subgroup with the same index. `AlternatingIndices` excludes it.
The Sylow normalization is an explicit input here; the placement assembly
supplies that separate local-component argument.

Source: Aschbacher–Smith, A.3.12(14), printed pp.47–48; the sporadic
Sylow-overgroup calculation cited there, and GLS3, Table 5.3e.
-/

namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.MathieuLocalSections

open Subgroup

private theorem relIndex_mul_sup_index {G : Type*} [Group G] [Finite G]
    (K N : Subgroup G) [N.Normal] :
    K.relIndex N * (K ⊔ N).index = K.index := by
  have hKN := relIndex_mul_index (show K ⊓ N ≤ N from inf_le_right)
  have hNK := relIndex_mul_index (show K ⊓ N ≤ K from inf_le_left)
  rw [inf_relIndex_right] at hKN
  rw [inf_relIndex_left] at hNK
  have hN := relIndex_mul_index (show N ≤ K ⊔ N from le_sup_right)
  rw [relIndex_sup_right] at hN
  apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (index_ne_zero_of_finite (H := N.subgroupOf K)))
  calc
    N.relIndex K * (K.relIndex N * (K ⊔ N).index) =
        K.relIndex N * (N.relIndex K * (K ⊔ N).index) := by ac_rfl
    _ = K.relIndex N * N.index := by rw [hN]
    _ = N.relIndex K * K.index := hKN.trans hNK.symm

private theorem three_not_dvd_two_power_divisor {d n : ℕ} (hd : d ∣ 2 ^ n) : ¬ 3 ∣ d := by
  intro h3
  have : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 3) (h3.trans hd)
  norm_num at this

private theorem normal_subgroup_index {G : Type*} [Group G] [Finite G]
    (K N : Subgroup G) [N.Normal] (hN : ∃ n : ℕ, N.index = 2 ^ n)
    (hK : K.index = 24) :
    (K.subgroupOf N).index ∣ 24 ∧ 3 ∣ (K.subgroupOf N).index := by
  have ht := relIndex_mul_sup_index K N
  rw [hK] at ht
  have hd : (K ⊔ N).index ∣ N.index := index_dvd_of_le le_sup_right
  obtain ⟨n, hn⟩ := hN
  rw [hn] at hd
  constructor
  · exact ⟨(K ⊔ N).index, ht.symm⟩
  · have h3 : 3 ∣ K.relIndex N * (K ⊔ N).index := by rw [ht]; decide
    exact ((Nat.Prime.dvd_mul (by decide : Nat.Prime 3)).mp h3).resolve_right
      (three_not_dvd_two_power_divisor hd)

private theorem quotient_subgroup_index {G : Type*} [Group G] [Finite G]
    (K N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
    (hK : K.index ∣ 24) (h3 : 3 ∣ K.index) :
    (K.map (QuotientGroup.mk' N)).index ∣ 24 ∧
      3 ∣ (K.map (QuotientGroup.mk' N)).index := by
  have hi : (K.map (QuotientGroup.mk' N)).index = (K ⊔ N).index := by
    rw [index_map, QuotientGroup.ker_mk', MonoidHom.range_eq_top.mpr
      (QuotientGroup.mk'_surjective N), index_top, mul_one]
  rw [hi]
  constructor
  · exact (index_dvd_of_le le_sup_left).trans hK
  · have ht := relIndex_mul_sup_index K N
    rw [← ht] at h3
    have hd := K.relIndex_dvd_card N
    obtain ⟨n, hn⟩ := hN.exists_card_eq
    rw [hn] at hd
    exact ((Nat.Prime.dvd_mul (by decide : Nat.Prime 3)).mp h3).resolve_left
      (three_not_dvd_two_power_divisor hd)


open CFSG.Quasithin.Chapter1
open Sporadic.Mathieu
open scoped MatrixGroups

private theorem sectionEquiv {G : Type*} [Group G]
    (h : ClassicalGroup.IsPSL G 4 2) : Nonempty (G ≃* alternatingGroup (Fin 8)) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
  exact ⟨e.trans ((Atlas.fieldEquivPSL 4 eF).trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8)⟩

/-- A normalized join of a source L₄(2) section with an ambient Sylow
 two-subgroup cannot be transitive on the actual 24 Mathieu points. -/
public theorem normalizedJoinIntransitivity : NormalizedJoinIntransitivity := by
  intro B S hB hn ht
  let H := B ⊔ S.toSubgroup
  let C := B.subgroupOf H
  let : MulAction.IsPretransitive H (Fin 24) := ht
  let : C.Normal := normal_subgroupOf_of_le_normalizer (sup_le B.le_normalizer hn)
  let K := MulAction.stabilizer H (0 : Fin 24)
  have hK : K.index = 24 := by
    simpa using MulAction.index_stabilizer_of_transitive (G := H) (0 : Fin 24)
  have hC : ∃ n : ℕ, C.index = 2 ^ n := normalized_join_index_two_power B S hn
  obtain ⟨hd, h3⟩ := normal_subgroup_index K C hC hK
  let e : C ≃* B := subgroupOfEquivOfLe (show B ≤ H from le_sup_left)
  let J : Subgroup B := (K.subgroupOf C).map e.toMonoidHom
  have hJ : J.index = (K.subgroupOf C).index := index_map_of_bijective e.bijective _
  obtain ⟨hqd, hq3⟩ := quotient_subgroup_index J (pCore 2 B) pCore_isPGroup
    (hJ ▸ hd) (hJ ▸ h3)
  obtain ⟨f⟩ := sectionEquiv hB
  let U := (J.map (QuotientGroup.mk' (pCore 2 B))).map f.toMonoidHom
  have hU : U.index = (J.map (QuotientGroup.mk' (pCore 2 B))).index :=
    index_map_of_bijective f.bijective _
  exact Intransitivity.alternatingEight_index_not_three_dvd U (hU ▸ hqd) (hU ▸ hq3)

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.MathieuLocalSections
