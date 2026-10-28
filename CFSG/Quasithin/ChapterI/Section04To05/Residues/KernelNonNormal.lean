module

public import CFSG.Quasithin.ChapterI.Section04To05.Residues.SymmetricCoreJoin
public import Theory.GroupTheory.MinimalFourCoreKernel

/-!
# The point-core line kernel is not point-group invariant

The core-join identity gives [Q₀:Q₀∩Q₁]=2. If the point group normalized
this line kernel, it would fix all neighboring points and lie in Q₂.
The normal image of Q₀ in the plane parabolic would then have order at
most two. The actual PSL₃(2) parabolic core is irreducible of order four,
so this image vanishes. But Q₂ fixes the line points whereas Q₀ does not.

This is I.5.7(6), with the erroneous printed index [Q₁:Q₀∩Q₁]=2 replaced
by the correct index in Q₀ and the minimal-core argument just given.
-/

public noncomputable section
namespace Quasithin.I5.DSystem
open Subgroup
variable {G : Type*} [Group G] (S : DSystem .C3 G)

theorem point_line_kernel_card :
    Nat.card (S.Q 0) = Nat.card (S.Q 0 ⊓ S.Q 1 : Subgroup G) * 2 := by
  have h := S.core_card_product 0 1
  rw [← S.point_line_core_join] at h
  have hc := S.line_pair_core_card 0 (Or.inl rfl)
  have hc' : Nat.card ((S.pair 0 1).pCoreIn 2) = Nat.card (S.Q 1) * 2 := by
    simpa only [pair, inf_comm] using hc
  rw [hc'] at h
  let : Finite (S.Q 1) := Finite.of_injective
    (inclusion ((S.family 1).pCoreIn_le 2)) (inclusion_injective _)
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := S.Q 1))
  calc
    Nat.card (S.Q 0) * Nat.card (S.Q 1) = _ := h
    _ = (Nat.card (S.Q 0 ⊓ S.Q 1 : Subgroup G) * 2) * Nat.card (S.Q 1) := by ring

theorem point_core_not_le_lineCore : ¬ S.Q 0 ≤ S.Q 1 := by
  intro h
  have hc := S.point_line_kernel_card
  rw [inf_eq_left.mpr h] at hc
  let : Finite (S.Q 0) := Finite.of_injective
    (inclusion ((S.family 0).pCoreIn_le 2)) (inclusion_injective _)
  have hp := Nat.card_pos (α := S.Q 0)
  omega

theorem point_core_not_le_planeCore : ¬ S.Q 0 ≤ S.Q 2 := by
  intro h
  apply S.point_core_not_le_lineCore
  intro g hg
  have hk : g ∈ S.Q 0 ⊓ fixingSubgroup G {y : S.Point | S.Inc y S.baseLine} := by
    refine ⟨hg, (mem_fixingSubgroup_iff G).mpr ?_⟩
    intro y hy
    exact S.core_fixes_incident_coset 2 0 (by decide) (h hg)
      (CosetGeometry.Incident.symm S.family (S.point_line_plane hy
        (show S.Inc S.baseLine S.basePlane from ⟨1, rfl, rfl⟩)))
  rw [S.point_core_line_kernel] at hk
  exact hk.2

theorem point_line_kernel_not_normalized :
    ¬ S.family 0 ≤ normalizer (S.Q 0 ⊓ S.Q 1 : Subgroup G) := by
  intro hn
  let N := S.Q 0 ⊓ S.Q 1
  have hN2 : N ≤ S.Q 2 := by
    apply (S.le_neighborCore_of_normalized_line_kernel N inf_le_left hn ?_).trans
      S.neighborCore_le_planeCore
    change S.Q 0 ⊓ S.Q 1 ≤ _
    rw [← S.point_core_line_kernel]
    exact inf_le_right
  obtain ⟨e, he⟩ := S.plane_standard_quotientMark
  let f := S.pairQuotientMap 2 0 e
  have h0 : S.Q 0 ≤ S.pair 2 0 :=
    le_inf ((S.Q_le_T 0).trans (S.T_le 2)) ((S.family 0).pCoreIn_le 2)
  have hN : N ≤ S.pair 2 0 := inf_le_left.trans h0
  let Q := (S.Q 0).subgroupOf (S.pair 2 0)
  let R := N.subgroupOf (S.pair 2 0)
  let : Finite (S.pair 2 0) := Finite.of_injective
    (inclusion (show S.pair 2 0 ≤ S.family 2 from inf_le_left)) (inclusion_injective _)
  let : Q.Normal := (normal_subgroupOf_iff_le_normalizer h0).mpr
    (inf_le_right.trans (S.family_le_normalizer_Q 0))
  have hc : Nat.card Q = Nat.card R * 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe h0).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hN).toEquiv]
    exact S.point_line_kernel_card
  have hRk : R ≤ f.ker := by
    rw [S.pairQuotientMap_ker]
    exact fun a ha => hN2 ha
  have hdata : Nat.card (pCore 2
      ((localParabolic S.family 2 0).map (S.localQuotientMap 2 e))) = 4 ∧
      ∀ A : Subgroup ((localParabolic S.family 2 0).map (S.localQuotientMap 2 e)),
        A.Normal → A ≤ pCore 2 _ → A = ⊥ ∨ A = pCore 2 _ := by
    rcases he with he | he
    · rw [he.1]
      refine ⟨Matrix.PSL3Two.pointParabolic_core_data.2, ?_⟩
      intro A hn hA
      let := hn
      exact Matrix.PSL3Two.pointParabolic_normal_le_core A hA
    · rw [he.1]
      refine ⟨Matrix.PSL3Two.lineParabolic_core_data.2, ?_⟩
      intro A hn hA
      let := hn
      exact Matrix.PSL3Two.lineParabolic_normal_le_core A hA
  have hQ := f.normal_two_le_ker_of_index_two (S.pairQuotientMap_surjective 2 0 e)
    Q R (((S.family 0).isPGroup_pCoreIn 2).comap_subtype)
    (fun _ ha => ha.1) hRk hc hdata.1 hdata.2
  rw [S.pairQuotientMap_ker] at hQ
  apply S.point_core_not_le_planeCore
  intro g hg
  exact hQ (show (⟨g, h0 hg⟩ : S.pair 2 0) ∈ Q from hg)

end Quasithin.I5.DSystem
