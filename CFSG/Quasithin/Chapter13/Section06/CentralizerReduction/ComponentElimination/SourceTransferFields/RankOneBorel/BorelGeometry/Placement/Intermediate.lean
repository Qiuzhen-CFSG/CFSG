module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry

/-!
# The invariant intermediate subgroup in the rank-one Borel argument

If the action kernel in KT is a two-group and the image of Baum(T) lies
in the image of K, pull back the image of K ∩ T. The kernel lies in T by
normality and the Sylow property, so this preimage lies in T. Its ambient
form is (K ∩ T) joined with the embedded kernel; hence the marked Borel
normalizes it. B.2.3 then gives both Thompson and Baumann normalization.

The action-image containment is an explicit premise, to be supplied by the
single-factor application of E.2.3(2). No normality in the whole ambient
simple group is asserted.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
13.6.18, printed p.931; E.2.3(2), pp.216–217; B.2.3(3–4), p.75.
-/

@[expose] public section

open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement
variable {G D : Type*} [Group G] [Group D] [Finite G]

omit [Finite G] in
private theorem thompson_le_baumann (S : Subgroup G) :
    elementaryAbelianMaxJ S ≤ ChapterB.baumann S := by
  refine le_inf (sSup_le fun _ hA => hA.1) ?_
  intro j hj a ha
  exact (((mem_omegaOneCenterAmbient_iff _ _).mp ha).2.2 j hj).symm

private theorem thompson_eq_of_intermediate (S Q : Subgroup G)
    (hJQ : elementaryAbelianMaxJ S ≤ Q) (hQS : Q ≤ S) :
    elementaryAbelianMaxJ S = elementaryAbelianMaxJ Q := by
  have hs := elementaryAbelianMaxOrder_le_and_j_le_of_eq Q S hQS
  have hl := elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le S Q hJQ
  have he := le_antisymm hs.1 hl.1
  exact le_antisymm (hl.2 he.symm) (hs.2 he)

omit [Finite G] in
private theorem normalizer_le_thompson (Q : Subgroup G) :
    normalizer (Q : Set G) ≤ normalizer (elementaryAbelianMaxJ Q : Set G) := by
  intro x hx
  rw [mem_normalizer_iff_map_conj_eq] at hx ⊢
  change Q.map (MulAut.conj x).toMonoidHom = Q at hx
  change (elementaryAbelianMaxJ Q).map (MulAut.conj x).toMonoidHom = _
  rw [← elementaryAbelianMaxJ_map_equiv (MulAut.conj x), hx]

theorem normalizations_of_intermediate (B S Q : Subgroup G)
    (hSQ : ChapterB.baumann S ≤ Q) (hQS : Q ≤ S)
    (hBQ : B ≤ normalizer (Q : Set G)) :
    B ≤ normalizer (elementaryAbelianMaxJ S : Set G) ∧
      B ≤ normalizer (ChapterB.baumann S : Set G) := by
  constructor
  · rw [thompson_eq_of_intermediate S Q ((thompson_le_baumann S).trans hSQ) hQS]
    exact hBQ.trans (normalizer_le_thompson Q)
  · rw [ChapterB.lemma_B_2_3_4 S Q hSQ hQS]
    exact hBQ.trans (normalizer_le_normalizer_baumann Q)

omit [Finite G] in
/-- Intersecting an image with the Sylow image is exact when the kernel lies
in the Sylow subgroup. No injectivity of the action is asserted. -/
theorem map_inf_of_kernel_le (f : G →* D) (K S : Subgroup G) (hk : f.ker ≤ S) :
    (K ⊓ S).map f = K.map f ⊓ S.map f := by
  apply le_antisymm (map_inf_le _ _ _)
  rintro _ ⟨⟨k, hkK, rfl⟩, s, hs, he⟩
  have hks : k⁻¹ * s ∈ f.ker := by
    change f (k⁻¹ * s) = 1
    rw [map_mul, map_inv, he, inv_mul_cancel]
  have hkS : k ∈ S := by
    have hh := S.mul_mem hs (S.inv_mem (hk hks))
    simpa only [mul_inv_rev, inv_inv, mul_inv_cancel_left] using hh
  exact ⟨k, ⟨hkK, hkS⟩, rfl⟩

/-- The explicit carrier is the full inverse image of the component Sylow
image, embedded in the original group. -/
def intermediate (K S : Subgroup G) (f : (K ⊔ S : Subgroup G) →* D) : Subgroup G :=
  ((((K ⊓ S).subgroupOf (K ⊔ S)).map f).comap f).map (K ⊔ S).subtype

omit [Finite G] in
theorem intermediate_eq (K S : Subgroup G) (f : (K ⊔ S : Subgroup G) →* D) :
    intermediate K S f = (K ⊓ S) ⊔ f.ker.map (K ⊔ S).subtype := by
  rw [intermediate, comap_map_eq, Subgroup.map_sup,
    map_subgroupOf_eq_of_le (inf_le_left.trans le_sup_left)]

omit [Finite G] in
theorem intermediate_spec (K S : Subgroup G)
    (hS : Chapter1.IsSylowIn 2 S (K ⊔ S))
    (f : (K ⊔ S : Subgroup G) →* D) (hk : IsPGroup 2 f.ker)
    (him : ((ChapterB.baumann S).subgroupOf (K ⊔ S)).map f ≤
      (K.subgroupOf (K ⊔ S)).map f) :
    ChapterB.baumann S ≤ intermediate K S f ∧
      intermediate K S f ≤ S ∧
      borel K S ≤ normalizer (intermediate K S f : Set G) := by
  let H := K ⊔ S
  have hker : f.ker ≤ S.subgroupOf H := by
    obtain ⟨P, hP⟩ := hS
    intro x hx
    change (x : G) ∈ S
    exact hP.le (mem_map_of_mem H.subtype (hk.le_sylow_of_normal P hx))
  have hkerG : f.ker.map H.subtype ≤ S := by
    simpa only [map_subgroupOf_eq_of_le (show S ≤ H from le_sup_right)] using
      map_mono (f := H.subtype) hker
  have hle : intermediate K S f ≤ S := by
    rw [intermediate_eq]
    exact sup_le inf_le_right hkerG
  have hB : ChapterB.baumann S ≤ intermediate K S f := by
    intro x hx
    have hxS : x ∈ S := hx.1
    let xH : H := ⟨x, (show S ≤ H from le_sup_right) hxS⟩
    have hxmap : f xH ∈ (K.subgroupOf H).map f ⊓ (S.subgroupOf H).map f :=
      ⟨him (mem_map_of_mem f hx), mem_map_of_mem f hxS⟩
    rw [← map_inf_of_kernel_le f _ _ hker] at hxmap
    exact mem_map.mpr ⟨xH, hxmap, rfl⟩
  refine ⟨hB, hle, ?_⟩
  have hNK : H ≤ normalizer (f.ker.map H.subtype : Set G) := by
    apply (normal_subgroupOf_iff_le_normalizer (map_subtype_le f.ker)).mp
    change ((f.ker.map H.subtype).comap H.subtype).Normal
    rw [comap_map_eq_self_of_injective H.subtype_injective]
    infer_instance
  intro b hb
  rw [intermediate_eq, mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
    mem_normalizer_iff_map_conj_eq.mp hb.2,
    mem_normalizer_iff_map_conj_eq.mp (hNK hb.1)]

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement

end
