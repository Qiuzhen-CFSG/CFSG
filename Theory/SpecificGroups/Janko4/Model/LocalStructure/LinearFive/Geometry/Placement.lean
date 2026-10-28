module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Geometry.SharpImages.Transport
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Geometry.IntersectionNormalizer

/-!
# Global F-occurrences in D lie in Q

The sharp Mathieu image theorem gives an actual pointwise octad kernel. Its
transitive action on the complementary sixteen points forces that octad to be
the octad defining D. A self-centralizing F-conjugate cannot lie inside E, so
every global F-conjugate contained in D lies in Q. Conjugators are arbitrary
ambient model elements throughout; no E- or Q-orbit exhaustion is assumed.

Source: Kleidman--Wilson (1988), Lemma 1.1.2(ii), p.485.
-/
@[expose] public noncomputable section
namespace Janko4.LocalStructure.LinearFive.Geometry
open Subgroup Cardinality
open Sporadic.Mathieu M24LocalGeometry MathieuCode
open scoped Pointwise
attribute [local irreducible] modelGroup matrixA matrixB localKernel max1Subgroup

/-- An octad invariant under a whole octad kernel is that octad itself. -/
theorem octad_eq_of_kernel_le_stabilizer (O P : Octad)
    (h : octadPointwiseKernel O ≤ octadStabilizer P) : O = P := by
  have hle : P.val ⊆ O.val := by
    intro x hx
    by_contra hxo
    have hcomp : Finset.univ \ O.val ⊆ P.val := by
      intro y hy
      have hyo := (Finset.mem_sdiff.mp hy).2
      obtain ⟨g,hg⟩ := octad_kernel_transitive O x y hxo hyo
      have he : g.val • P.val = P.val := h g.property
      rw [← hg, ← he]
      exact Finset.smul_mem_smul_finset hx
    have hc := Finset.card_le_card hcomp
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
      Fintype.card_fin, m24Blocks_card _ O.property, m24Blocks_card _ P.property] at hc
    omega
  apply Subtype.ext
  exact (Finset.eq_of_subset_of_card_le hle (by
    rw [m24Blocks_card _ O.property, m24Blocks_card _ P.property])).symm

private def movedOctad (g : M24) (O : Octad) : Octad :=
  ⟨g • O.val, by
    have h := (mem_M24_iff g.val).mp g.property
    change g.val • O.val ∈ (m24Blocks : Set (Finset (Fin 24)))
    rw [← h]
    exact Set.smul_mem_smul_set O.property⟩

/-- Every large elementary subgroup outside E has a full native octad-kernel image. -/
theorem local_large_image_is_octad (H : Subgroup M) [IsElementaryAbelian 2 H]
    (hne : ¬ H ≤ localKernel matrixA_mul_self matrixB_pow_four)
    (hcard : 1024 ≤ Nat.card H) :
    ∃ P : Octad, H.map projection = octadPointwiseKernel P := by
  obtain ⟨g,hg⟩ := SharpImages.local_large_image_eq_octad H hne hcard
  let P := movedOctad (projection g)⁻¹ SharpImages.exceptionalOctad
  refine ⟨P, ?_⟩
  have hm := congrArg (fun K : Subgroup M24 =>
    K.map (MulAut.conj (projection g)⁻¹).toMonoidHom) hg
  rw [octad_kernel_map _ P _ rfl] at hm
  have he : (((H.map (MulAut.conj g).toMonoidHom).map projection).map
      (MulAut.conj (projection g)⁻¹).toMonoidHom) = H.map projection := by
    rw [map_map, map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    change (projection g)⁻¹ * projection (g*x*g⁻¹) * ((projection g)⁻¹)⁻¹ = projection x
    rw [map_mul, map_mul, map_inv]
    group
  exact he.symm.trans hm

/-- In the literal D container, the sharp image must be the original octad kernel. -/
theorem local_large_in_D_image (H : Subgroup M) [IsElementaryAbelian 2 H]
    (hD : H ≤ (octadStabilizer O).comap projection)
    (hne : ¬ H ≤ localKernel matrixA_mul_self matrixB_pow_four)
    (hcard : 1024 ≤ Nat.card H) : H.map projection = A := by
  obtain ⟨P,hP⟩ := local_large_image_is_octad H hne hcard
  have hk : octadPointwiseKernel P ≤ octadStabilizer O := by
    rw [← hP]
    exact map_le_iff_le_comap.mpr hD
  exact hP.trans (congrArg octadPointwiseKernel (octad_eq_of_kernel_le_stabilizer P O hk))

/-- Actual elementary subgroups in D of order at least 1024, outside E, lie in Q. -/
theorem large_in_D_le_Q (H : Subgroup Model) [IsElementaryAbelian 2 H]
    (hD : H ≤ D) (hne : ¬ H ≤ E) (hcard : 1024 ≤ Nat.card H) : H ≤ Q := by
  have hM := hD.trans D_le_M
  let : IsElementaryAbelian 2 (H.subgroupOf M) := IsElementaryAbelian.subgroupOf hM
  have hc : Nat.card (H.subgroupOf M) = Nat.card H :=
    Nat.card_congr (subgroupOfEquivOfLe hM).toEquiv
  have hl : H.subgroupOf M ≤ (octadStabilizer O).comap projection := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hD hx
    exact (Subtype.ext he : y = x) ▸ hy
  have hn : ¬ H.subgroupOf M ≤ localKernel matrixA_mul_self matrixB_pow_four := by
    intro he
    apply hne
    intro x hx
    exact mem_map.mpr ⟨⟨x,hM hx⟩,he hx,rfl⟩
  have hi := local_large_in_D_image (H.subgroupOf M) hl hn (by simpa only [hc] using hcard)
  intro x hx
  refine mem_map.mpr ⟨⟨x,hM hx⟩, ?_, rfl⟩
  change projection ⟨x,hM hx⟩ ∈ A
  rw [← hi]
  exact mem_map.mpr ⟨⟨x,hM hx⟩,hx,rfl⟩

/-- Every global F-conjugate in D lies in Q; no E/Q conjugator is assumed. -/
theorem global_conjugate_in_D_le_Q (g : Model)
    (hD : F.map (MulAut.conj g).toMonoidHom ≤ D) :
    F.map (MulAut.conj g).toMonoidHom ≤ Q := by
  let H := F.map (MulAut.conj g).toMonoidHom
  let := F_elementary
  let : IsElementaryAbelian 2 H := IsElementaryAbelian.map _
  have hc : Nat.card H = 1024 := by
    rw [card_map_of_injective (MulAut.conj g).injective, F_card]
  have hC : centralizer (H : Set Model) = H := by
    let e := MulAut.conj g
    apply le_antisymm
    · intro x hx
      refine mem_map.mpr ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      rw [← centralizer_F]
      intro y hy
      apply e.injective
      simpa only [map_mul, e.apply_symm_apply] using hx (e y) (mem_map_of_mem _ hy)
    · exact H.le_centralizer
  apply large_in_D_le_Q H hD ?_ hc.ge
  intro hE
  have : IsElementaryAbelian 2 E := by
    let := localKernel_elementary matrixA_mul_self matrixB_pow_four
    exact IsElementaryAbelian.map M.subtype
  have hEH : E ≤ H := by
    rw [← hC]
    exact E.le_centralizer.trans (centralizer_le hE)
  have he := le_antisymm hE hEH
  have hec : Nat.card E = 2048 := by
    rw [card_map_of_injective M.subtype_injective, localKernel_card]
  rw [he, hec] at hc
  omega

end Janko4.LocalStructure.LinearFive.Geometry
