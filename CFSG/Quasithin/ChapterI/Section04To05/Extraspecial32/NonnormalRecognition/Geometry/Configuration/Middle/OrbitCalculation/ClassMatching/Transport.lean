module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Configuration.Middle.OrbitCalculation.Contracts
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Configuration.Middle.Construction.Split
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Configuration.Middle.Construction.Model
public import Theory.GroupTheory.SylowKernelCore

/-!
# Marked coordinates for the endpoint-normalizer class calculation

Starting with the genuine splitting of N_G(E), conjugate the image of the
chosen Sylow subgroup of H to the standard unitriangular subgroup. Uniqueness
of its elementary sixteen identifies A with the middle radical. Its central
involution identifies H with the point preimage, and intrinsic two-core
transport identifies the literal embedded Q with that point preimage's core.
The splitting projection and normality preserve the literal E as the
translation kernel throughout. In particular, the intersection A ∩ E has
order four.

No A₃ configuration or ambient fusion assertion is used. These coordinates
feed the class-preserving matching in the parent `ClassMatching` module.
Source: M. Aschbacher, “A 2-local characterization of M12”, Lemmas 2.6(3)
and 3.1, printed pp.35–37,
https://authors.library.caltech.edu/records/m3wrn-5w840/files/ASCijm03.pdf.
-/

@[expose] public section
open Subgroup Matrix.PSL3Two Matrix.PSL3Two.SplitParabolic
namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Configuration.OrbitCalculation.ClassMatching
variable {G : Type*} [Group G] [Finite G] {z g : G}

structure MarkedCoordinates (z g : G) (A : Subgroup G) where
  equiv : endpointNormalizer z g ≃* Block
  kernel : ((coreIntersection z g).subgroupOf (endpointNormalizer z g)).map
    equiv.toMonoidHom = projection.ker
  middle : (A.subgroupOf (endpointNormalizer z g)).map equiv.toMonoidHom = middleGroup
  core : ((coreInG z).subgroupOf (endpointNormalizer z g)).map equiv.toMonoidHom =
    pointPreimage.pCoreIn 2

private theorem splitData_kernel {L : Type*} [Group L] {V : Subgroup L} [V.Normal]
    (s : SplitNaturalData V) : V.map s.blockEquiv.toMonoidHom = projection.ker := by
  ext b
  obtain ⟨x, rfl⟩ := s.blockEquiv.surjective b
  simp only [mem_map_equiv, MulEquiv.symm_apply_apply, MonoidHom.mem_ker,
    s.blockEquiv_projection, MulEquiv.map_eq_one_iff]
  exact (QuotientGroup.eq_one_iff x).symm

/-- Coordinates preserve the actual endpoint kernel, middle subgroup, and intrinsic core. -/
theorem exists_markedCoordinates (h : Hypotheses z) (d : IntersectionData z g)
    (m : MiddleLocalData z)
    (point_split : ∃ K : Subgroup (normalizer (coreIntersection z g : Set G)),
      IsComplement' ((coreIntersection z g).subgroupOf
        (normalizer (coreIntersection z g : Set G))) K) :
    Nonempty (MarkedCoordinates z g m.A) := by
  classical
  let N := endpointNormalizer z g
  let T := middleSylowImage m.S
  have hHN : Centralizer z ≤ N := intersection_centralizer_le_normalizer d
  have hTH : T ≤ Centralizer z := map_subtype_le _
  have hTN : T ≤ N := hTH.trans hHN
  have hAN : m.A ≤ N := m.A_le_centralizer.trans hHN
  let U := T.subgroupOf N
  have hTc : Nat.card T = 64 := by
    rw [card_map_of_injective (Centralizer z).subtype_injective]
    exact h.centralizer_sylow_two_card m.S
  have hUc : Nat.card U = 64 :=
    (Nat.card_congr (subgroupOfEquivOfLe hTN).toEquiv).trans hTc
  let s := Construction.pointSplitData d point_split
  let e₀ := s.blockEquiv
  let P : Sylow 2 Block := Sylow.ofCard (U.map e₀.toMonoidHom) (by
    rw [card_map_of_injective e₀.injective, hUc,
      SemidirectProduct.card, card_E3, card_SL]
    decide +kernel)
  obtain ⟨b, hb⟩ := MulAction.exists_smul_eq Block P naturalSylow
  let e : N ≃* Block := e₀.trans (MulAut.conj b)
  have heT : U.map e.toMonoidHom = standardSylow := by
    change U.map ((MulAut.conj b).toMonoidHom.comp e₀.toMonoidHom) = _
    rw [← map_map]
    exact congrArg (fun S : Sylow 2 Block => (S : Subgroup Block)) hb
  have heE : ((coreIntersection z g).subgroupOf N).map e.toMonoidHom =
      projection.ker := by
    change ((coreIntersection z g).subgroupOf N).map
      ((MulAut.conj b).toMonoidHom.comp s.blockEquiv.toMonoidHom) = _
    rw [← map_map, splitData_kernel]
    exact Normal.map_conj_eq projection.ker b
  have heA : (m.A.subgroupOf N).map e.toMonoidHom = middleGroup := by
    let := m.elementary
    let : IsElementaryAbelian 2 (m.A.subgroupOf N) :=
      IsElementaryAbelian.subgroupOf hAN
    apply elementary_sixteen_eq_middle_of_le_standardSylow _ (IsElementaryAbelian.map _)
    · rw [card_map_of_injective e.injective,
        Nat.card_congr (subgroupOfEquivOfLe hAN).toEquiv, m.card]
    · rw [← heT]
      exact map_mono (fun _ hx => m.A_le_sylow hx)
  let j : Block →* G := N.subtype.comp e.symm.toMonoidHom
  have hj : Function.Injective j := N.subtype_injective.comp e.symm.injective
  have hstd : standardSylow.map j = T := by
    rw [← heT, map_map]
    have hjc : j.comp e.toMonoidHom = N.subtype := by
      ext x
      exact congrArg Subtype.val (e.symm_apply_apply x)
    rw [hjc, map_subgroupOf_eq_of_le hTN]
  have hzT : z ∈ T := m.A_le_sylow m.distinguished_mem
  let k := j.comp sylowMap
  have hk : Function.Injective k := hj.comp sylowMap_injective
  have hkrange : k.range = T := by
    rw [MonoidHom.range_comp, sylowMap_range]
    exact hstd
  obtain ⟨u, hu⟩ := hkrange ▸ hzT
  have huc : u ∈ center Unitriangular.T := by
    apply mem_center_iff.mpr
    intro v
    apply hk
    simp only [map_mul, hu]
    exact mem_centralizer_singleton_iff.mp
      (hTH (hkrange ▸ (show k v ∈ k.range from ⟨v, rfl⟩)))
  have hz : j (sylowMap Unitriangular.z) = z := by
    rcases ConstructionModel.center_cases u huc with hu1 | huz
    · rw [hu1, map_one] at hu
      have ho := h.involution
      rw [← hu, orderOf_one] at ho
      omega
    · change k Unitriangular.z = z
      exact huz ▸ hu
  have heH : ((Centralizer z).subgroupOf N).map e.toMonoidHom = pointPreimage := by
    apply eq_of_le_of_card_ge
    · rintro x ⟨n, hn, rfl⟩
      apply ConstructionModel.marked_centralizer_le_point
      apply mem_centralizer_singleton_iff.mpr
      apply hj
      have hje : j (e n) = n := congrArg Subtype.val (e.symm_apply_apply n)
      simp only [map_mul]
      change j (e n) * j (sylowMap Unitriangular.z) =
        j (sylowMap Unitriangular.z) * j (e n)
      rw [hz, hje]
      exact mem_centralizer_singleton_iff.mp hn
    · rw [card_map_of_injective e.injective,
        Nat.card_congr (subgroupOfEquivOfLe hHN).toEquiv,
        h.centralizer_card, card_pointPreimage]
  have hQ : coreInG z = (Centralizer z).pCoreIn 2 := by
    change (Core z).map (Centralizer z).subtype = _
    rw [h.core_eq_pCore]
    rfl
  have hQN : (coreInG z).subgroupOf N = ((Centralizer z).subgroupOf N).pCoreIn 2 := by
    apply map_injective N.subtype_injective
    rw [map_subgroupOf_eq_of_le ((coreInG_le z).trans hHN),
      map_pCoreIn_of_injective 2 _ _ N.subtype_injective,
      map_subgroupOf_eq_of_le hHN, hQ]
  refine ⟨⟨e, heE, heA, ?_⟩⟩
  rw [hQN, map_pCoreIn_of_injective 2 _ _ e.injective, heH]

omit [Finite G] in
/-- The exact four-point intersection required by the fusion-count contract. -/
theorem plane_card (d : IntersectionData z g) (m : MiddleLocalData z)
    (coords : MarkedCoordinates z g m.A) :
    Nat.card (m.A ⊓ coreIntersection z g : Subgroup G) = 4 := by
  let N := endpointNormalizer z g
  have hAN : m.A ≤ N := m.A_le_centralizer.trans (intersection_centralizer_le_normalizer d)
  have he : ((m.A ⊓ coreIntersection z g).subgroupOf N).map
      coords.equiv.toMonoidHom = middleGroup ⊓ projection.ker := by
    change ((m.A.subgroupOf N) ⊓ ((coreIntersection z g).subgroupOf N)).map _ = _
    rw [map_inf _ _ _ coords.equiv.injective, coords.middle, coords.kernel]
  have hc := card_middle_inf_ker
  rw [← he, card_map_of_injective coords.equiv.injective,
    Nat.card_congr (subgroupOfEquivOfLe (inf_le_left.trans hAN)).toEquiv] at hc
  exact hc

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Configuration.OrbitCalculation.ClassMatching
end
