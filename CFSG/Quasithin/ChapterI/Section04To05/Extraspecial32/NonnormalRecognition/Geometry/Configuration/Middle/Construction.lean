module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Configuration.Middle.LocalData
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Configuration.Middle.Construction.Split
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Configuration.Middle.Construction.Transport

/-!
# Construction of the local middle sixteen

The elementary-eight intersection and its complement identify its normalizer
with the genuine natural split extension E₈ ⋊ SL₃(2). A Sylow subgroup of
H = C_G(z) has order 64, so its image is Sylow in this block. Conjugate that
image to the standard Sylow subgroup. Its center has a unique nonidentity
element, which forces the given z to be the central root involution in these
coordinates. The marked transport then constructs every field of
`MiddleLocalData`, including the literal relative centralizer and normalizer.

No A₃ configuration, middle-subgroup witness, ambient fusion conclusion or
recognition theorem is used. Splitting is exactly the explicit input supplied
by the preceding source argument. This completes the local construction used
by `Middle.Control`; ambient fusion and normalizer-quotient assembly remain
with the enclosing source-theorem owner.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), Lemma 3.1 and its proof, printed p.36,
https://authors.library.caltech.edu/records/m3wrn-5w840/files/ASCijm03.pdf.
-/

public section

open Subgroup Matrix.PSL3Two Matrix.PSL3Two.SplitParabolic
namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Configuration
variable {G : Type*} [Group G] [Finite G] {z g : G}

/-- The local middle-sixteen geometry of source Lemma 3.1, constructed from the
split point normalizer. No A₃ configuration or ambient fusion conclusion is used. -/
theorem middle_local_data_of_point_split (h : Hypotheses z) (d : IntersectionData z g)
    (point_split : ∃ K : Subgroup (normalizer (coreIntersection z g : Set G)),
      IsComplement' ((coreIntersection z g).subgroupOf
        (normalizer (coreIntersection z g : Set G))) K) :
    Nonempty (MiddleLocalData z) := by
  classical
  let S : Sylow 2 (Centralizer z) := Classical.choice inferInstance
  let N := normalizer (coreIntersection z g : Set G)
  let T := middleSylowImage S
  have hHN : Centralizer z ≤ N := intersection_centralizer_le_normalizer d
  have hTH : T ≤ Centralizer z := map_subtype_le _
  have hTN : T ≤ N := hTH.trans hHN
  let U := T.subgroupOf N
  have hTc : Nat.card T = 64 := by
    rw [card_map_of_injective (Centralizer z).subtype_injective]
    exact h.centralizer_sylow_two_card S
  have hUc : Nat.card U = 64 :=
    (Nat.card_congr (subgroupOfEquivOfLe hTN).toEquiv).trans hTc
  let e₀ := (Construction.pointSplitData d point_split).blockEquiv
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
  let j : Block →* G := N.subtype.comp e.symm.toMonoidHom
  have hj : Function.Injective j := N.subtype_injective.comp e.symm.injective
  have hstd : standardSylow.map j = T := by
    rw [← heT, map_map]
    have hjc : j.comp e.toMonoidHom = N.subtype := by
      ext x
      exact congrArg Subtype.val (e.symm_apply_apply x)
    rw [hjc, map_subgroupOf_eq_of_le hTN]
  have hH : Centralizer z ≤ j.range := by
    intro x hx
    refine ⟨e ⟨x, hHN hx⟩, ?_⟩
    exact congrArg Subtype.val (e.symm_apply_apply ⟨x, hHN hx⟩)
  have hzT : z ∈ T := by
    have hcore : Core z ≤ (S : Subgroup (Centralizer z)) :=
      (IsPGroup.of_card (p := 2) (n := 5) h.core_card).le_sylow_of_normal S
    exact mem_map_of_mem (Centralizer z).subtype (hcore h.distinguished_mem_core)
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
      norm_num at ho
    · change k Unitriangular.z = z
      exact huz ▸ hu
  exact ⟨Construction.localDataOfEmbedding S j hj hstd hH hz⟩

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Configuration

end
