module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Configuration.Middle.LocalData
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Configuration.Middle.Construction.Model

/-!
# Transport of the marked split-block Sylow geometry

An injective map from the genuine split block identifies its standard Sylow
subgroup with a Sylow subgroup of C_G(z), and takes the central root involution
to z. The ambient centralizer is contained in the image. Under these precise
conditions, the middle sixteen has all the local properties needed in source
Lemma 3.1. Its relative normalizer is the intersection of the point and line
stabilizers; its centralizer, squares, uniqueness and center follow from the
unitriangular coordinates. `Construction` constructs and discharges every one
of these embedding premises from the split point normalizer.
Source: Aschbacher, “A 2-local characterization of M12”, Lemma 3.1, p.36.
-/

public section

open Subgroup Matrix.PSL3Two Matrix.PSL3Two.SplitParabolic
open scoped IsMulCommutative
namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Configuration.Construction
variable {G : Type*} [Group G] [Finite G] {z : G}

/-- Transport the unitriangular geometry along an actual embedding of the split
block whose standard Sylow subgroup is a Sylow subgroup of the given centralizer. -/
noncomputable def localDataOfEmbedding
    (S : Sylow 2 (Centralizer z)) (j : Block →* G) (hj : Function.Injective j)
    (hT : standardSylow.map j = middleSylowImage S)
    (hH : Centralizer z ≤ j.range)
    (hz : j (sylowMap Unitriangular.z) = z) : MiddleLocalData z := by
  let T := middleSylowImage S
  change standardSylow.map j = T at hT
  let A := middleGroup.map j
  let k := j.comp sylowMap
  have hk : Function.Injective k := hj.comp sylowMap_injective
  have hkrange : k.range = T := by
    rw [MonoidHom.range_comp, sylowMap_range]
    exact hT
  have hAm : Unitriangular.A.map k = A := by
    rw [← map_map, middle_image]
  have hAelem : IsElementaryAbelian 2 A := by
    rw [← hAm]
    exact IsElementaryAbelian.map k
  have hAcard : Nat.card A = 16 := by
    rw [← hAm, card_map_of_injective hk, Unitriangular.card_A]
  have hAT : A ≤ T := by
    rw [← hkrange, ← hAm]
    exact map_le_range k Unitriangular.A
  have hkT (u : Unitriangular.T) : k u ∈ T := hkrange ▸ (show k u ∈ k.range from ⟨u, rfl⟩)
  have hTH : T ≤ Centralizer z := map_subtype_le _
  have hnorm : Centralizer z ⊓ normalizer (A : Set G) = T := by
    apply le_antisymm
    · intro x hx
      obtain ⟨b, rfl⟩ := hH hx.1
      have hbz : b ∈ centralizer ({sylowMap Unitriangular.z} : Set Block) := by
        apply mem_centralizer_singleton_iff.mpr
        apply hj
        simpa only [map_mul, hz] using mem_centralizer_singleton_iff.mp hx.1
      have hbn : b ∈ normalizer (middleGroup : Set Block) := by
        rw [mem_normalizer_iff]
        intro a
        have he := mem_normalizer_iff.mp hx.2 (j a)
        simpa only [A, ← map_mul, ← map_inv, mem_map_iff_mem hj] using he
      have hbT : b ∈ standardSylow :=
        ⟨ConstructionModel.marked_centralizer_le_point hbz,
          show b ∈ linePreimage from normalizer_middle_eq_linePreimage ▸ hbn⟩
      rw [← hT]
      exact mem_map_of_mem j hbT
    · intro x hx
      refine ⟨hTH hx, ?_⟩
      rw [← hT] at hx
      obtain ⟨b, hb, rfl⟩ := hx
      have hn := standardSylow_normalizes_middle hb
      exact le_normalizer_map j (mem_map_of_mem j hn)
  have hcent : Centralizer z ⊓ centralizer (A : Set G) = A := by
    apply le_antisymm
    · intro x hx
      have hxT : x ∈ T := hnorm ▸ ⟨hx.1, Subgroup.centralizer_le_normalizer _ hx.2⟩
      obtain ⟨u, rfl⟩ := hkrange ▸ hxT
      have hu : u ∈ centralizer (Unitriangular.A : Set Unitriangular.T) := by
        intro v hv
        apply hk
        simp only [map_mul]
        exact hx.2 (k v) (hAm ▸ mem_map_of_mem k hv)
      rw [← hAm]
      exact mem_map_of_mem k (ConstructionModel.centralizer_middle u hu)
    · let := hAelem
      exact le_inf (hAT.trans hTH) (le_centralizer A)
  refine {
    A := A
    elementary := hAelem
    card := hAcard
    S := S
    A_le_sylow := hAT
    sylow_square := ?_
    relative_centralizer := hcent
    normalizer_intersection := hnorm
    unique_sixteen := ?_
    sylow_center := ?_ }
  · intro t ht
    change t ∈ T at ht
    obtain ⟨u, rfl⟩ := hkrange ▸ ht
    rw [← map_pow, ← hAm]
    exact mem_map_of_mem k (ConstructionModel.square_mem u)
  · intro B hBT hBe hBc
    let e : Unitriangular.T ≃* T := (MonoidHom.ofInjective hk).trans
      (MulEquiv.subgroupCongr hkrange)
    let C := (B.subgroupOf T).map e.symm.toMonoidHom
    let := hBe
    let : IsElementaryAbelian 2 (B.subgroupOf T) := IsElementaryAbelian.subgroupOf hBT
    let : IsElementaryAbelian 2 C := IsElementaryAbelian.map _
    have hCc : Nat.card C = 16 := by
      rw [card_map_of_injective e.symm.injective,
        Nat.card_congr (subgroupOfEquivOfLe hBT).toEquiv, hBc]
    have hCA : C ≤ Unitriangular.A := Unitriangular.large_elementary_le C hCc.ge
    apply eq_of_le_of_card_ge _ (hBc.trans hAcard.symm).ge
    intro b hb
    have hc : e.symm ⟨b, hBT hb⟩ ∈ C := mem_map_of_mem _ hb
    have hm := mem_map_of_mem k (hCA hc)
    have he : k (e.symm ⟨b, hBT hb⟩) = b :=
      congrArg Subtype.val (e.apply_symm_apply ⟨b, hBT hb⟩)
    rwa [hAm, he] at hm
  · change (center T).map T.subtype = zpowers z
    apply le_antisymm
    · rintro x ⟨x, hx, rfl⟩
      change (x : G) ∈ zpowers z
      have hxrange : (x : G) ∈ k.range := by
        rw [hkrange]
        exact x.property
      obtain ⟨u, hu⟩ := hxrange
      have huc : u ∈ center Unitriangular.T := by
        apply mem_center_iff.mpr
        intro v
        apply hk
        simp only [map_mul, hu]
        exact congrArg Subtype.val (mem_center_iff.mp hx ⟨k v, hkT v⟩)
      rcases ConstructionModel.center_cases u huc with hu1 | huz
      · rw [hu1, map_one] at hu
        rw [← hu]
        exact (zpowers z).one_mem
      · change j (sylowMap u) = x at hu
        rw [huz, hz] at hu
        rw [← hu]
        exact mem_zpowers z
    · apply zpowers_le.mpr
      have hzT : z ∈ T := hz ▸ hkT Unitriangular.z
      refine ⟨⟨z, hzT⟩, ?_, rfl⟩
      apply mem_center_iff.mpr
      intro t
      apply Subtype.ext
      exact mem_centralizer_singleton_iff.mp (hTH t.property)

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Configuration.Construction

end
