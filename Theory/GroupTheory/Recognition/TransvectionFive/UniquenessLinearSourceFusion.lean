module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceSylowCensus
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceOvergroup
public import Theory.GroupTheory.AbelianWeakClosureFusion
public import Theory.GroupTheory.SylowNormalPairFusion
public import Theory.GroupTheory.WeakClosureNormalizer

/-!
# Ambient fusion of the two marked rectangular groups

Transport the maximum elementary subgroup calculation through the original
full-centralizer marking. The self-normalizing marked Sylow prevents the two
rectangles from being conjugate. Every conjugate of either rectangle inside
that Sylow has order 64 and must be one of the two; nonconjugacy forces it to
be the original one. Burnside fusion then produces an actual conjugating
element in its literal normalizer.

This proves Aschbacher, *Sporadic Groups* (1994), 39.6(1–3), pp.214–215,
without simplicity or an ambient recognition isomorphism. The actual 21/21
consumer gives the two relative point-centralizer indices in 40.3. The full
fusion sets also restrict unchanged to any centralizer overgroup containing
the corresponding normalizers, so the normalizer-generated subgroup in 41.1
inherits `LinearFusion`. Its generation and local comparison remain unproved.
-/

public noncomputable section
open Subgroup BinaryLinear.TransvectionFiveLocal
namespace Theory.GroupTheory.TransvectionFive.UniquenessLinear
variable {G : Type*} [Group G] [Finite G] {z : G} (F : MarkedCentralizer z)

/-- The maximum elementary subgroups of the actual marked ambient Sylow.
The proof transports the original marking, including subgroup embeddings. -/
theorem source_large_elementary_eq (E : Subgroup G) [IsElementaryAbelian 2 E]
    (hET : E ≤ (sourceSylow F : Subgroup G)) (hcard : 64 ≤ Nat.card E) :
    E = F.plane ∨ E = F.threeSpace := by
  let C := Subgroup.centralizer ({z} : Set G)
  have hEC : E ≤ C := hET.trans (sourceSylow_le_point_centralizer F)
  let f : C →* SL := centralizer.subtype.comp F.equiv.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp F.equiv.injective
  let A : Subgroup SL := (E.subgroupOf C).map f
  let : IsElementaryAbelian 2 (E.subgroupOf C) :=
    IsElementaryAbelian.of_injective (subgroupOfEquivOfLe hEC).toMonoidHom
      (subgroupOfEquivOfLe hEC).injective
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map f
  have hAU : A ≤ upper := by
    rintro _ ⟨x, hx, rfl⟩
    apply (F.mem_pullback_iff upper x).mp
    rw [← sourceSylow_eq_pullback_upper]
    exact hET hx
  have hcA : Nat.card A = Nat.card E := by
    rw [card_map_of_injective hf]
    exact Nat.card_congr (subgroupOfEquivOfLe hEC).toEquiv
  have hback : F.pullback A = E := by
    ext x
    constructor
    · intro hx
      let c : C := ⟨x, F.pullback_le A hx⟩
      obtain ⟨y, hy, he⟩ := (F.mem_pullback_iff A c).mp hx
      have he' : y = c := F.equiv.injective (Subtype.ext he)
      change (y : G) ∈ E at hy
      have hh : (y : G) = x := congrArg (fun a : C => (a : G)) he'
      exact hh ▸ hy
    · intro hx
      let c : C := ⟨x, hEC hx⟩
      apply (F.mem_pullback_iff A c).mpr
      exact mem_map_of_mem f hx
  rcases model_large_elementary_eq_rectangle A hAU (hcA.symm ▸ hcard) with h2 | h3
  · exact Or.inl (hback.symm.trans (congrArg F.pullback h2))
  · exact Or.inr (hback.symm.trans (congrArg F.pullback h3))

omit [Finite G] in
/-- The two marked rectangular groups are distinct in their original embedding. -/
theorem source_plane_ne_threeSpace : F.plane ≠ F.threeSpace := by
  let a : SL := root (show (0 : Fin 5) < 2 by decide)
  have ha : a ∈ Model.plane := subset_closure ⟨0, 2, by decide, by decide, by decide, rfl⟩
  have hn : a ∉ Model.threeSpace := by
    intro h
    have he := (RectangleCoordinates.mem3_iff a).mp h 0 2 (by decide)
    norm_num [a, root, Matrix.SpecialLinearGroup.transvection_coe, Matrix.single, Matrix.one_apply] at he
  let x := F.equiv.symm ⟨a, Model.plane_le_centralizer ha⟩
  have hx : (x : G) ∈ F.plane := (F.mem_pullback_iff Model.plane x).mpr (by
    simpa only [x, F.equiv.apply_symm_apply] using ha)
  intro he
  rw [he] at hx
  apply hn
  simpa only [x, F.equiv.apply_symm_apply] using (F.mem_pullback_iff Model.threeSpace x).mp hx

/-- Source 39.6(1): the two marked rectangular groups are not ambient conjugates. -/
theorem source_planes_not_conjugate (g : G) :
    F.plane.map (MulAut.conj g).toMonoidHom ≠ F.threeSpace := by
  apply (sourceSylow F).not_conjugate_of_normalizer_pair F.plane F.threeSpace
    (plane_normalizers_contain_sourceSylow F).1
    (plane_normalizers_contain_sourceSylow F).2 (source_plane_ne_threeSpace F)
  intro n hn
  change n ∈ normalizer ((sourceSylow F : Subgroup G) : Set G) at hn
  rw [sourceSylow_normalizer] at hn
  exact Or.inl (mem_normalizer_iff_map_conj_eq.mp
    ((plane_normalizers_contain_sourceSylow F).1 hn))

/-- Source 39.6(2): the original plane group is weakly closed in the marked Sylow. -/
theorem source_plane_weakly_closed (g : G)
    (hg : F.plane.map (MulAut.conj g).toMonoidHom ≤ (sourceSylow F : Subgroup G)) :
    F.plane.map (MulAut.conj g).toMonoidHom = F.plane := by
  let := marked_rectangle_elementary F 2
  let := IsElementaryAbelian.map (p := 2) (A := F.plane) (MulAut.conj g).toMonoidHom
  have hc : 64 ≤ Nat.card (F.plane.map (MulAut.conj g).toMonoidHom) := by
    rw [card_map_of_injective (MulAut.conj g).injective, source_plane_card]
  exact (source_large_elementary_eq F _ hg hc).resolve_right (source_planes_not_conjugate F g)

/-- Source 39.6(2) for the other marked rectangle. -/
theorem source_threeSpace_weakly_closed (g : G)
    (hg : F.threeSpace.map (MulAut.conj g).toMonoidHom ≤ (sourceSylow F : Subgroup G)) :
    F.threeSpace.map (MulAut.conj g).toMonoidHom = F.threeSpace := by
  let := marked_rectangle_elementary F 3
  let := IsElementaryAbelian.map (p := 2) (A := F.threeSpace) (MulAut.conj g).toMonoidHom
  have hc : 64 ≤ Nat.card (F.threeSpace.map (MulAut.conj g).toMonoidHom) := by
    rw [card_map_of_injective (MulAut.conj g).injective, source_threeSpace_card]
  apply (source_large_elementary_eq F _ hg hc).resolve_left
  intro he
  have hh := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) he
  have hc : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id G := by
    ext x
    simp [mul_assoc]
  rw [map_map, hc, map_id] at hh
  exact source_planes_not_conjugate F g⁻¹ hh.symm

/-- Weak closure also holds inside the full plane normalizer, as in source 39.6(2). -/
theorem source_plane_weakly_closed_in_normalizer (g : G)
    (hg : F.plane.map (MulAut.conj g).toMonoidHom ≤ normalizer (F.plane : Set G)) :
    F.plane.map (MulAut.conj g).toMonoidHom = F.plane :=
  (sourceSylow F).conjugate_eq_of_le_normalizer_of_weakly_closed F.plane
    (flag_le_sourceSylow F).2.2.1 (source_plane_weakly_closed F) g hg

/-- The same full-normalizer weak closure for the local-plane group. -/
theorem source_threeSpace_weakly_closed_in_normalizer (g : G)
    (hg : F.threeSpace.map (MulAut.conj g).toMonoidHom ≤ normalizer (F.threeSpace : Set G)) :
    F.threeSpace.map (MulAut.conj g).toMonoidHom = F.threeSpace :=
  (sourceSylow F).conjugate_eq_of_le_normalizer_of_weakly_closed F.threeSpace
    (flag_le_sourceSylow F).2.2.2 (source_threeSpace_weakly_closed F) g hg

/-- Source 39.6(3): an actual element of the literal plane normalizer realizes fusion. -/
theorem source_plane_fusion {a b : G} (ha : a ∈ F.plane) (hb : b ∈ F.plane)
    (hab : IsConj a b) : ∃ n ∈ normalizer (F.plane : Set G), n * a * n⁻¹ = b := by
  let := marked_rectangle_elementary F 2
  exact (sourceSylow F).normalizer_fuses_of_abelian_weakly_closed F.plane
    (flag_le_sourceSylow F).2.2.1 (source_plane_weakly_closed F) ha hb hab

/-- Source 39.6(3) for the actual three-space normalizer. -/
theorem source_threeSpace_fusion {a b : G} (ha : a ∈ F.threeSpace) (hb : b ∈ F.threeSpace)
    (hab : IsConj a b) : ∃ n ∈ normalizer (F.threeSpace : Set G), n * a * n⁻¹ = b := by
  let := marked_rectangle_elementary F 3
  exact (sourceSylow F).normalizer_fuses_of_abelian_weakly_closed F.threeSpace
    (flag_le_sourceSylow F).2.2.2 (source_threeSpace_weakly_closed F) ha hb hab


omit [Finite G] in
private theorem normalizer_point_index (A : Subgroup G) (hz : z ∈ A)
    (hf : ∀ a ∈ A, IsConj z a → ∃ n ∈ normalizer (A : Set G), n * z * n⁻¹ = a) :
    (Subgroup.centralizer ({z} : Set G)).relIndex (normalizer (A : Set G)) =
      (F.fusion A).ncard := by
  let N := normalizer (A : Set G)
  let ρ : N →* MulAut G := MulAut.conj.comp N.subtype
  let : MulAction N G := MulAction.compHom G ρ
  have ho : MulAction.orbit N z = F.fusion A := by
    ext a
    constructor
    · rintro ⟨n, rfl⟩
      refine ⟨?_, isConj_iff.mpr ⟨(n : G), rfl⟩⟩
      exact (mem_normalizer_iff.mp n.property z).mp hz
    · rintro ⟨ha, hza⟩
      obtain ⟨n, hn, he⟩ := hf a ha hza
      exact ⟨⟨n, hn⟩, he⟩
  have hs : MulAction.stabilizer N z =
      (Subgroup.centralizer ({z} : Set G)).subgroupOf N := by
    ext n
    change (n : G) * z * (n : G)⁻¹ = z ↔
      (n : G) ∈ Subgroup.centralizer ({z} : Set G)
    rw [mem_centralizer_singleton_iff]
    exact mul_inv_eq_iff_eq_mul
  change ((Subgroup.centralizer ({z} : Set G)).subgroupOf N).index = _
  rw [← hs, MulAction.index_stabilizer, ho]

/-- The 21-element plane fusion set is the actual orbit of z under its normalizer.
Thus the relative point-centralizer index used in source 40.3 is exactly 21. -/
theorem source_plane_point_index (hlinear : F.LinearFusion) :
    (Subgroup.centralizer ({z} : Set G)).relIndex (normalizer (F.plane : Set G)) = 21 := by
  rw [normalizer_point_index F F.plane (point_mem_plane F)
    (fun _ ha hf => source_plane_fusion F (point_mem_plane F) ha hf)]
  exact hlinear.1

/-- The same exact relative index for the three-space normalizer. -/
theorem source_threeSpace_point_index (hlinear : F.LinearFusion) :
    (Subgroup.centralizer ({z} : Set G)).relIndex (normalizer (F.threeSpace : Set G)) = 21 := by
  rw [normalizer_point_index F F.threeSpace (point_mem_threeSpace F)
    (fun _ ha hf => source_threeSpace_fusion F (point_mem_threeSpace F) ha hf)]
  exact hlinear.2

omit [Finite G] in
private theorem overgroup_fusion_image (L : Subgroup G)
    (hCL : Subgroup.centralizer ({z} : Set G) ≤ L) (A : Subgroup SL)
    (hNL : normalizer (F.pullback A : Set G) ≤ L)
    (hf : ∀ a ∈ F.pullback A, IsConj z a →
      ∃ n ∈ normalizer (F.pullback A : Set G), n * z * n⁻¹ = a) :
    L.subtype '' ((overgroupMarking F L hCL).fusion ((overgroupMarking F L hCL).pullback A)) =
      F.fusion (F.pullback A) := by
  ext a
  constructor
  · rintro ⟨b, ⟨hb, hz⟩, rfl⟩
    constructor
    · rw [← overgroupMarking_pullback_map F L hCL A]
      exact mem_map_of_mem L.subtype hb
    · obtain ⟨n, hn⟩ := isConj_iff.mp hz
      exact isConj_iff.mpr ⟨(n : G), by
        change (n : G) * z * (n : G)⁻¹ = (b : G)
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv, overgroupPoint_val] using
          congrArg (fun a : L => (a : G)) hn⟩
  · rintro ⟨ha, hz⟩
    let a' : L := ⟨a, hCL (F.pullback_le A ha)⟩
    refine ⟨a', ⟨?_, ?_⟩, rfl⟩
    · rw [overgroupMarking_pullback]
      exact ha
    · obtain ⟨n, hn, he⟩ := hf a ha hz
      exact isConj_iff.mpr ⟨⟨n, hNL hn⟩, Subtype.ext (by
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv, overgroupPoint_val] using he)⟩

/-- An overgroup containing the whole point centralizer and the plane normalizer
has exactly the original plane fusion set under its inclusion. -/
theorem overgroup_plane_fusion_image (L : Subgroup G)
    (hCL : Subgroup.centralizer ({z} : Set G) ≤ L)
    (hNL : normalizer (F.plane : Set G) ≤ L) :
    L.subtype '' ((overgroupMarking F L hCL).fusion (overgroupMarking F L hCL).plane) =
      F.fusion F.plane :=
  overgroup_fusion_image F L hCL Model.plane hNL
    (fun _ ha hf => source_plane_fusion F (point_mem_plane F) ha hf)

/-- The corresponding literal fusion-set transport for the three-space normalizer. -/
theorem overgroup_threeSpace_fusion_image (L : Subgroup G)
    (hCL : Subgroup.centralizer ({z} : Set G) ≤ L)
    (hNL : normalizer (F.threeSpace : Set G) ≤ L) :
    L.subtype '' ((overgroupMarking F L hCL).fusion (overgroupMarking F L hCL).threeSpace) =
      F.fusion F.threeSpace :=
  overgroup_fusion_image F L hCL Model.threeSpace hNL
    (fun _ ha hf => source_threeSpace_fusion F (point_mem_threeSpace F) ha hf)

/-- The actual generated subgroup in 41.1 inherits both 21-element fusion counts.
No simplicity or generation assertion about that subgroup is assumed. -/
theorem normalizerSpan_linearFusion (hlinear : F.LinearFusion) :
    (normalizerSpanMarking F).LinearFusion := by
  rw [normalizerSpanMarking_eq]
  constructor
  · have he := congrArg Set.ncard (overgroup_plane_fusion_image F (normalizerSpan F)
      (point_centralizer_le_normalizerSpan F) (by
        rw [normalizerSpan_eq]; exact le_sup_right.trans le_sup_left))
    rw [Set.ncard_image_of_injective _ (normalizerSpan F).subtype_injective] at he
    exact he.trans hlinear.1
  · have he := congrArg Set.ncard (overgroup_threeSpace_fusion_image F (normalizerSpan F)
      (point_centralizer_le_normalizerSpan F) (by
        rw [normalizerSpan_eq]; exact le_sup_right))
    rw [Set.ncard_image_of_injective _ (normalizerSpan F).subtype_injective] at he
    exact he.trans hlinear.2

end Theory.GroupTheory.TransvectionFive.UniquenessLinear
