module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.PairedOddLinearTwo.Source
public import CFSG.Quasithin.ChapterE.Section02.Structure.ComponentModels.OriginalImage
/-!
# The original elementary subgroup inside the paired PSL₂ product

The source supplies two commuting conjugate components and their literal
multiplication isomorphism. The original Sylow-normal elementary subgroup
acts inwardly on both factors; triviality of the product centralizer places
it inside their product. Compose the two actual component markings with
that multiplication map to obtain an injective PSL₂×PSL₂ map whose image
contains V. The quotient wrapper retains exactly the original image VJ/J.

Source: Aschbacher–Smith E.2.7 and E.2.17, printed pp.219 and230.
-/
public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Witnesses.PairedOddLinearTwo
variable {H : Type*} [Group H] [Finite H]
theorem source_product_embedding
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p) (hp : p = 7 ∨ 9 < p)
    (hH : IsStronglyQuasithin H) (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hs : ¬Group.IsSolvable H)
    (hJ : ChapterB.minimalParabolicCore T hP = ⊥)
    {K : Subgroup H} (hK : IsComponent H K) (hC : K.IsCComponent)
    [IsSimpleGroup K] (hgen : K ⊔ (T : Subgroup H) = ⊤) (hnot : ¬K.Normal)
    (e : K ≃* PSL(2,F)) (V : Subgroup H) [IsElementaryAbelian 2 V]
    (hVT : V ≤ T) (hVN : (T : Subgroup H) ≤ normalizer (V : Set H))
    : ∃ j : PSL(2,F) × PSL(2,F) →* H,
      Function.Injective j ∧ V ≤ j.range := by
  have hrad : solvableRadical H = ⊥ :=
    (ChapterB.minimalParabolic_nonsolvable_core_eq_radical T hP hs).symm.trans hJ
  obtain ⟨t,hne,hDsimple,hD,hR,⟨d,_⟩,_,_⟩ :=
    Structure.source_pair_coordinates hH T hP hs hJ hK hC hgen hnot
  let D := K.map (MulAut.conj (t:H)).toMonoidHom
  let : IsSimpleGroup D := hDsimple
  let : IsQuasisimple D := hD.2
  have hDC : D.IsCComponent := isCComponent_of_isSimpleGroup_of_isPerfect hD.1
  let eD : D ≃* PSL(2,F) := ((MulAut.conj (t:H)).subgroupMap K).symm.trans e
  have hDT : D ⊔ (T : Subgroup H) = ⊤ := by
    have he := congrArg (Subgroup.map (MulAut.conj (t:H)).toMonoidHom) hgen
    rw [Subgroup.map_sup,map_top_of_surjective _ (MulAut.conj (t:H)).surjective] at he
    have ht : (T : Subgroup H).map (MulAut.conj (t:H)).toMonoidHom = T :=
      mem_normalizer_iff_map_conj_eq.mp ((T : Subgroup H).le_normalizer t.property)
    rwa [ht] at he
  have hKdata := source_component_placement ho hF hp hH T hP hK hC hrad hgen e V hVT hVN
  have hDdata := source_component_placement ho hF hp hH T hP hD hDC hrad hDT eD V hVT hVN
  have hc : ⁅K,D⁆ = ⊥ := hK.commutator_eq_bot_of_ne hD hne.symm
  have hnormal : (K ⊔ D).Normal := by rw [← hR]; infer_instance
  let := hnormal
  have hRT : (K ⊔ D : Subgroup H) ⊔ (T : Subgroup H) = ⊤ := top_unique (by
    rw [← hgen]
    exact sup_le_sup le_sup_left le_rfl)
  have hZ : center (K ⊔ D : Subgroup H) = ⊥ :=
    center_eq_bot_of_isSubnormal_of_solvableRadical_eq_bot hrad hnormal.isSubnormal
  have hCR : centralizer ((K ⊔ D : Subgroup H) : Set H) = ⊥ := by
    have hcT := centralizer_le_sylow_of_centerless_supplement (K ⊔ D) T hRT hZ
    have hcO : centralizer ((K ⊔ D : Subgroup H) : Set H) ≤ pCore 2 H :=
      le_sSup ⟨inferInstance,T.isPGroup'.to_le hcT⟩
    exact le_bot_iff.mp (hcO.trans ((ChapterB.minimalParabolicTwoCore_le_core T hP).trans hJ.le))
  have hVR : V ≤ K ⊔ D := (le_inf hKdata.2.1 hDdata.2.1).trans
    (inf_inner_centralizer_supplements_le_sup K D hc hCR)
  let f : K × D →* H := (K ⊔ D : Subgroup H).subtype.comp d.toMonoidHom
  have hf : Function.Injective f := (K ⊔ D : Subgroup H).subtype_injective.comp d.injective
  have hfr : f.range = K ⊔ D := by
    change ((K ⊔ D : Subgroup H).subtype.comp d.toMonoidHom).range = _
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr d.surjective,
      ← MonoidHom.range_eq_map,range_subtype]
  let dF : PSL(2,F) × PSL(2,F) ≃* K × D := MulEquiv.prodCongr e.symm eD.symm
  let j := f.comp dF.toMonoidHom
  refine ⟨j,hf.comp dF.injective,?_⟩
  have hj : j.range = f.range := by
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr dF.surjective,← MonoidHom.range_eq_map]
  rw [hj,hfr]
  exact hVR

universe u
theorem source_star_product_embedding
    {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
    (hA : ChapterA.Section02.TheoremA κ G) (hG : IsSQTK κ G)
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable G) (K : Subgroup G) (hK : K.IsCComponent)
    (hgen : K ⊔ (T : Subgroup G) = ⊤) (hnot : ¬ K.Normal)
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p) (hp : p=7 ∨ 9<p)
    (e : K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (V : Subgroup G) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hVN : (V.subgroupOf (T : Subgroup G)).Normal) :
    ∃ j : PSL(2,F) × PSL(2,F) →* G ⧸ ChapterB.minimalParabolicCore T hP,
      Function.Injective j ∧
      V.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP)) ≤ j.range := by
  let J := ChapterB.minimalParabolicCore T hP
  let q := QuotientGroup.mk' J
  let S := T.mapSurjective (QuotientGroup.mk'_surjective J)
  let L := K.map q
  let W := V.map q
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map q
  let : Group.IsSolvable J := ChapterB.minimalParabolic_core_solvable T hP
  have hsQ : ¬ Group.IsSolvable (G ⧸ J) := fun hq =>
    hs ((Group.isSolvable_iff_subgroup_quotient J).mpr ⟨inferInstance,hq⟩)
  have hi := Structure.source_component_simple_image T hP hs K hK hgen
  let : IsSimpleGroup L := hi.1
  have hC : L.IsCComponent := hi.2.1.isCComponent
  have hnotQ : ¬ L.Normal := fun hq =>
    hnot (cComponent_normal_of_quotient_normal hK J hq)
  have hSQ : IsStronglyQuasithin (G ⧸ J) :=
    (Structure.source_star_sqtk hA hG T hP hs).stronglyQuasithin
  have hSW : (S:Subgroup (G⧸J)) ≤ normalizer (W:Set (G⧸J)) :=
    (map_mono ((normal_subgroupOf_iff_le_normalizer hVT).mp hVN)).trans (le_normalizer_map q)
  exact source_product_embedding ho hF hp hSQ S
    (Structure.source_star_minimal_core_free T hP).1 hsQ
    (Structure.source_star_minimal_core_free T hP).2 hi.2.1 hC hi.2.2.2 hnotQ
    e W (map_mono hVT) hSW
end CFSG.Quasithin.ChapterE.Witnesses.PairedOddLinearTwo
