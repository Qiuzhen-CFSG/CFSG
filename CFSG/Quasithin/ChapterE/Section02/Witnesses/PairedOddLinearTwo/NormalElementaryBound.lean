module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.PairedOddLinearTwo.SmallProduct

/-!
# Sylow-normal elementary subgroups with an odd-linear component

The original elementary subgroup acts on each of the two conjugate
components through a group of order at most two, including the prime-seven
boundary. The product of these two actions is faithful: its kernel
centralizes the whole residual, whose centralizer is trivial in the
core-free minimal parabolic. Hence the original subgroup has order at most
four. When the generating component is normal, its own centralizer is
trivial and the single action gives the stronger bound of two. The
star-quotient applications retain the literal image of the same subgroup
under the minimal-parabolic core quotient.

Source: Aschbacher–Smith E.2.7, printed p.219, and the last paragraph of
14.6.9, printed p.1028.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Witnesses.PairedOddLinearTwo
variable {H : Type*} [Group H] [Finite H]

private theorem card_le_four_of_component_actions (K D V : Subgroup H)
    (hVK : V ≤ normalizer (K : Set H))
    (hVD : V ≤ normalizer (D : Set H))
    (hK : Nat.card ((V.subgroupOf (normalizer (K : Set H))).map
      (NormalizerAction.quotient K)) ≤ 2)
    (hD : Nat.card ((V.subgroupOf (normalizer (D : Set H))).map
      (NormalizerAction.quotient D)) ≤ 2)
    (hC : centralizer ((K ⊔ D : Subgroup H) : Set H) = ⊥) : Nat.card V ≤ 4 := by
  let A := (V.subgroupOf (normalizer (K : Set H))).map (NormalizerAction.quotient K)
  let B := (V.subgroupOf (normalizer (D : Set H))).map (NormalizerAction.quotient D)
  let fK : V →* A := ((NormalizerAction.quotient K).comp (inclusion hVK)).codRestrict A
    (fun v => ⟨inclusion hVK v,v.property,rfl⟩)
  let fD : V →* B := ((NormalizerAction.quotient D).comp (inclusion hVD)).codRestrict B
    (fun v => ⟨inclusion hVD v,v.property,rfl⟩)
  let f : V →* A × B := fK.prod fD
  have hf : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    apply le_bot_iff.mp
    intro v hv
    have hvK : (v : H) ∈ centralizer (K : Set H) := by
      apply (NormalizerAction.quotient_eq_one_iff K (inclusion hVK v)).mp
      exact congrArg (fun w : A × B => (w.1 : NormalizerAction.Star K)) hv
    have hvD : (v : H) ∈ centralizer (D : Set H) := by
      apply (NormalizerAction.quotient_eq_one_iff D (inclusion hVD v)).mp
      exact congrArg (fun w : A × B => (w.2 : NormalizerAction.Star D)) hv
    have hz : zpowers (v : H) ≤ centralizer ((K ⊔ D : Subgroup H) : Set H) :=
      le_centralizer_iff.mpr (sup_le
        (le_centralizer_iff.mp (zpowers_le.mpr hvK))
        (le_centralizer_iff.mp (zpowers_le.mpr hvD)))
    have hv1 : (v : H) = 1 := by
      have hh := hz (mem_zpowers (v : H))
      rwa [hC,mem_bot] at hh
    exact Subtype.ext hv1
  calc
    Nat.card V ≤ Nat.card (A × B) := Nat.card_le_card_of_injective f hf
    _ = Nat.card A * Nat.card B := Nat.card_prod _ _
    _ ≤ 2 * 2 := Nat.mul_le_mul hK hD
    _ = 4 := rfl

/-- In the original paired odd-linear source, every Sylow-normal elementary
subgroup has order at most four. No factor-action premise is added. -/
theorem source_normal_elementary_card_le_four
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p) (hp : p = 7 ∨ 9 < p)
    (hH : IsStronglyQuasithin H) (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hs : ¬Group.IsSolvable H)
    (hJ : ChapterB.minimalParabolicCore T hP = ⊥)
    {K : Subgroup H} (hK : IsComponent H K) (hC : K.IsCComponent)
    [IsSimpleGroup K] (hgen : K ⊔ (T : Subgroup H) = ⊤) (hnot : ¬K.Normal)
    (e : K ≃* PSL(2,F)) (V : Subgroup H) [IsElementaryAbelian 2 V]
    (hVT : V ≤ T) (hVN : (T : Subgroup H) ≤ normalizer (V : Set H)) :
    Nat.card V ≤ 4 := by
  have hrad : solvableRadical H = ⊥ :=
    (ChapterB.minimalParabolic_nonsolvable_core_eq_radical T hP hs).symm.trans hJ
  obtain ⟨t,_,hDsimple,hD,hR,_,_,_⟩ :=
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
  exact card_le_four_of_component_actions K D V hKdata.1 hDdata.1 hKdata.2.2 hDdata.2.2 hCR

/-- Every original Sylow-normal elementary subgroup acts faithfully on a
normal generating odd-linear component. -/
theorem source_normal_component_elementary_card_le_two
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p) (hp : p = 7 ∨ 9 < p)
    (hH : IsStronglyQuasithin H) (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hs : ¬Group.IsSolvable H)
    (hJ : ChapterB.minimalParabolicCore T hP = ⊥)
    {K : Subgroup H} (hK : IsComponent H K) (hC : K.IsCComponent)
    [IsSimpleGroup K] [K.Normal] (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (e : K ≃* PSL(2,F)) (V : Subgroup H) [IsElementaryAbelian 2 V]
    (hVT : V ≤ T) (hVN : (T : Subgroup H) ≤ normalizer (V : Set H)) :
    Nat.card V ≤ 2 := by
  have hrad : solvableRadical H = ⊥ :=
    (ChapterB.minimalParabolic_nonsolvable_core_eq_radical T hP hs).symm.trans hJ
  have hdata := source_component_placement ho hF hp hH T hP hK hC hrad hgen e V hVT hVN
  have hZ : center K = ⊥ :=
    center_eq_bot_of_isSubnormal_of_solvableRadical_eq_bot hrad hK.1
  have hCK : centralizer (K : Set H) = ⊥ := by
    have hcT := centralizer_le_sylow_of_centerless_supplement K T hgen hZ
    have hcO : centralizer (K : Set H) ≤ pCore 2 H :=
      le_sSup ⟨inferInstance,T.isPGroup'.to_le hcT⟩
    exact le_bot_iff.mp (hcO.trans ((ChapterB.minimalParabolicTwoCore_le_core T hP).trans hJ.le))
  let A := (V.subgroupOf (normalizer (K : Set H))).map (NormalizerAction.quotient K)
  let f : V →* A := ((NormalizerAction.quotient K).comp (inclusion hdata.1)).codRestrict A
    (fun v => ⟨inclusion hdata.1 v,v.property,rfl⟩)
  have hf : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    apply le_bot_iff.mp
    intro v hv
    have hvK : (v : H) ∈ centralizer (K : Set H) := by
      apply (NormalizerAction.quotient_eq_one_iff K (inclusion hdata.1 v)).mp
      exact congrArg (fun w : A => (w : NormalizerAction.Star K)) hv
    have hv1 : (v : H) = 1 := by rwa [hCK,mem_bot] at hvK
    exact Subtype.ext hv1
  exact (Nat.card_le_card_of_injective f hf).trans hdata.2.2

/-- The order-four bound for every generating odd-linear component, whether
normal or exchanged with its conjugate. -/
theorem source_elementary_card_le_four
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p) (hp : p = 7 ∨ 9 < p)
    (hH : IsStronglyQuasithin H) (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hs : ¬Group.IsSolvable H)
    (hJ : ChapterB.minimalParabolicCore T hP = ⊥)
    {K : Subgroup H} (hK : IsComponent H K) (hC : K.IsCComponent)
    [IsSimpleGroup K] (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (e : K ≃* PSL(2,F)) (V : Subgroup H) [IsElementaryAbelian 2 V]
    (hVT : V ≤ T) (hVN : (T : Subgroup H) ≤ normalizer (V : Set H)) :
    Nat.card V ≤ 4 := by
  by_cases hn : K.Normal
  · let := hn
    exact (source_normal_component_elementary_card_le_two ho hF hp hH T hP hs hJ
      hK hC hgen e V hVT hVN).trans (by decide)
  · exact source_normal_elementary_card_le_four ho hF hp hH T hP hs hJ
      hK hC hgen hn e V hVT hVN

universe u
/-- The same bound on the literal image of the original subgroup in H/J,
where J is the original minimal-parabolic core. -/
theorem source_star_normal_elementary_card_le_four
    {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
    (hA : ChapterA.Section02.TheoremA κ G) (hG : IsSQTK κ G)
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable G) (K : Subgroup G) (hK : K.IsCComponent)
    (hgen : K ⊔ (T : Subgroup G) = ⊤) (hnot : ¬ K.Normal)
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p) (hp : p = 7 ∨ 9 < p)
    (e : K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (V : Subgroup G) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hVN : (V.subgroupOf (T : Subgroup G)).Normal) :
    Nat.card (V.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) ≤ 4 := by
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
  have hSW : (S : Subgroup (G ⧸ J)) ≤ normalizer (W : Set (G ⧸ J)) :=
    (map_mono ((normal_subgroupOf_iff_le_normalizer hVT).mp hVN)).trans (le_normalizer_map q)
  exact source_normal_elementary_card_le_four ho hF hp hSQ S
    (Structure.source_star_minimal_core_free T hP).1 hsQ
    (Structure.source_star_minimal_core_free T hP).2 hi.2.1 hC hi.2.2.2 hnotQ
    e W (map_mono hVT) hSW

/-- The literal star-quotient image has order at most four, with no
normality restriction on the original generating component. -/
theorem source_star_elementary_card_le_four
    {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
    (hA : ChapterA.Section02.TheoremA κ G) (hG : IsSQTK κ G)
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable G) (K : Subgroup G) (hK : K.IsCComponent)
    (hgen : K ⊔ (T : Subgroup G) = ⊤)
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p) (hp : p = 7 ∨ 9 < p)
    (e : K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (V : Subgroup G) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hVN : (V.subgroupOf (T : Subgroup G)).Normal) :
    Nat.card (V.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) ≤ 4 := by
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
  have hSQ : IsStronglyQuasithin (G ⧸ J) :=
    (Structure.source_star_sqtk hA hG T hP hs).stronglyQuasithin
  have hSW : (S : Subgroup (G ⧸ J)) ≤ normalizer (W : Set (G ⧸ J)) :=
    (map_mono ((normal_subgroupOf_iff_le_normalizer hVT).mp hVN)).trans (le_normalizer_map q)
  exact source_elementary_card_le_four ho hF hp hSQ S
    (Structure.source_star_minimal_core_free T hP).1 hsQ
    (Structure.source_star_minimal_core_free T hP).2 hi.2.1 hC hi.2.2.2
    e W (map_mono hVT) hSW

end CFSG.Quasithin.ChapterE.Witnesses.PairedOddLinearTwo
