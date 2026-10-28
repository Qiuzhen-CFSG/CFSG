module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Embeddings
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.LinearFiveStabilizer
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.MathieuTwentyFourStabilizer
public import Theory.GroupTheory.SylowSubnormalIntersection

/-!
# The actual quotient embeddings and their stabilizer hypotheses

Restriction of the original local component to a containing C-component,
followed by the two-core projection, gives a local component for a genuine
Sylow subgroup of the quotient. The quotient equivalence preserves the actual
smaller subgroup. Restricting a parabolic to its containing group preserves
its solvable residual, and an elementary-by-linear extension is transported
with its normal kernel. These deductions apply the proved L₅(2) and M₂₄
stabilizers; the precise universal J₄ stabilizer remains an explicit input.

Source: Aschbacher–Smith, 15.3.32(3), printed p.1133; the embedding conventions
of 1.2.4, p.505, and A.3.12(5),(14),(17), pp.47–48.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ComponentExtension.EmbeddingReduction
open Chapter1 Chapter1.Section02 Chapter1.Section02.LocalModels
open Chapter1.Terminal Chapter1.Terminal.LinearFourActions
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
/-- Innerness in an overgroup uses the same section as innerness in G.
In particular the two-core in the displacement formula is transported,
rather than replaced by the ambient overgroup's two-core. -/
theorem le_innerNormalizer_of_subgroupOf {B S C : Subgroup G}
    (hBC : B ≤ C) (hSC : S ≤ C) (hSB : S ≤ normalizer (B : Set G))
    (hinner : S.subgroupOf C ≤ innerTwoQuotientNormalizer (B.subgroupOf C)) :
    S ≤ innerTwoQuotientNormalizer B := by
  intro s hs
  have hsC : (⟨s, hSC hs⟩ : C) ∈ normalizer (B.subgroupOf C : Set C) := by
    rw [← subgroupOf_normalizer_eq hBC]
    exact hSB hs
  obtain ⟨b, hb, hact⟩ := (mem_innerNormalizer_iff_conjugation
    (⟨⟨s, hSC hs⟩, hsC⟩ : normalizer (B.subgroupOf C : Set C))).mp (hinner hs)
  apply (mem_innerNormalizer_iff_conjugation
    (⟨s, hSB hs⟩ : normalizer (B : Set G))).mpr
  refine ⟨b, hb, fun x hx => ?_⟩
  have h := mem_map_of_mem C.subtype (hact ⟨x, hBC hx⟩ hx)
  rw [map_pCoreIn_of_injective 2 (B.subgroupOf C) C.subtype C.subtype_injective,
    map_subgroupOf_eq_of_le hBC] at h
  exact h

omit [Finite G] in
private theorem local_of_top {B S : Subgroup G}
    (htop : (⊤ : Subgroup B).IsCComponent)
    (hSB : S ≤ normalizer (B : Set G)) :
    B ∈ ChapterA.Section03.localCComponents S := by
  change (B.subgroupOf (B ⊔ S)).IsCComponent
  have hB : B ≤ B ⊔ S := le_sup_left
  have hn : (B.subgroupOf (B ⊔ S)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hB).mpr (sup_le B.le_normalizer hSB)
  have ht := htop.map_equiv (subgroupOfEquivOfLe hB).symm
  rw [map_top_of_surjective _ (subgroupOfEquivOfLe hB).symm.surjective] at ht
  simpa only [← MonoidHom.range_eq_map, range_subtype] using
    Subgroup.IsCComponent.map_subtype hn.isSubnormal ht

omit [Finite G] in
/-- Restrict the genuine local component to a normalizing subgroup inside K. -/
theorem local_subgroupOf {B S K : Subgroup G}
    (hB : B ∈ ChapterA.Section03.localCComponents S)
    (hSB : S ≤ normalizer (B : Set G)) (hBK : B ≤ K) :
    B.subgroupOf K ∈ ChapterA.Section03.localCComponents (S.subgroupOf K) := by
  have htop : (⊤ : Subgroup B).IsCComponent := by
    simpa only [subgroupOf_self] using
      hB.subgroupOf_of_le (show B ≤ B from le_rfl) le_sup_left
  have ht := htop.map_equiv (subgroupOfEquivOfLe hBK).symm
  rw [map_top_of_surjective _ (subgroupOfEquivOfLe hBK).symm.surjective] at ht
  apply local_of_top ht
  rw [← subgroupOf_normalizer_eq hBK]
  exact comap_mono hSB

/-- The image in K/O₂(K) is local for an actual Sylow subgroup of that quotient.
This discharges the local-family premise of the J₄ stabilizer theorem. -/
theorem exists_image_local_sylow (S : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ ChapterA.Section03.localCComponents S)
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hBK : B ≤ K) (hK : K.IsCComponent) :
    ∃ T : Sylow 2 (XiQuotient K),
      twoQuotientImage B K ∈ ChapterA.Section03.localCComponents T := by
  obtain ⟨R, hR⟩ := S.exists_subgroupOf_eq_of_subnormal K hK.subnormal
  let q := QuotientGroup.mk' (pCore 2 K)
  let : Group.IsSolvable q.ker := by
    rw [QuotientGroup.ker_mk']
    let := pCore_isNilpotent (p := 2) (G := K)
    infer_instance
  refine ⟨R.mapSurjective (f := q) (QuotientGroup.mk'_surjective _), ?_⟩
  change (B.subgroupOf K).map q ∈ ChapterA.Section03.localCComponents ((R : Subgroup K).map q)
  rw [hR]
  exact localCComponents_map_of_solvable_ker (local_subgroupOf hB hSB hBK) q

/-- The intrinsic component quotient is identified with its actual ambient image. -/
@[simp] theorem component_image_equiv_apply {K : Subgroup G} (hK : K.IsCComponent) (k : K) :
    cComponentTwoCoreQuotientEquiv hK (QuotientGroup.mk' (pCore 2 K) k) =
      (QuotientGroup.mk' (pCore 2 G)).subgroupMap K k := rfl

/-- The same equivalence carries the smaller image to its actual embedded subgroup. -/
theorem component_image_equiv_map {B K : Subgroup G}
    (hBK : B ≤ K) (hK : K.IsCComponent) :
    (twoQuotientImage B K).map (cComponentTwoCoreQuotientEquiv hK).toMonoidHom =
      (B.map (QuotientGroup.mk' (pCore 2 G))).subgroupOf
        (K.map (QuotientGroup.mk' (pCore 2 G))) := by
  ext x
  constructor
  · rintro ⟨a, ⟨b, hb, rfl⟩, rfl⟩
    exact mem_map_of_mem (QuotientGroup.mk' (pCore 2 G)) hb
  · rintro ⟨b, hb, he⟩
    refine ⟨QuotientGroup.mk' (pCore 2 K) ⟨b, hBK hb⟩,
      mem_map_of_mem _ hb, ?_⟩
    exact Subtype.ext he

omit [Finite G] in
/-- Relative subgroup notation preserves the intrinsic two-core quotient model. -/
theorem isPSL_subgroupOf {B K : Subgroup G} (hBK : B ≤ K) {n q : ℕ}
    (hB : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) n q) :
    ClassicalGroup.IsPSL ((B.subgroupOf K) ⧸ pCore 2 (B.subgroupOf K)) n q := by
  let e := subgroupOfEquivOfLe hBK
  exact hB.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e))

private theorem parabolicResidual_of_embedded {A P : Subgroup G}
    (hP : LieParabolicTwo P) (he : (solvableResidual P).map P.subtype = A) :
    IsParabolicResidual A ⊤ false := by
  let e : G ≃* (⊤ : Subgroup G) := topEquiv.symm
  refine ⟨P.map e.toMonoidHom, LinearFiveStabilizer.lieParabolicTwo_map hP e,
    (by intro hf; cases hf), ?_⟩
  rw [← map_map, ← LinearFiveStabilizer.embeddedResidual_map P e, map_map]
  rw [show (⊤ : Subgroup G).subtype.comp e.toMonoidHom = MonoidHom.id G by rfl,
    Subgroup.map_id]
  exact he

/-- The parabolic remains the specified solvable residual after restricting to K. -/
theorem parabolicResidual_subgroupOf {B K : Subgroup G}
    (hBK : B ≤ K) (hres : IsParabolicResidual B K false) :
    IsParabolicResidual (B.subgroupOf K) ⊤ false := by
  obtain ⟨P, hP, _, he⟩ := hres
  apply parabolicResidual_of_embedded hP
  apply map_injective K.subtype_injective
  rw [map_map, map_subgroupOf_eq_of_le hBK]
  exact he

omit [Finite G] in
/-- Transfer an E(2^r)-by-PSL extension across the actual group equivalence. -/
theorem elementary_linear_extension_of_equiv {H : Type*} [Group H]
    (e : H ≃* G) {r n q : ℕ}
    (h : HasExtension G (ElementaryModel 2 r) (fun X _ => ClassicalGroup.IsPSL X n q)) :
    HasExtension H (ElementaryModel 2 r) (fun X _ => ClassicalGroup.IsPSL X n q) := by
  obtain ⟨N, hN, ⟨eN⟩, hQ⟩ := h
  let N' := N.map e.symm.toMonoidHom
  let f := e.symm.subgroupMap N
  let : N'.Normal := Subgroup.Normal.map hN e.symm.toMonoidHom e.symm.surjective
  refine ⟨N', inferInstance, ⟨f.symm.trans eN⟩, ?_⟩
  exact hQ.of_mulEquiv (QuotientGroup.congr N N' e.symm rfl).symm

/-- Apply the completed L₅(2) stabilizer to the original embedded parabolic. -/
theorem inner_of_five {B K : Subgroup G} (hBK : B ≤ K) (hK : K.IsCComponent)
    (hsmall : ClassicalGroup.IsPSL
      ((B.map (QuotientGroup.mk' (pCore 2 G))) ⧸
        pCore 2 (B.map (QuotientGroup.mk' (pCore 2 G)))) 4 2)
    (hlarge : ClassicalGroup.IsPSL (K.map (QuotientGroup.mk' (pCore 2 G))) 5 2)
    (hres : IsParabolicResidual (B.map (QuotientGroup.mk' (pCore 2 G)))
      (K.map (QuotientGroup.mk' (pCore 2 G))) false) :
    TwoStabilizerActsInner (twoQuotientImage B K) := by
  apply TwoStabilizerActsInner.of_map (cComponentTwoCoreQuotientEquiv hK)
  rw [component_image_equiv_map hBK hK]
  exact LinearFiveStabilizer.twoStabilizerActsInner hlarge
    (isPSL_subgroupOf (map_mono hBK) hsmall)
    (parabolicResidual_subgroupOf (map_mono hBK) hres)

/-- Apply the completed M₂₄ stabilizer, retaining the actual extension kernel. -/
theorem inner_of_fourteen {B K : Subgroup G} (hBK : B ≤ K) (hK : K.IsCComponent)
    (hlarge : Nonempty ((K.map (QuotientGroup.mk' (pCore 2 G))) ≃* Sporadic.Mathieu.M24))
    (hext : HasExtension (B.map (QuotientGroup.mk' (pCore 2 G)))
      (ElementaryModel 2 4) (fun X _ => ClassicalGroup.IsPSL X 4 2)) :
    TwoStabilizerActsInner (twoQuotientImage B K) := by
  apply TwoStabilizerActsInner.of_map (cComponentTwoCoreQuotientEquiv hK)
  rw [component_image_equiv_map hBK hK]
  exact MathieuTwentyFourStabilizer.twoStabilizerActsInner hlarge.some _
    (elementary_linear_extension_of_equiv (subgroupOfEquivOfLe (map_mono hBK)) hext)

/-- The J₄ conclusion remains the precise universal external input; its Sylow
local-component premise is proved here, not added to the section's assumptions. -/
theorem inner_of_seventeen
    (hJ4 : ∀ (Q : Type u) [Group Q] [Finite Q],
      ∀ (_eQ : Q ≃* Janko4.Model) (A : Subgroup Q) (T : Sylow 2 Q),
      ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 4 2 →
      A ∈ ChapterA.Section03.localCComponents T → TwoStabilizerActsInner A)
    (S : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ ChapterA.Section03.localCComponents S)
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hBK : B ≤ K) (hK : K.IsCComponent)
    (hsmall : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2)
    (hlarge : Nonempty ((K.map (QuotientGroup.mk' (pCore 2 G))) ≃* Janko4.Model)) :
    TwoStabilizerActsInner (twoQuotientImage B K) := by
  obtain ⟨T, hT⟩ := exists_image_local_sylow S hB hSB hBK hK
  exact hJ4 _ ((cComponentTwoCoreQuotientEquiv hK).trans hlarge.some) _ T
    (hsmall.of_mulEquiv (imageSectionEquiv hBK).symm) hT

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ComponentExtension.EmbeddingReduction
