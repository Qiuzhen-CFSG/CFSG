module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.MovedOffenderImage
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockCentralizerG2CoreProduct
public import Theory.Representation.G2BinaryOffenderPairGeneration
public import Theory.GroupTheory.PGroup.NormalSupplementKernel

/-!
# Generation by the actual moving G₂ module

The marked full normalizer actor has a two-group kernel on LT: its
restriction to L has kernel O₂(L), and LT/L is a two-group. The actual
moving offender and a derived conjugate generate the full binary model.
Lifting that conjugator through the original L marking gives the exact
generation modulo O₂(LT) used by the whole-core product theorem.

The final consumer therefore retains only the whole-core centralizer-index
bound; no independently chosen block actor or offender marking is needed.
Source: Aschbacher--Smith 3.3.28, printed p.601.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
open Chapter12.Section02 Chapter12.Section02.RecognitionSource
open Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
open ChapterB.QuasisimpleSource Atlas.G2.Natural
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
local notation "F" => ZMod 2

omit [Finite G] in
private theorem marked_join_actor_kernel_isPGroup
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* commutator (Atlas.G2.Model F))
    (q : ↥(L ⊔ (T : Subgroup G)) →* Atlas.G2.Model F)
    (hmark : ∀ l : L, q (inclusion le_sup_left l) =
      (e (QuotientGroup.mk' (pCore 2 L) l) : Atlas.G2.Model F)) :
    IsPGroup 2 q.ker := by
  let H := L ⊔ (T : Subgroup G)
  let L₀ := L.subgroupOf H
  let P := (T : Subgroup G).subgroupOf H
  let : L₀.Normal := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer hTL)
  apply q.kernel_isPGroup_of_normal_supplement L₀ P T.isPGroup'.comap_subtype
    (by rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self])
  let eL : L₀ ≃* L := subgroupOfEquivOfLe le_sup_left
  let f := q.comp L₀.subtype
  have hf (x : f.ker) : eL x.val ∈ pCore 2 L := by
    apply (QuotientGroup.eq_one_iff (eL x.val)).mp
    apply e.map_eq_one_iff.mp
    apply Subtype.val_injective
    have hh : q (inclusion le_sup_left (eL x.val)) = 1 := x.property
    rw [hmark] at hh
    exact hh
  let r : f.ker →* pCore 2 L :=
    (eL.toMonoidHom.comp f.ker.subtype).codRestrict _ hf
  apply (pCore_isPGroup (p := 2) (G := L)).of_injective r
  intro x y hxy
  apply Subtype.ext
  exact eL.injective (congrArg Subtype.val hxy)

/-- The actual noncentral moving module generates L modulo the original
core with one L-conjugate. The source Weyl marking supplies all actor data. -/
theorem moved_chosen_two_conjugate_generation
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction (OrthogonalCover.action F))
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    {d : G} (hd : d ∈ normalizer (T : Set G))
    (hmove : ¬ V.map (MulAut.conj d).toMonoidHom ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    ∃ g ∈ L, L ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊔
      (V.map (MulAut.conj d).toMonoidHom ⊔
        (V.map (MulAut.conj d).toMonoidHom).map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨b, ψ, hψ, hψL⟩ := exists_normalizer_full_g2_actor_marked h D structural e hne
  let H := L ⊔ (T : Subgroup G)
  let B := V.map (MulAut.conj d).toMonoidHom
  have hHN : H ≤ normalizer (L : Set G) :=
    sup_le L.le_normalizer D.sylow_normalizes_component
  have hBT : B ≤ (T : Subgroup G) :=
    (map_mono D.le_sylow).trans (mem_normalizer_iff_map_conj_eq.mp hd).le
  have hBH : B ≤ H := hBT.trans le_sup_right
  let q := ψ.comp (inclusion hHN)
  have hmark (l : L) : q (inclusion le_sup_left l) =
      (e.groupEquiv (QuotientGroup.mk' (pCore 2 L) l) : Atlas.G2.Model F) := hψL l
  have hker : q.ker ≤ pCore 2 H := le_sSup
    ⟨inferInstance, marked_join_actor_kernel_isPGroup D.sylow_normalizes_component
      e.groupEquiv q hmark⟩
  have himage : (B.subgroupOf H).map q =
      (B.subgroupOf (normalizer (L : Set G))).map ψ := by
    change (B.subgroupOf H).map (ψ.comp (inclusion hHN)) = _
    rw [← map_map]
    congr 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x.val, hBH hx⟩, hx, rfl⟩
  have hoff := (moved_full_actor_offender_image h D structural e hne b ψ hψ hd hmove).1
  change IsOffender (traceZeroAction F)
    ((B.subgroupOf (normalizer (L : Set G))).map ψ) at hoff
  rw [← himage] at hoff
  have hnatural := (OrthogonalCover.BinaryOffenders.offender_iff_natural _).mp hoff
  obtain ⟨c, hc, hgen⟩ :=
    BinaryPointGeneration.offender_exists_derived_conjugate_generating _ hnatural
  obtain ⟨k, hk⟩ :=
    (e.groupEquiv.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))) ⟨c, hc⟩
  let x : H := inclusion le_sup_left k
  have hx : q x = c := by
    rw [show q x = (e.groupEquiv (QuotientGroup.mk' (pCore 2 L) k) :
      Atlas.G2.Model F) from hmark k]
    exact congrArg Subtype.val hk
  let A := B.subgroupOf H
  let E := A ⊔ A.map (MulAut.conj x).toMonoidHom
  have he : (A.map (MulAut.conj x).toMonoidHom).map q =
      (A.map q).map (MulAut.conj c).toMonoidHom := by
    rw [map_map, map_map]
    congr 1
    apply MonoidHom.ext
    intro y
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      map_mul, map_inv, hx]
  have hgen' : commutator (Atlas.G2.Model F) ≤ E.map q := by
    change _ ≤ (A ⊔ A.map (MulAut.conj x).toMonoidHom).map q
    rw [Subgroup.map_sup, he, hgen]
    exact le_top
  have hLE : L.subgroupOf H ≤ E ⊔ q.ker := by
    rw [← comap_map_eq]
    intro l hl
    apply hgen'
    have hh : l = inclusion le_sup_left (⟨l.val, hl⟩ : L) := rfl
    rw [hh, hmark]
    exact (e.groupEquiv (QuotientGroup.mk' (pCore 2 L) ⟨l.val, hl⟩)).property
  have hl : L.subgroupOf H ≤ pCore 2 H ⊔ E :=
    hLE.trans (sup_le le_sup_right (hker.trans le_sup_left))
  have hm := map_mono (f := H.subtype) hl
  rw [map_subgroupOf_eq_of_le (show L ≤ H from le_sup_left), Subgroup.map_sup] at hm
  have he' : (A.map (MulAut.conj x).toMonoidHom).map H.subtype =
      (A.map H.subtype).map (MulAut.conj k.val).toMonoidHom := by
    rw [map_map, map_map]
    rfl
  refine ⟨k, k.property, ?_⟩
  change L ≤ H.pCoreIn 2 ⊔ E.map H.subtype at hm
  dsimp only [E] at hm
  rw [Subgroup.map_sup, he', show A.map H.subtype = B from
    map_subgroupOf_eq_of_le hBH] at hm
  exact hm

/-- The core-product consumer with its generation and offender premises
discharged. The whole-Q index bound remains for the moved-cover producer. -/
theorem core_elementary_of_moved_chosen_index
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction (OrthogonalCover.action F))
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    {d : G} (hd : d ∈ normalizer (T : Set G))
    (hmove : ¬ V.map (MulAut.conj d).toMonoidHom ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hi : (centralizer (V.map (MulAut.conj d).toMonoidHom : Set G)).relIndex
      ((L ⊔ (T : Subgroup G)).pCoreIn 2) ≤ 8) :
    IsElementaryAbelian 2 ((L ⊔ (T : Subgroup G)).pCoreIn 2) ∧
      frattini ((L ⊔ (T : Subgroup G)).pCoreIn 2) = ⊥ := by
  obtain ⟨g, hg, hgen⟩ := moved_chosen_two_conjugate_generation h D structural e hne hd hmove
  exact g2Two_core_elementary_of_conjugate_index h D hne hescape
    (g2Two_block_of_weyl_model h D hescape e) _ g hg hgen hi

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
