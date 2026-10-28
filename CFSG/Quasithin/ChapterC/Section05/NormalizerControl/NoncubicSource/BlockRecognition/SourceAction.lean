module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.BlockRecognition.ImageAction
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.Kernel
/-!
# The original moved action is the full block action

The source identity [V₁,L]=U(L) and exact action kernel give an actual
intertwining equivalence between the moved representation and conjugation
on the complete U(L). No fixed layer is discarded.
Source: Aschbacher–Smith C.5.13, printed p.163.
-/
public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.DualOffender
open ConjugateSource.RankOne ChapterB.QuasisimpleSource ExceptionalRestrictions
variable {G : Type*} [Group G]
theorem source_blockU_actionEquiv_of_moved (V K N : Subgroup G)
    (hVN : V ≤ N) (hKN : K ≤ N) (hNV : N ≤ normalizer (V : Set G))
    [IsElementaryAbelian 2 V]
    (hI : ⁅V,conjugateSpanBy K N⁆ = U (conjugateSpanBy K N))
    (hL : IsShort (conjugateSpanBy K N)) :
    let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hVN).mpr hNV
    let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hVN
    let : IsElementaryAbelian 2 (blockU (conjugateSpanBy K N)) := hL.elementary
    let q := QuotientGroup.mk' (centralizer (V.subgroupOf N : Set N))
    (q.subgroupMap ((conjugateSpanBy K N).subgroupOf N)).ker = pCore 2 ((conjugateSpanBy K N).subgroupOf N) →
    Nonempty (ActionEquiv (uRepresentation hL)
      (movedRepresentation (V.subgroupOf N) (K.subgroupOf N))) := by
  let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hVN).mpr hNV
  let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hVN
  let : IsElementaryAbelian 2 (blockU (conjugateSpanBy K N)) := hL.elementary
  change ((QuotientGroup.mk' (centralizer (V.subgroupOf N : Set N))).subgroupMap
    ((conjugateSpanBy K N).subgroupOf N)).ker = pCore 2 ((conjugateSpanBy K N).subgroupOf N) →
    Nonempty (ActionEquiv (uRepresentation hL) (movedRepresentation (V.subgroupOf N) (K.subgroupOf N)))
  intro hk
  let L := conjugateSpanBy K N
  let I := ⁅V.subgroupOf N,normalClosure (K.subgroupOf N : Set N)⁆
  let W := (movedSpace (V.subgroupOf N) (K.subgroupOf N)).toSubmodule
  let ρ := movedRepresentation (V.subgroupOf N) (K.subgroupOf N)
  have hLN : L ≤ N := conjugateSpanBy_le_self hKN
  have hcl : normalClosure (K.subgroupOf N : Set N) = L.subgroupOf N :=
    normalClosure_subgroupOf_eq_conjugateSpanBy K N hKN
  let : (L.subgroupOf N).Normal := source_span_normal K N hKN
  have hImap : I.map N.subtype = U L := (source_moved_map V K N hVN hKN).trans hI
  have hwL (w : W) : ((w.val.toMul : V.subgroupOf N) : G) ∈ L := by
    have hw : (w.val.toMul : N) ∈ I := w.property
    change (w.val.toMul : N) ∈ ⁅V.subgroupOf N,normalClosure (K.subgroupOf N : Set N)⁆ at hw
    rw [hcl] at hw
    exact (show (w.val.toMul : N) ∈ L.subgroupOf N from (commutator_le_right _ _) hw)
  let j : Multiplicative W →* L :=
    { toFun := fun w => ⟨(w.toAdd.val.toMul : N),hwL w.toAdd⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro a b he
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun l : L => (l : G)) he
  have hr : j.range = blockU L := by
    apply map_injective L.subtype_injective
    rw [MonoidHom.range_eq_map,map_map]
    change (⊤ : Subgroup (Multiplicative W)).map (L.subtype.comp j) = U L
    rw [← hImap]
    apply le_antisymm
    · rintro a ⟨w,_,rfl⟩
      exact ⟨w.toAdd.val.toMul,w.toAdd.property,rfl⟩
    · rintro a ⟨i,hi,rfl⟩
      have hiV : i ∈ V.subgroupOf N := (commutator_le_left _ _) hi
      exact ⟨Multiplicative.ofAdd (⟨Additive.ofMul ⟨i,hiV⟩,hi⟩ : W),mem_top _,rfl⟩
  let q := QuotientGroup.mk' (centralizer (V.subgroupOf N : Set N))
  let f : L →* closureImage (V.subgroupOf N) (K.subgroupOf N) :=
    { toFun := fun l => ⟨q ⟨l,hLN l.property⟩,mem_map_of_mem q (hcl.symm ▸ l.property)⟩
      map_one' := Subtype.ext (map_one q)
      map_mul' := fun a b => Subtype.ext (map_mul q ⟨a,hLN a.property⟩ ⟨b,hLN b.property⟩) }
  have hf : Function.Surjective f := by
    rintro ⟨a,i,hi,rfl⟩
    have hiL : (i : G) ∈ L := by
      have hh : i ∈ L.subgroupOf N := hcl ▸ hi
      exact hh
    exact ⟨⟨i,hiL⟩,rfl⟩
  have hkf : f.ker = pCore 2 L := by
    let E := subgroupOfEquivOfLe hLN
    have hp : (pCore 2 (L.subgroupOf N)).map E.toMonoidHom = pCore 2 L := pCore_map_iso 2 E
    ext l
    constructor
    · intro hl
      change f l = 1 at hl
      have hh : E.symm l ∈ (q.subgroupMap (L.subgroupOf N)).ker := by
        apply MonoidHom.mem_ker.mpr
        apply Subtype.ext
        exact congrArg (fun c : closureImage (V.subgroupOf N) (K.subgroupOf N) =>
          (c : N ⧸ centralizer (V.subgroupOf N : Set N))) hl
      rw [hk] at hh
      have hm := mem_map_of_mem E.toMonoidHom hh
      change E (E.symm l) ∈ (pCore 2 (L.subgroupOf N)).map E.toMonoidHom at hm
      rw [E.apply_symm_apply] at hm
      exact hp ▸ hm
    · intro hl
      rw [←hp] at hl
      obtain ⟨a,ha,rfl⟩ := hl
      rw [←hk] at ha
      change (q.subgroupMap (L.subgroupOf N)) a = 1 at ha
      apply MonoidHom.mem_ker.mpr
      apply Subtype.ext
      exact congrArg (fun c : (L.subgroupOf N).map q =>
        (c : N ⧸ centralizer (V.subgroupOf N : Set N))) ha
  apply blockU_actionEquiv_of_image hL ρ f hf hkf j hj hr
  intro l w
  apply Subtype.ext
  change ((centralizerQuotient (V.subgroupOf N) (q ⟨l,hLN l.property⟩) w.val).toMul : G) = _
  exact congrArg N.subtype (centralizerQuotient_apply (V.subgroupOf N) ⟨l,hLN l.property⟩ w.val)
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.DualOffender
