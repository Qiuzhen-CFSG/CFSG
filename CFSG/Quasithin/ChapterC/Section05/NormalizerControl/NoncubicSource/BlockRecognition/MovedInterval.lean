module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.BlockRecognition.ImageInterval
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.DualOffender.MovedCore
/-!
# The original moved module realizes the intrinsic block interval

The canonical subgroup maps send I=[V,⟨K^N⟩] bijectively onto the actual
embedded U(L), where L=⟨K^N⟩. The image action intertwines conjugation by
L. Irr⁺ therefore gives exactly the C.1.7 invariant-subgroup interval,
including its central layer, without a new quotient-identification premise.
Source: Aschbacher–Smith C.5.13, printed p.163.
-/
public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.DualOffender
open ConjugateSource.RankOne
variable {G : Type*} [Group G]

theorem source_blockModuleIrreducible_of_moved (V K N : Subgroup G)
    (hVN : V ≤ N) (hKN : K ≤ N) (hNV : N ≤ normalizer (V : Set G))
    [IsElementaryAbelian 2 V]
    (hI : ⁅V,conjugateSpanBy K N⁆ = U (conjugateSpanBy K N)) :
    let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hVN).mpr hNV
    let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hVN
    IsIrrPlus (movedRepresentation (V.subgroupOf N) (K.subgroupOf N)) ⊤ ⊤ →
      BlockModuleIrreducible (conjugateSpanBy K N) := by
  let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hVN).mpr hNV
  let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hVN
  change IsIrrPlus (movedRepresentation (V.subgroupOf N) (K.subgroupOf N)) ⊤ ⊤ →
    BlockModuleIrreducible (conjugateSpanBy K N)
  intro hi
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
  apply blockModuleIrreducible_of_isIrrPlus_image ρ f hf j hj hr _ hi
  intro l w
  apply Subtype.ext
  change ((centralizerQuotient (V.subgroupOf N) (q ⟨l,hLN l.property⟩) w.val).toMul : G) = _
  exact congrArg N.subtype (centralizerQuotient_apply (V.subgroupOf N) ⟨l,hLN l.property⟩ w.val)
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.DualOffender
