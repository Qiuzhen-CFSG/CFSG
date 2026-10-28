module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.ZeroClosure.Mutual.SmallMoved
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.ZeroClosure.Mutual.Pair
public import Theory.ElementaryAbelian.Injective

/-!
# Subspace actors on the actual reverse conjugate

A subspace P of W defines an ambient subgroup. Conjugation by g⁻¹ turns
its action on Wᵍ into an action on W. The image rank is exactly the fixed
codimension on P, and its group commutator is bounded by the original
linear displacement span. Thus a plane-sized moved space and fixed
codimension at least two contradict the proved rank-one bound for inner
actors on a natural module plus its dual.

Only mutual normalization is used; W is not assumed normal in G. The
actual application is the small-rank branch in `FiveSmall`.
Source: Aschbacher--Smith, 12.1.3, printed pp.789--790 (PDF806--807).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender Module
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.ChapterE CFSG.Quasithin.ChapterH.NaturalDual
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.ZeroClosure.Mutual
variable {G : Type*} [Group G] [Finite G] {W : Subgroup G}
  [IsElementaryAbelian 2 W]

/-- A subspace of the actual elementary group, embedded back in G. -/
private def ambientSubspace (P : Submodule (ZMod 2) (Additive W)) : Subgroup G :=
  P.toAddSubgroup.toSubgroup'.map W.subtype

omit [Finite G] in
private theorem ambientSubspace_le (P : Submodule (ZMod 2) (Additive W)) :
    ambientSubspace P ≤ W := by
  rintro _ ⟨w,_,rfl⟩
  exact w.property

omit [Finite G] in
@[simp] private theorem mem_ambientSubspace (P : Submodule (ZMod 2) (Additive W))
    (w : W) : (w : G) ∈ ambientSubspace P ↔ Additive.ofMul w ∈ P := by
  constructor
  · rintro ⟨u,hu,he⟩
    exact (Subtype.ext he : u = w) ▸ hu
  · intro hw
    exact ⟨w,hw,rfl⟩

omit [Finite G] in
private theorem subgroupSpace_ambientSubspace (P : Submodule (ZMod 2) (Additive W)) :
    subgroupSpace W (ambientSubspace P) = P := by
  ext w
  rw [mem_subgroupSpace]
  exact mem_ambientSubspace P w.toMul

private theorem rank_ambientSubspace (P : Submodule (ZMod 2) (Additive W)) :
    rank (ambientSubspace P) = finrank (ZMod 2) P := by
  have hd := subgroupSpace_finrank W (ambientSubspace P) (ambientSubspace_le P)
  rw [subgroupSpace_ambientSubspace] at hd
  exact hd.symm

omit [Finite G] in
private theorem ambientSubspace_fixed (P : Submodule (ZMod 2) (Additive W))
    (A : Subgroup G) (hA : A ≤ normalizer (W : Set G)) :
    ambientSubspace (P ⊓ fixedSpace (automizerRepresentation W) (inducedAutomizer W A)) =
      ambientSubspace P ⊓ centralizer (A : Set G) := by
  ext x
  constructor
  · intro hx
    have hxW := ambientSubspace_le _ hx
    have hh := (mem_ambientSubspace _ ⟨x,hxW⟩).mp hx
    exact ⟨(mem_ambientSubspace P ⟨x,hxW⟩).mpr hh.1,
      (mem_fixedSpace_inducedAutomizer W A hA _).mp hh.2⟩
  · intro hx
    have hxW := ambientSubspace_le P hx.1
    exact (mem_ambientSubspace _ ⟨x,hxW⟩).mpr
      ⟨(mem_ambientSubspace P ⟨x,hxW⟩).mp hx.1,
        (mem_fixedSpace_inducedAutomizer W A hA _).mpr hx.2⟩

omit [Finite G] in
/-- The module displacement span bounds the literal ambient commutator. -/
private theorem commutator_le_ambientSubspace (P : Submodule (ZMod 2) (Additive W))
    (A : Subgroup G) (hA : A ≤ normalizer (W : Set G)) :
    ⁅ambientSubspace P,A⁆ ≤ ambientSubspace
      (subspaceCommutator (automizerRepresentation W) P (inducedAutomizer W A)) := by
  rw [Subgroup.commutator_comm]
  apply commutator_le.mpr
  intro a ha u hu
  let v : Additive W := Additive.ofMul ⟨u,ambientSubspace_le P hu⟩
  let b : normalizer (W : Set G) := ⟨a,hA ha⟩
  let i := W.normalizerMonoidHom.rangeRestrict b
  have hi : i ∈ inducedAutomizer W A := ⟨b,ha,rfl⟩
  have hv : v ∈ P := (mem_ambientSubspace P v.toMul).mp hu
  have hm : automizerRepresentation W i v - v ∈
      subspaceCommutator (automizerRepresentation W) P (inducedAutomizer W A) :=
    Submodule.subset_span ⟨i,hi,v,hv,rfl⟩
  refine ⟨(automizerRepresentation W i v - v).toMul,hm,?_⟩
  rw [toMul_sub,div_eq_mul_inv]
  rfl

omit [Finite G] in
private theorem map_centralizer_equiv (U : Subgroup G) (e : G ≃* G) :
    (centralizer (U : Set G)).map e.toMonoidHom = centralizer (U.map e.toMonoidHom : Set G) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro x hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    intro y hy
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hx (e y) (mem_map_of_mem _ hy)

/-- Reverse the action of a literal subspace, retaining its exact image rank. -/
private theorem reverse_subspace_rank (g : G)
    (hA : W.map (MulAut.conj g).toMonoidHom ≤ normalizer (W : Set G))
    (hW : W ≤ normalizer (W.map (MulAut.conj g).toMonoidHom : Set G))
    (P : Submodule (ZMod 2) (Additive W)) :
    rank (inducedAutomizer W ((ambientSubspace P).map (MulAut.conj g⁻¹).toMonoidHom)) =
      finrank (ZMod 2) P - finrank (ZMod 2)
        ↥(P ⊓ fixedSpace (automizerRepresentation W)
          (inducedAutomizer W (W.map (MulAut.conj g).toMonoidHom))) := by
  let A := W.map (MulAut.conj g).toMonoidHom
  let U := ambientSubspace P
  let e := MulAut.conj g⁻¹
  have hUn : U.map e.toMonoidHom ≤ normalizer (W : Set G) :=
    (map_mono (ambientSubspace_le P)).trans (reverse_normalizes g hW)
  rw [rank_inducedAutomizer W _ hUn]
  have he : A.map e.toMonoidHom = W := Subgroup.conjBy_inv W g
  have hc : (U ⊓ centralizer (A : Set G)).map e.toMonoidHom =
      U.map e.toMonoidHom ⊓ centralizer (W : Set G) := by
    rw [Subgroup.map_inf _ _ _ e.injective, map_centralizer_equiv,he]
  unfold subgroupCorank
  rw [←hc,relIndex_map_map_of_injective _ _ e.injective]
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_injective
    (inclusion (ambientSubspace_le P)) (inclusion_injective _)
  rw [←log_card_sub_log_card_eq_log_relIndex U _ inf_le_left]
  change rank U - rank (U ⊓ centralizer (A : Set G)) = _
  rw [←ambientSubspace_fixed P A hA,rank_ambientSubspace,rank_ambientSubspace]

/-- A small moved subspace gives an impossible inner actor on the reverse
conjugate when its own fixed codimension is at least two. -/
theorem reverse_subspace_false {n : ℕ}
    (S : SourceSetup n (Automizer W) (Additive W))
    (hρ : S.representation = automizerRepresentation W) (g : G)
    (hA : W.map (MulAut.conj g).toMonoidHom ≤ normalizer (W : Set G))
    (hW : W ≤ normalizer (W.map (MulAut.conj g).toMonoidHom : Set G))
    (hi : inducedAutomizer W (W.map (MulAut.conj g⁻¹).toMonoidHom) ≤
      componentLayer (Automizer W))
    (P : Submodule (ZMod 2) (Additive W))
    (hc : 2 ≤ finrank (ZMod 2) P - finrank (ZMod 2)
      ↥(P ⊓ fixedSpace S.representation
        (inducedAutomizer W (W.map (MulAut.conj g).toMonoidHom))))
    (hm : finrank (ZMod 2) (subspaceCommutator S.representation P
      (inducedAutomizer W (W.map (MulAut.conj g).toMonoidHom))) ≤ 2) : False := by
  let A := W.map (MulAut.conj g).toMonoidHom
  let U := ambientSubspace P
  let e := MulAut.conj g⁻¹
  let U' := U.map e.toMonoidHom
  have hUn : U' ≤ normalizer (W : Set G) :=
    (map_mono (ambientSubspace_le P)).trans (reverse_normalizes g hW)
  have hi' : inducedAutomizer W U' ≤ componentLayer (Automizer W) :=
    (map_mono (show U'.subgroupOf (normalizer (W : Set G)) ≤
      (W.map e.toMonoidHom).subgroupOf (normalizer (W : Set G)) from
        fun _ hx => map_mono (ambientSubspace_le P) hx)).trans hi
  have hb : rank ⁅W,U'⁆ ≤ 2 := by
    have he : A.map e.toMonoidHom = W := Subgroup.conjBy_inv W g
    have hcomm : ⁅W,U'⁆ = ⁅U,A⁆.map e.toMonoidHom := by
      rw [Subgroup.map_commutator,he,Subgroup.commutator_comm]
    rw [hcomm,rank_map_injective e.toMonoidHom e.injective]
    have hle := commutator_le_ambientSubspace P A hA
    have hh := Nat.log_monotone (b := 2) (Subgroup.card_le_of_le hle)
    change rank ⁅U,A⁆ ≤ rank (ambientSubspace _) at hh
    rw [rank_ambientSubspace,←hρ] at hh
    exact hh.trans hm
  have hbound := actual_inner_small_moved S hρ U' hUn hi' hb
  have hr := reverse_subspace_rank g hA hW P
  rw [←hρ] at hr
  change rank (inducedAutomizer W U') = _ at hr
  omega
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.ZeroClosure.Mutual
