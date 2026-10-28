module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.CubicNormalizerMarkedComplement
public import Theory.SpecificGroups.Janko3.SourceRecognition.CubicNormalizerModelPair

/-!
# The original cubic normalizer with its full pair marking

The original inverting involution makes the cubic action nontrivial, so the
split normalizer has the canonical 3 : PGL₂(9) model. Conjugacy of full pair
subgroups then retains the entire original overlap normalizer, as well as
the cubic kernel.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
open Janko23.J3Recognition.LocalSixteen Janko23.J3Recognition.Ambient
open Representation.CentralCubicNaturalFour
open Sporadic.Janko3.SourceRecognition
open Sporadic.Janko3.SourceRecognition.BaumeisterParabolics

/-- The actual cubic normalizer has the canonical model, carrying its entire
original pair intersection and original cubic kernel to the fixed model subgroups. -/
theorem literal_cubic_normalizer_model_pair
    {G : Type*} [Group G] [Finite G] {D : Seed G}
    (P : ReturningPair D) (hc : Janko23.OneInvolutionClass G)
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G)))
    (l : C ≃* LinearGroup) (a : A ≃* Plane)
    (ha : ∀ (c : C) (x : A), a (A.normalizerMonoidHom c x) = naturalAction (l c) (a x))
    (j : SingerField.Model →* G) (hj : PlaneTransport.FieldEmbedding A C a j) :
    let N := normalizer (zpowers (j cubic) : Set G)
    ∃ e : N ≃* CubicNormalizerModel.Model,
      ((normalizer (overlap j : Set G)).subgroupOf N).map e.toMonoidHom =
        CubicNormalizerModel.pair ∧
      (cubicNormalizerKernel (j cubic)).map e.toMonoidHom =
        CubicNormalizerModel.projection.ker := by
  let s := j cubic
  let N := normalizer (zpowers s : Set G)
  let V := cubicNormalizerKernel s
  let H := (normalizer (overlap j : Set G)).subgroupOf N
  have hs : orderOf s = 3 := (orderOf_injective j hj.1 _).trans cubic_order
  obtain ⟨_,y,K,_,_,_,_,_,hy,_,_,hK,⟨eK⟩,_⟩ :=
    literal_cubic_normalizer_marked_complement P hc A C l a ha j hj
  have hnc : ¬ V ≤ center N := by
    intro hcV
    let u : N := ⟨s,(zpowers s).le_normalizer (mem_zpowers s)⟩
    have hu : u ∈ V := mem_zpowers s
    have he := congrArg Subtype.val ((mem_center_iff.mp (hcV hu)) y)
    change (y:G) * s = s * (y:G) at he
    have hi : s = s⁻¹ := by rwa [he,mul_inv_cancel_right] at hy
    have hp : s ^ 2 = 1 := by rw [pow_two]; nth_rw 1 [hi]; exact inv_mul_cancel _
    have hd := orderOf_dvd_of_pow_eq_one hp
    norm_num [hs] at hd
  obtain ⟨eV,e0,heV,_,_,_⟩ := CubicNormalizerModel.exists_splitEquiv
    V K hK eK (cubicNormalizerKernel_card s hs) hnc
  have hV : V.map e0.toMonoidHom = CubicNormalizerModel.projection.ker := by
    rw [CubicNormalizerModel.projection_ker]
    apply le_antisymm
    · rintro _ ⟨v,hv,rfl⟩
      exact ⟨eV ⟨v,hv⟩,(heV ⟨v,hv⟩).symm⟩
    · rintro _ ⟨z,rfl⟩
      obtain ⟨v,rfl⟩ := eV.surjective z
      exact ⟨v,v.property,heV v⟩
  have hVN : V ≤ H := subgroupOf_mono N
    ((zpowers_le.mpr (mem_map_of_mem j cubic_mem)).trans (overlap j).le_normalizer)
  have hH : Nat.card H = 60 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (overlap_normalizer_le_cubic j hj.1)).toEquiv]
    obtain ⟨eH⟩ := literal_overlap_pair_equiv P hc A C a j hj
    rw [Nat.card_congr eH.toEquiv,Nat.card_prod]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,DihedralGroup.card]
  obtain ⟨g,hg⟩ := CubicNormalizerModel.exists_conjugating_pair
    (H.map e0.toMonoidHom) (hV ▸ map_mono hVN)
    ((card_map_of_injective e0.injective).trans hH)
  refine ⟨e0.trans (MulAut.conj g),?_,?_⟩
  · change H.map ((MulAut.conj g).toMonoidHom.comp e0.toMonoidHom) = _
    rw [←map_map,hg]
  · change V.map ((MulAut.conj g).toMonoidHom.comp e0.toMonoidHom) = _
    rw [←map_map,hV]
    exact Subgroup.Normal.map_conj_eq _ g

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
