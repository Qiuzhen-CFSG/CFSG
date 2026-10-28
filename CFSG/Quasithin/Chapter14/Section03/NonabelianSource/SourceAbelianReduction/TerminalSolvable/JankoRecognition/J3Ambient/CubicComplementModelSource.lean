module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.CompatiblePairModelSource
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.TrianglePairGenerators
public import Theory.SpecificGroups.Janko3.SourceRecognition.CubicNormalizerComplementPair
public import Theory.SpecificGroups.Janko3.SourceRecognition.CubicModelPairEquiv

/-!
# The original pair models retaining the same cubic complement

The cubic normalizer model can align the full pair by conjugation inside its
projective complement. It therefore retains the specified original complement,
including its original A₅ plane intersection. The sixteen-field correction
then gives pointwise agreement on the full pair without changing that map.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
open Janko23.J3Recognition.LocalSixteen Janko23.J3Recognition.Ambient
open Janko23.J3Recognition.Ambient.Seventeen
open Representation.CentralCubicNaturalFour
open Sporadic.Janko3.SourceRecognition
open Sporadic.Janko3.SourceRecognition.BaumeisterParabolics

/-- A given original cubic complement is retained together with the full pair
and the original cubic kernel. -/
theorem literal_cubic_model_pair_of_complement
    {G : Type*} [Group G] [Finite G] {D : Seed G}
    (P : ReturningPair D) (hc : Janko23.OneInvolutionClass G)
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G))) (a : A ≃* Plane)
    (j : SingerField.Model →* G) (hj : PlaneTransport.FieldEmbedding A C a j)
    (K : Subgroup (normalizer (zpowers (j cubic) : Set G)))
    (hK : (cubicNormalizerKernel (j cubic)).IsComplement' K)
    (eK : K ≃* CubicNormalizerModel.P) :
    let N := normalizer (zpowers (j cubic) : Set G)
    ∃ e : N ≃* CubicNormalizerModel.Model,
      ((normalizer (overlap j : Set G)).subgroupOf N).map e.toMonoidHom =
        CubicNormalizerModel.pair ∧
      (cubicNormalizerKernel (j cubic)).map e.toMonoidHom =
        CubicNormalizerModel.projection.ker ∧
      K.map e.toMonoidHom =
        (SemidirectProduct.inr : CubicNormalizerModel.P →* CubicNormalizerModel.Model).range := by
  let s := j cubic
  let N := normalizer (zpowers s : Set G)
  let V := cubicNormalizerKernel s
  let H := (normalizer (overlap j : Set G)).subgroupOf N
  have hs : orderOf s = 3 := (orderOf_injective j hj.1 _).trans cubic_order
  have hnc : ¬ V ≤ center N := by
    intro hcV
    obtain ⟨y,hy,_,hi,_⟩ := literal_triangle_pair_generators P hc A C a j hj
    let yN : N := ⟨y,overlap_normalizer_le_cubic j hj.1 hy.1⟩
    let u : N := ⟨s,(zpowers s).le_normalizer (mem_zpowers s)⟩
    have hu : u ∈ V := mem_zpowers s
    have he := congrArg Subtype.val ((mem_center_iff.mp (hcV hu)) yN)
    change y * s = s * y at he
    have hinv : s = s⁻¹ := by rwa [he,mul_inv_cancel_right] at hi
    have hp : s ^ 2 = 1 := by rw [pow_two]; nth_rw 1 [hinv]; exact inv_mul_cancel _
    have hd := orderOf_dvd_of_pow_eq_one hp
    norm_num [hs] at hd
  have hVH : V ≤ H := subgroupOf_mono N
    ((zpowers_le.mpr (mem_map_of_mem j cubic_mem)).trans (overlap j).le_normalizer)
  have hH : Nat.card H = 60 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (overlap_normalizer_le_cubic j hj.1)).toEquiv]
    obtain ⟨eH⟩ := literal_overlap_pair_equiv P hc A C a j hj
    rw [Nat.card_congr eH.toEquiv,Nat.card_prod]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,DihedralGroup.card]
  exact CubicNormalizerModel.exists_splitEquiv_pair V K H hK eK
    (cubicNormalizerKernel_card s hs) hnc hVH hH

/-- The canonical simultaneous pair maps retain any specified original cubic
complement, with no supplied identification of the two model pairs. -/
theorem literal_canonical_pair_maps_of_complement
    {G : Type*} [Group G] [Finite G] {D : Seed G}
    (P : ReturningPair D) (hc : Janko23.OneInvolutionClass G)
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G))) (a : A ≃* Plane)
    (j : SingerField.Model →* G) (hj : PlaneTransport.FieldEmbedding A C a j)
    (K : Subgroup (normalizer (zpowers (j cubic) : Set G)))
    (hK : (cubicNormalizerKernel (j cubic)).IsComplement' K)
    (eK : K ≃* CubicNormalizerModel.P) :
    let L := completion j.range (overlap j)
    let N := normalizer (zpowers (j cubic) : Set G)
    ∃ (e₁ : L ≃* Theory.PSL2.BinaryFourFieldExtension.Model)
      (e₃ : N ≃* CubicNormalizerModel.Model),
      ((L ⊓ N).subgroupOf L).map e₁.toMonoidHom =
        Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam.pair ∧
      ((L ⊓ N).subgroupOf N).map e₃.toMonoidHom = CubicNormalizerModel.pair ∧
      (cubicNormalizerKernel (j cubic)).map e₃.toMonoidHom =
        CubicNormalizerModel.projection.ker ∧
      K.map e₃.toMonoidHom =
        (SemidirectProduct.inr : CubicNormalizerModel.P →* CubicNormalizerModel.Model).range ∧
      ∀ x : (L ⊓ N : Subgroup G),
        ∃ z : Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam.pair,
          e₁ ⟨x,x.property.1⟩ = (z : Theory.PSL2.BinaryFourFieldExtension.Model) ∧
          e₃ ⟨x,x.property.2⟩ =
            (CubicNormalizerModel.modelPairEquiv z : CubicNormalizerModel.Model) := by
  let L := completion j.range (overlap j)
  let N := normalizer (zpowers (j cubic) : Set G)
  let mark := Janko23.J3Recognition.Ambient.BaumeisterParabolics.original_marking_of_pair_triangle
    j hj.1 (literal_overlap_pair_equiv P hc A C a j hj).some
    (literal_triangle_equiv P hc A C a j hj).some
  obtain ⟨e₁,_,hpair,_,_⟩ := mark.recognition
  obtain ⟨e₃,hpair₃,hkernel,hcomplement⟩ :=
    literal_cubic_model_pair_of_complement P hc A C a j hj K hK eK
  have hi : L ⊓ N = normalizer (overlap j : Set G) :=
    literal_completion_cubic_normalizer_intersection P hc A C a j hj
  have h₁ : ((L ⊓ N).subgroupOf L).map e₁.toMonoidHom =
      Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam.pair := by
    rw [hi]
    exact hpair
  have h₃ : ((L ⊓ N).subgroupOf N).map e₃.toMonoidHom = CubicNormalizerModel.pair := by
    rw [hi]
    exact hpair₃
  obtain ⟨f,hf,hcompat⟩ := Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam.compatible_pair_maps
    L N CubicNormalizerModel.pair e₁ e₃ h₁ h₃ CubicNormalizerModel.modelPairEquiv
  exact ⟨f,e₃,hf,h₃,hkernel,hcomplement,hcompat⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
