module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.CubicComplementModelSource
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.MarkedAmalgamSource
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.CompletionPlaneIntersection
public import Theory.SpecificGroups.Janko3.SourceRecognition.CubicNormalizerFullThird

/-!
# The actual third overlap with the full pair marking retained

The original cubic complement intersects the original plane normalizer in
an actual A₅. The literal triple intersection is the original order-thirty
overlap. These source facts identify the entire plane/cubic intersection
with the fixed third-overlap model. The correcting automorphism fixes the
full order-sixty pair pointwise, so the same sixteen-field pair agreement
and full cubic kernel are retained.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
open Janko23.J3Recognition.LocalSixteen Janko23.J3Recognition.Ambient
open Janko23.J3Recognition.Ambient.Seventeen
open Representation.CentralCubicNaturalFour
open Sporadic.Janko3.SourceRecognition
open Sporadic.Janko3.SourceRecognition.BaumeisterParabolics

private theorem map_eq_self_of_fixed {E : Type*} [Group E]
    (H : Subgroup E) (τ : MulAut E) (hfix : ∀ x ∈ H, τ x = x) :
    H.map τ.toMonoidHom = H := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    change τ x ∈ H
    rw [hfix x hx]
    exact hx
  · intro x hx
    exact ⟨x,hx,hfix x hx⟩

/-- The original source supplies full pair agreement and the fixed third
overlap simultaneously, with its same chosen cubic complement and kernel.
No subgroup-alignment or third-overlap hypothesis is added. -/
theorem literal_canonical_third_pair_models
    {G : Type*} [Group G] [Finite G] {D : Seed G}
    (P : ReturningPair D) (hc : Janko23.OneInvolutionClass G)
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G)))
    (l : C ≃* LinearGroup) (a : A ≃* Plane)
    (hC : (A.subgroupOf (normalizer (A : Set G))).IsComplement' C)
    (ha : ∀ (c : C) (x : A), a (A.normalizerMonoidHom c x) = naturalAction (l c) (a x))
    (j : SingerField.Model →* G) (hj : PlaneTransport.FieldEmbedding A C a j) :
    let L := completion j.range (overlap j)
    let N := normalizer (zpowers (j cubic) : Set G)
    ∃ (K : Subgroup N) (e₁ : L ≃* Theory.PSL2.BinaryFourFieldExtension.Model)
      (e₃ : N ≃* CubicNormalizerModel.Model),
      (cubicNormalizerKernel (j cubic)).IsComplement' K ∧
      ((L ⊓ N).subgroupOf L).map e₁.toMonoidHom =
        Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam.pair ∧
      ((L ⊓ N).subgroupOf N).map e₃.toMonoidHom = CubicNormalizerModel.pair ∧
      (cubicNormalizerKernel (j cubic)).map e₃.toMonoidHom =
        CubicNormalizerModel.projection.ker ∧
      K.map e₃.toMonoidHom =
        (SemidirectProduct.inr : CubicNormalizerModel.P →* CubicNormalizerModel.Model).range ∧
      ((normalizer (A : Set G)).subgroupOf N).map e₃.toMonoidHom =
        CubicNormalizerModel.thirdOverlap ∧
      ∀ x : (L ⊓ N : Subgroup G),
        ∃ z : Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam.pair,
          e₁ ⟨x,x.property.1⟩ = (z : Theory.PSL2.BinaryFourFieldExtension.Model) ∧
          e₃ ⟨x,x.property.2⟩ =
            (CubicNormalizerModel.modelPairEquiv z : CubicNormalizerModel.Model) := by
  let L := completion j.range (overlap j)
  let N := normalizer (zpowers (j cubic) : Set G)
  let V := cubicNormalizerKernel (j cubic)
  let H := normalizer (overlap j : Set G)
  let Cn := (normalizer (A : Set G)).subgroupOf N
  let Hp := (L ⊓ N).subgroupOf N
  obtain ⟨B,y,K,_hB,_eB,_hfB,_hyH,_hy2,_hyinv,_hyB,_hKeq,hK,⟨eK⟩,
    _hBK,_hpair,_ePair,_hplane,hfive,_hgen⟩ :=
    literal_marked_amalgam_source P hc A C l a hC ha j hj
  obtain ⟨e₁,e₃,h₁,h₃,hV,hKm,hcompat⟩ :=
    literal_canonical_pair_maps_of_complement P hc A C a j hj K hK eK
  have hi : L ⊓ N = H := literal_completion_cubic_normalizer_intersection P hc A C a j hj
  have hHN : H ≤ N := overlap_normalizer_le_cubic j hj.1
  have hHL : H ≤ L := le_sup_right
  have hplane : L ⊓ normalizer (A : Set G) = j.range :=
    literal_completion_plane_intersection P hc A C l a hC ha j hj
  have htriple : normalizer (A : Set G) ⊓ H = overlap j := by
    rw [←point_intersection_normalizer j hj.1,←hplane]
    ext x
    constructor
    · intro hx
      exact ⟨⟨hHL hx.2,hx.1⟩,hx.2⟩
    · intro hx
      exact ⟨hx.1.2,hx.2⟩
  have hVC : V ≤ Cn := by
    have hs : zpowers (j cubic) ≤ normalizer (A : Set G) :=
      zpowers_le.mpr (hj.2.1 ⟨cubic,rfl⟩)
    exact subgroupOf_mono N hs
  have hmapK : (Cn ⊓ K).map N.subtype = normalizer (A : Set G) ⊓ K.map N.subtype := by
    ext x
    constructor
    · rintro ⟨n,hn,rfl⟩
      exact ⟨hn.1,⟨n,hn.2,rfl⟩⟩
    · rintro ⟨hx,⟨n,hn,rfl⟩⟩
      exact ⟨n,⟨hx,hn⟩,rfl⟩
  have hfiveN : Nonempty ((Cn ⊓ K : Subgroup N) ≃* alternatingGroup (Fin 5)) :=
    ⟨((Cn ⊓ K).equivMapOfInjective N.subtype N.subtype_injective).trans
      ((MulEquiv.subgroupCongr hmapK).trans hfive.some)⟩
  have hmapH : (Cn ⊓ Hp).map N.subtype = overlap j := by
    rw [←htriple]
    ext x
    constructor
    · rintro ⟨n,hn,rfl⟩
      exact ⟨hn.1,hi ▸ hn.2⟩
    · intro hx
      refine ⟨⟨x,hHN hx.2⟩,⟨hx.1,?_⟩,rfl⟩
      change x ∈ L ⊓ N
      exact hi.symm ▸ hx.2
  have hcard : Nat.card (Cn ⊓ Hp : Subgroup N) = 30 := by
    rw [←card_map_of_injective N.subtype_injective,hmapH,
      Nat.card_congr (overlapEquiv j hj.1).toEquiv]
    simp [Sporadic.Janko3.SourceRecognition.Seventeen.Complement,
      Nat.card_eq_fintype_card,Fintype.card_multiplicative,DihedralGroup.card]
  let Cm := Cn.map e₃.toMonoidHom
  have hk : CubicNormalizerModel.projection.ker ≤ Cm := hV ▸ map_mono hVC
  have heK : (Cn ⊓ K).map e₃.toMonoidHom =
      Cm ⊓ (SemidirectProduct.inr : CubicNormalizerModel.P →* CubicNormalizerModel.Model).range := by
    rw [map_inf _ _ _ e₃.injective,hKm]
  have hmFive : Nonempty ((Cm ⊓
      (SemidirectProduct.inr : CubicNormalizerModel.P →* CubicNormalizerModel.Model).range :
      Subgroup CubicNormalizerModel.Model) ≃* alternatingGroup (Fin 5)) :=
    ⟨(MulEquiv.subgroupCongr heK.symm).trans
      (((Cn ⊓ K).equivMapOfInjective e₃.toMonoidHom e₃.injective).symm.trans hfiveN.some)⟩
  have heH : (Cn ⊓ Hp).map e₃.toMonoidHom = Cm ⊓ CubicNormalizerModel.pair := by
    rw [map_inf _ _ _ e₃.injective,h₃]
  have hmCard : Nat.card (Cm ⊓ CubicNormalizerModel.pair : Subgroup CubicNormalizerModel.Model) = 30 := by
    rw [←heH,card_map_of_injective e₃.injective,hcard]
  obtain ⟨τ,hfix,hker,hcomp,hthird⟩ :=
    CubicNormalizerModel.exists_full_third_alignment Cm hk hmFive hmCard
  refine ⟨K,e₁,e₃.trans τ,hK,h₁,?_,?_,?_,?_,?_⟩
  · change Hp.map (τ.toMonoidHom.comp e₃.toMonoidHom) = _
    rw [←map_map,h₃,map_eq_self_of_fixed _ τ hfix]
  · change V.map (τ.toMonoidHom.comp e₃.toMonoidHom) = _
    rw [←map_map,hV,map_eq_self_of_fixed _ τ hker]
  · change K.map (τ.toMonoidHom.comp e₃.toMonoidHom) = _
    rw [←map_map,hKm,hcomp]
  · change Cn.map (τ.toMonoidHom.comp e₃.toMonoidHom) = _
    rw [←map_map]
    exact hthird
  · intro x
    obtain ⟨z,hz₁,hz₃⟩ := hcompat x
    refine ⟨z,hz₁,?_⟩
    change τ (e₃ ⟨x,x.property.2⟩) = _
    rw [hz₃]
    exact hfix _ (CubicNormalizerModel.modelPairEquiv z).property
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
