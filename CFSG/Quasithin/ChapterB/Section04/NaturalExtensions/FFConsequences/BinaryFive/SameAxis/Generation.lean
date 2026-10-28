module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.BinaryFive.SameAxis.Propagation
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.BinaryFive.SameAxis.Generation.Linear

/-!
# Literal normalizer generation for the rank-four same-axis position

The native linear-group proofs are transported through the coherent natural
marking `BinaryFive.groupEquiv`. Injective subgroup maps preserve the marked
radicals, their intersection and both actual normalizers. The rank-four
hypothesis gives order sixteen because the offender lies in a two-group.

The final consumer applies the established quadraticity propagation theorem
to the original representation. No splitting or quadraticity of the ambient
radical is assumed. Source: Aschbacher–Smith, combined manuscript of
1 March 2004, B.4.9, final paragraph on printed p.95.
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.DoubleNatural.BinaryFive.SameAxis
variable {G K : Type*} [Group G] [Group K]

private theorem generation_of_map (e : G ≃* K) (B R X : Subgroup G)
    (h : R.map e.toMonoidHom ≤ ⨆ x : X.map e.toMonoidHom,
      (B.map e.toMonoidHom).map (MulAut.conj x.val).toMonoidHom) :
    R ≤ ⨆ x : X, B.map (MulAut.conj x.val).toMonoidHom := by
  let D := ⨆ x : X, B.map (MulAut.conj x.val).toMonoidHom
  have hle : (⨆ x : X.map e.toMonoidHom,
      (B.map e.toMonoidHom).map (MulAut.conj x.val).toMonoidHom) ≤ D.map e.toMonoidHom := by
    apply iSup_le
    intro x
    obtain ⟨g, hg, he⟩ := x.property
    rintro y ⟨b, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨(MulAut.conj g) a, ?_, ?_⟩
    · exact (le_iSup (fun x : X => B.map (MulAut.conj x.val).toMonoidHom) ⟨g, hg⟩)
        ⟨a, ha, rfl⟩
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
      change e g = x.val at he
      rw [he]
  intro r hr
  obtain ⟨t, ht, he⟩ := hle (h ⟨r, hr, rfl⟩)
  exact e.injective he ▸ ht


private theorem normalizerGeneration_of_map (e : G ≃* K) (B C R : Subgroup G)
    (h : NormalizerGeneration (B.map e.toMonoidHom) (C.map e.toMonoidHom)
      (R.map e.toMonoidHom)) : NormalizerGeneration B C R := by
  constructor
  · apply generation_of_map e B R (normalizer (R : Set G) ⊓ normalizer (C : Set G))
    have he : (normalizer (R : Set G) ⊓ normalizer (C : Set G) : Subgroup G).map e.toMonoidHom =
        normalizer (R.map e.toMonoidHom : Set K) ⊓ normalizer (C.map e.toMonoidHom : Set K) := by
      rw [Subgroup.map_inf _ _ _ e.injective, Subgroup.map_equiv_normalizer_eq,
        Subgroup.map_equiv_normalizer_eq]
    rw [he]
    exact h.1
  · apply generation_of_map e C R (normalizer (R : Set G))
    rw [Subgroup.map_equiv_normalizer_eq]
    exact h.2


end CFSG.Quasithin.ChapterB.NaturalExtensions.DoubleNatural.BinaryFive.SameAxis

open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.DoubleNatural.BinaryFive.SameAxis
open QuasisimpleSource BinaryLinear.OuterCyclic
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {F : BinaryField} {ρ : Representation (ZMod 2) G V}

/-- Both literal generation claims in the rank-four source position. -/
theorem normalizerGeneration_of_rankFourPosition (d : DoubleNatural F 5 ρ)
    (hF : F.degree = 1) {B : Subgroup G} {W H : Submodule (ZMod 2) (Space 5)}
    (hpos : RankFourPosition d hF B W H) :
    NormalizerGeneration B (B ⊓ markedRadical d hF H) (markedRadical d hF W) := by
  let e := groupEquiv d hF
  let A := B.map e.toMonoidHom
  have hmap (U : Submodule (ZMod 2) (Space 5)) :
      (markedRadical d hF U).map e.toMonoidHom = BinaryLinear.radical U := by
    exact Subgroup.map_comap_eq_self_of_surjective e.surjective _
  have hAR : A ≤ BinaryLinear.radical W := by
    rintro a ⟨b, hb, rfl⟩
    exact hpos.le_radical hb
  have hAC : (B ⊓ markedRadical d hF H).map e.toMonoidHom =
      A ⊓ BinaryLinear.radical H := by
    rw [Subgroup.map_inf _ _ _ e.injective, hmap]
  have hcard : Nat.card A = 16 := by
    have hp : IsPGroup 2 A := (BinaryLinear.radical_two W).to_le hAR
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    have hr : rank A = 4 := by
      unfold rank
      rw [show Nat.card A = Nat.card B from Subgroup.card_map_of_injective e.injective]
      exact hpos.rank_four
    rw [rank, hn, Nat.log_pow (by decide : 1 < 2)] at hr
    rw [hn, hr]
    norm_num
  have hcardC : Nat.card (A ⊓ BinaryLinear.radical H : Subgroup _) = 2 := by
    rw [← hAC, Subgroup.card_map_of_injective e.injective]
    exact hpos.intersection_card
  have hC0 : (A ⊓ BinaryLinear.radical H : Subgroup _) ≠ ⊥ := by
    intro he
    rw [he, Subgroup.card_bot] at hcardC
    omega
  apply normalizerGeneration_of_map e
  rw [hmap, hAC]
  constructor
  · exact LinearGeneration.first_generation (by simp [Space]) hpos.dim_three
      hpos.dim_hyperplane hpos.le_hyperplane A hAR hcard hcardC
  · exact LinearGeneration.second_generation (by simp [Space]) hpos.dim_three
      hpos.dim_hyperplane hpos.le_hyperplane (A ⊓ BinaryLinear.radical H)
      (inf_le_left.trans hAR) inf_le_right hC0

/-- The generated radical supplies the quadratic axis four-group in the
original representation, without requiring quadraticity of the radical. -/
theorem axisFour_of_rankFourPosition (d : DoubleNatural F 5 ρ)
    (hF : F.degree = 1) {B E : Subgroup G} {W H : Submodule (ZMod 2) (Space 5)}
    (hpos : RankFourPosition d hF B W H) (hB : IsQuadratic ρ B)
    (hER : E ≤ markedRadical d hF W) (hE : QuadraticSplitting.IsAxisFour d E) :
    HasQuadraticAxisFour d := by
  exact axisFour_of_normalizer_generation ρ d hB inf_le_left
    (normalizerGeneration_of_rankFourPosition d hF hpos) hER hE

end CFSG.Quasithin.ChapterB.NaturalExtensions.DoubleNatural.BinaryFive.SameAxis
