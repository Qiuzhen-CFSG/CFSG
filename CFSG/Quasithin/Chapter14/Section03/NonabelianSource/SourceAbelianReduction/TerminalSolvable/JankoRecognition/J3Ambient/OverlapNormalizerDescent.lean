module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.CubicOverlapSource

/-!
# Descent of the literal overlap normalizer through its cubic

The overlap is the actual embedded `C₃ × D₁₀`, and its characteristic
cubic confines its full ambient normalizer to the cubic normalizer.
Quotienting by exactly that cubic gives an actual `D₁₀` image. The full
ambient overlap normalizer is exactly the inverse image of this image's
normalizer in the recognized `PGL₂(9)` quotient.

The quotient map, its full cubic kernel, both actual images and their
inverse images are retained. No normalizer model or cubic splitting is
assumed. Identifying the remaining concrete `D₁₀` normalizer is the next
step toward Baumeister Lemma 2.5.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
open Janko23.J3Recognition.LocalSixteen Janko23.J3Recognition.Ambient
open Representation.CentralCubicNaturalFour
open Sporadic.Janko3.SourceRecognition
open Sporadic.Janko3.SourceRecognition.BaumeisterParabolics

private theorem dihedral_cube_trivial (x : DihedralGroup 5) (hx : x ^ 3 = 1) : x = 1 := by
  revert x
  decide +kernel

private theorem image_dihedral_of_cubic_kernel
    {N Q : Type*} [Group N] [Finite N] [Group Q]
    (q : N →* Q) (L : Subgroup N) (hker : q.ker ≤ L)
    (hkcard : Nat.card q.ker = 3)
    (eL : L ≃* (Multiplicative (ZMod 3) × DihedralGroup 5)) :
    Nonempty (L.map q ≃* DihedralGroup 5) ∧ Nat.card (L.map q) = 10 := by
  let f := q.subgroupMap L
  have hfk : Nat.card f.ker = 3 := by
    rw [Subgroup.ker_subgroupMap,
      Nat.card_congr (subgroupOfEquivOfLe hker).toEquiv]
    exact hkcard
  have hLc : Nat.card L = 30 := by
    rw [Nat.card_congr eL.toEquiv]
    norm_num [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      DihedralGroup.card]
  have hfi : f.ker.index = Nat.card (L.map q) := by
    rw [index_eq_card,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f
        (q.subgroupMap_surjective L)).toEquiv]
  have hcard : Nat.card (L.map q) = 10 := by
    have hh := f.ker.index_mul_card
    rw [hfi, hfk, hLc] at hh
    omega
  let : Finite (L.map q) := Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  let r : DihedralGroup 5 →* L.map q :=
    f.comp (eL.symm.toMonoidHom.comp (MonoidHom.inr (Multiplicative (ZMod 3)) (DihedralGroup 5)))
  have hr : Function.Injective r := by
    apply (injective_iff_map_eq_one r).mpr
    intro x hx
    let y : L := eL.symm (1, x)
    have hy : (y : N) ∈ q.ker := congrArg Subtype.val hx
    have hy3 : (y : N) ^ 3 = 1 := by
      have hh := pow_card_eq_one' (x := (⟨y, hy⟩ : q.ker))
      rw [hkcard] at hh
      exact congrArg Subtype.val hh
    have hyL : y ^ 3 = 1 := Subtype.ext hy3
    have hx3 : x ^ 3 = 1 := by
      have hh := congrArg eL hyL
      rw [map_pow, map_one, show eL y = (1, x) from eL.apply_symm_apply _] at hh
      exact congrArg Prod.snd hh
    exact dihedral_cube_trivial x hx3
  have hrc : Nat.card (DihedralGroup 5) = Nat.card (L.map q) := by
    rw [hcard]
    exact DihedralGroup.nat_card
  exact ⟨⟨(MulEquiv.ofBijective r
    ((Nat.bijective_iff_injective_and_card r).mpr ⟨hr, hrc⟩)).symm⟩, hcard⟩

variable {G : Type*} [Group G] [Finite G]

set_option maxHeartbeats 1000000 in
/-- The full original overlap normalizer is the exact inverse image of the
normalizer of its actual dihedral image in the literal projective quotient.
The cubic kernel and the ambient embeddings are part of the conclusion. -/
theorem literal_overlap_normalizer_descent
    {D : Seed G} (P : ReturningPair D) (hc : Janko23.OneInvolutionClass G)
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G)))
    (a : A ≃* Plane) (j : SingerField.Model →* G)
    (hj : PlaneTransport.FieldEmbedding A C a j) :
    ∃ e : (normalizer (zpowers (j cubic) : Set G) ⧸ cubicNormalizerKernel (j cubic)) ≃*
        GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F,
      let N := normalizer (zpowers (j cubic) : Set G)
      let q := e.toMonoidHom.comp (QuotientGroup.mk' (cubicNormalizerKernel (j cubic)))
      let L := (overlap j).subgroupOf N
      let K := (normalizer (overlap j : Set G)).subgroupOf N
      Function.Surjective q ∧ q.ker = cubicNormalizerKernel (j cubic) ∧
      Nat.card q.ker = 3 ∧ q.ker ≤ L ∧
      Nonempty (L.map q ≃* DihedralGroup 5) ∧ Nat.card (L.map q) = 10 ∧
      (L.map q).comap q = L ∧
      K = (normalizer (L.map q : Set (GorensteinWalter.PGL2
        Atlas.Comparisons.Exceptional.Nine.F))).comap q ∧
      K.map q = normalizer (L.map q : Set (GorensteinWalter.PGL2
        Atlas.Comparisons.Exceptional.Nine.F)) ∧
      ((normalizer (L.map q : Set (GorensteinWalter.PGL2
        Atlas.Comparisons.Exceptional.Nine.F))).comap q).map N.subtype =
        normalizer (overlap j : Set G) ∧
      Nat.card (normalizer (overlap j : Set G)) =
        3 * Nat.card (normalizer (L.map q : Set (GorensteinWalter.PGL2
          Atlas.Comparisons.Exceptional.Nine.F))) := by
  obtain ⟨_, ⟨e⟩⟩ := literal_field_cubic_projective P hc A C a j hj
  refine ⟨e, ?_⟩
  let N := normalizer (zpowers (j cubic) : Set G)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (cubicNormalizerKernel (j cubic)))
  let L := (overlap j).subgroupOf N
  let K := (normalizer (overlap j : Set G)).subgroupOf N
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = cubicNormalizerKernel (j cubic) := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hkc : Nat.card q.ker = 3 := by
    rw [hk]
    exact cubicNormalizerKernel_card (j cubic)
      ((orderOf_injective j hj.1 _).trans cubic_order)
  have hON : normalizer (overlap j : Set G) ≤ N := overlap_normalizer_le_cubic j hj.1
  have hLN : overlap j ≤ N := (overlap j).le_normalizer.trans hON
  have hkL : q.ker ≤ L := by
    rw [hk]
    exact subgroupOf_mono N (zpowers_le.mpr (mem_map_of_mem j cubic_mem))
  let eL : L ≃* (Multiplicative (ZMod 3) × DihedralGroup 5) :=
    (subgroupOfEquivOfLe hLN).trans (overlapEquiv j hj.1)
  obtain ⟨heL, hLc⟩ := image_dihedral_of_cubic_kernel q L hkL hkc eL
  have hpre : (L.map q).comap q = L := comap_map_eq_self hkL
  have hK : K = (normalizer (L.map q : Set _)).comap q := by
    rw [comap_normalizer_eq_of_surjective _ hq, hpre]
    exact subgroupOf_normalizer_eq hLN
  have hmap : K.map q = normalizer (L.map q : Set _) := by
    rw [hK, map_comap_eq_self_of_surjective hq]
  have hambient : ((normalizer (L.map q : Set _)).comap q).map N.subtype =
      normalizer (overlap j : Set G) := by
    rw [← hK]
    exact map_subgroupOf_eq_of_le hON
  have hkerK : q.ker ≤ K := by
    change q.ker ≤ (normalizer (overlap j : Set G)).subgroupOf N
    rw [subgroupOf_normalizer_eq hLN]
    exact hkL.trans L.le_normalizer
  have hcount : Nat.card (normalizer (overlap j : Set G)) =
      3 * Nat.card (normalizer (L.map q : Set (GorensteinWalter.PGL2
        Atlas.Comparisons.Exceptional.Nine.F))) := by
    let f := q.subgroupMap K
    have hfkc : Nat.card f.ker = 3 := by
      rw [Subgroup.ker_subgroupMap,
        Nat.card_congr (subgroupOfEquivOfLe hkerK).toEquiv]
      exact hkc
    have hfi : f.ker.index = Nat.card (normalizer (L.map q : Set (GorensteinWalter.PGL2
        Atlas.Comparisons.Exceptional.Nine.F))) := by
      rw [index_eq_card,
        Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f
          (q.subgroupMap_surjective K)).toEquiv, hmap]
    have hh := f.ker.index_mul_card
    rw [hfi, hfkc, Nat.card_congr (subgroupOfEquivOfLe hON).toEquiv] at hh
    omega
  exact ⟨hq, hk, hkc, hkL, heL, hLc, hpre, hK, hmap, hambient, hcount⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient

open Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Janko23.J3Recognition.LocalSixteen Janko23.J3Recognition.Ambient
open Representation.CentralCubicNaturalFour
open Sporadic.Janko3.SourceRecognition
open Sporadic.Janko3.SourceRecognition.BaumeisterParabolics

variable {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
    (hnot : ¬ ClassificationModels.IsTheoremEModel G) (g : G)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    {K : Subgroup G} (hK : ComponentLift F g K)
include hG hempty hM hu hmany hcard e hne hnot hgP hgH hyp hK

set_option maxHeartbeats 1000000 in
/-- Both original terminal planes supply the exact overlap-normalizer descent
through the full literal cubic kernel. All local field markings are retained. -/
theorem source_single_a5_j3_pair_normalizer_descent_of_four
    (e5 : F.terminalDot K ≃* alternatingGroup (Fin 5))
    (hspan : K = conjugateSpanBy K (T : Subgroup G))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4) :
    Janko23.OneInvolutionClass G ∧
    ∃ (D : Seed G) (P : ReturningPair D)
      (eR : P.R ≃* Matrix.PSL3Four.RootNormalizerModel.Root),
      F.H = K ∧ F.H = Janko23.involutionCentralizer D.z ∧
      Janko23.ambientCore D.z = F.U ∧
      P.A₁ eR ≠ P.A₂ eR ∧ P.A₁ eR ⊔ P.A₂ eR = P.R ∧ P.A₁ eR ⊓ P.A₂ eR = P.E ∧
      ∀ A : Subgroup G, A = P.A₁ eR ∨ A = P.A₂ eR →
        IsElementaryAbelian 2 A ∧ Nat.card A = 16 ∧
        ∃ (C : Subgroup (normalizer (A : Set G))) (f : C ≃* LinearGroup) (a : A ≃* Plane),
          (A.subgroupOf (normalizer (A : Set G))).IsComplement' C ∧
          (∀ (c : C) (x : A),
            a (A.normalizerMonoidHom c x) = naturalAction (f c) (a x)) ∧
          ∃ j : SingerField.Model →* G,
            PlaneTransport.FieldEmbedding A C a j ∧
            ∃ eQ : (normalizer (zpowers (j cubic) : Set G) ⧸ cubicNormalizerKernel (j cubic)) ≃*
                GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F,
              let N := normalizer (zpowers (j cubic) : Set G)
              let q := eQ.toMonoidHom.comp
                (QuotientGroup.mk' (cubicNormalizerKernel (j cubic)))
              let L := (overlap j).subgroupOf N
              Function.Surjective q ∧ q.ker = cubicNormalizerKernel (j cubic) ∧
              Nat.card q.ker = 3 ∧ q.ker ≤ L ∧
              Nonempty (L.map q ≃* DihedralGroup 5) ∧ Nat.card (L.map q) = 10 ∧
              (L.map q).comap q = L ∧
              ((normalizer (L.map q : Set (GorensteinWalter.PGL2
                Atlas.Comparisons.Exceptional.Nine.F))).comap q).map N.subtype =
                  normalizer (overlap j : Set G) ∧
              Nat.card (normalizer (overlap j : Set G)) =
                3 * Nat.card (normalizer (L.map q : Set (GorensteinWalter.PGL2
                  Atlas.Comparisons.Exceptional.Nine.F))) := by
  obtain ⟨hc, D, P, eR, hHK, hHz, hcore, hneP, hsup, hinf, hfields⟩ :=
    source_single_a5_j3_field_subgroups_of_four
      hG T hempty hM hu hmany hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  refine ⟨hc, D, P, eR, hHK, hHz, hcore, hneP, hsup, hinf, ?_⟩
  intro A hA
  obtain ⟨hAE, hAc, C, f, a, hC, ha, j, hj⟩ := hfields A hA
  obtain ⟨eQ, hq, hk, hkc, hkL, hD, hDc, hpre, _hK, _hmap, hambient, hcount⟩ :=
    J3Ambient.literal_overlap_normalizer_descent P hc A C a j hj
  exact ⟨hAE, hAc, C, f, a, hC, ha, j, hj,
    eQ, hq, hk, hkc, hkL, hD, hDc, hpre, hambient, hcount⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
