module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.CubicNonfusion
public import Theory.SpecificGroups.AlternatingSix.IndexTwoCubicNonfusionSplit

/-!
# Splitting the original cubic normalizer over its full cubic kernel

The actual plane coordinates supply a cubic nonfusion pair. Its transport
to the full cubic centralizer splits the central extension of A₆, and the
index-two Gaschütz bridge splits the same full kernel in the literal ambient
normalizer. The complement is therefore isomorphic to the already identified
PGL₂(9) quotient. No cubic splitting or local model is an input.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
open Janko23.J3Recognition.LocalSixteen Janko23.J3Recognition.Ambient
open Representation.CentralCubicNaturalFour
open Sporadic.Janko3.SourceRecognition
open Sporadic.Janko3.SourceRecognition.BaumeisterParabolics

/-- An actual complement to the full cubic kernel in the literal source normalizer. -/
theorem literal_cubic_normalizer_splits
    {G : Type*} [Group G] [Finite G] {D : Seed G}
    (P : ReturningPair D) (hc : Janko23.OneInvolutionClass G)
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G)))
    (l : C ≃* LinearGroup) (a : A ≃* Plane)
    (ha : ∀ (c : C) (x : A), a (A.normalizerMonoidHom c x) = naturalAction (l c) (a x))
    (j : SingerField.Model →* G) (hj : PlaneTransport.FieldEmbedding A C a j) :
    ∃ K : Subgroup (normalizer (zpowers (j cubic) : Set G)),
      (cubicNormalizerKernel (j cubic)).IsComplement' K ∧
      Nonempty (K ≃* GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F) := by
  let s := j cubic
  let N := normalizer (zpowers s : Set G)
  let Z := centralizer ({s} : Set G)
  let V := cubicNormalizerKernel s
  let H := Z.subgroupOf N
  have hs : orderOf s = 3 := (orderOf_injective j hj.1 _).trans cubic_order
  have hZN : Z ≤ N := cubic_centralizer_le_normalizer s
  let eH : H ≃* Z := subgroupOfEquivOfLe hZN
  have hVH : V ≤ H := by
    intro x hx
    exact cubic_le_centralizer s hx
  have hker : (V.subgroupOf H).map eH.toMonoidHom = cubicKernel s := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact hy
    · intro hx
      refine ⟨eH.symm x,?_,eH.apply_symm_apply x⟩
      exact hx
  obtain ⟨⟨eA⟩,⟨eN⟩⟩ := literal_field_cubic_projective P hc A C a j hj
  let e : (H ⧸ V.subgroupOf H) ≃* alternatingGroup (Fin 6) :=
    (QuotientGroup.congr _ _ eH hker).trans eA
  have hcenter : V.subgroupOf H ≤ center H := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    apply eH.injective
    rw [map_mul,map_mul]
    exact mem_center_iff.mp (cubicKernel_central s (show eH x ∈ cubicKernel s from hx)) (eH y)
  have hst : Commute s (j SingerField.fieldElement) := by
    exact (cubic_commutes_complement ⟨SingerField.fieldElement,(mem_pointComplement _).mpr rfl⟩).map j
  have hindex : H.index = 2 := cubic_normalizer_index D.localType hc s
    (j SingerField.fieldElement) hs (image_involution_order j hj.1) hst
  obtain ⟨σ,hσ,_hder,hσs,hσout,hnf⟩ := literal_cubic_nonfusion P hc A C l a ha j hj
  let σG : G := ((σ : normalizer (A : Set G)) : G)
  have hσZ : σG ∈ Z := mem_centralizer_singleton_iff.mpr hσs.eq.symm
  let x : H := eH.symm ⟨σG,hσZ⟩
  let z : H := eH.symm ⟨s,cubic_le_centralizer s (mem_zpowers s)⟩
  have hx : orderOf x = 3 :=
    (eH.symm.orderOf_eq _).trans ((orderOf_coe _).symm.trans
      ((orderOf_coe (σ : normalizer (A : Set G))).trans ((orderOf_coe σ).trans hσ)))
  have hxn : x ∉ V.subgroupOf H := hσout
  have hz : z ∈ V.subgroupOf H := mem_zpowers s
  have hnon : ¬ IsConj x (z*x) := by
    intro hh
    have hm := Z.subtype.map_isConj (eH.toMonoidHom.map_isConj hh)
    apply hnf
    change IsConj ((eH x : Z) : G) (((eH z : Z) : G) * ((eH x : Z) : G)) at hm
    simpa only [x,z,eH.apply_symm_apply] using hm
  obtain ⟨K,hK⟩ := AlternatingSix.CentralThreeNonfusionSplit.exists_complement_of_index_two_nonfusion
    V H (cubicNormalizerKernel_card s hs) hVH hindex hcenter e x z hx hxn hz hnon
  exact ⟨K,hK,⟨hK.symm.QuotientMulEquiv.symm.trans eN⟩⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient

open Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Janko23.J3Recognition.LocalSixteen
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

/-- Both original terminal planes have split full cubic normalizers, with the
same full kernels, normalizer complements, natural actions and field embeddings. -/
theorem source_single_a5_j3_cubic_normalizer_splits_of_four
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
        ∃ (C : Subgroup (normalizer (A : Set G))) (l : C ≃* LinearGroup) (a : A ≃* Plane),
          (A.subgroupOf (normalizer (A : Set G))).IsComplement' C ∧
          (∀ (c : C) (x : A),
            a (A.normalizerMonoidHom c x) = naturalAction (l c) (a x)) ∧
          ∃ j : SingerField.Model →* G,
            PlaneTransport.FieldEmbedding A C a j ∧
            ∃ K : Subgroup (normalizer (zpowers (j cubic) : Set G)),
              (Janko23.J3Recognition.Ambient.cubicNormalizerKernel (j cubic)).IsComplement' K ∧
              Nonempty (K ≃* GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F) := by
  obtain ⟨hc,D,P,eR,hHK,hHz,hcore,hneP,hsup,hinf,hfields⟩ :=
    source_single_a5_j3_field_subgroups_of_four
      hG T hempty hM hu hmany hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  refine ⟨hc,D,P,eR,hHK,hHz,hcore,hneP,hsup,hinf,?_⟩
  intro A hA
  obtain ⟨hAE,hAc,C,l,a,hC,ha,j,hj⟩ := hfields A hA
  exact ⟨hAE,hAc,C,l,a,hC,ha,j,hj,
    J3Ambient.literal_cubic_normalizer_splits P hc A C l a ha j hj⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
