module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.CoverModels
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveOddModels
public import Theory.Representation.SU3.BinaryDegree.ProjectiveOrder
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Theory.GroupTheory.PerfectSmallTwoAction
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualCartanNormalizationLinear
public import Theory.GroupTheory.PCoreFrattiniTransport

/-!
# The actual smaller subgroup in the PSU₃(5) Cartan container

The local A₅ section in PSU₃(5) is the double cover SL₂(5). The ambient
order bounds its normal two-core by four, so perfectness makes that core
central. The perfect central-cover classification gives A₅ or SL₂(5);
the full Sylow normalization excludes the first alternative.

The source consumer uses the original line normalizer modulo its two-core,
and retains the literal image of the original residual inside the image
of its containing component. This proves the smaller-group marking needed
for Cartan normalization; it does not assert that the Cartan preserves it.

Source: Aschbacher--Smith A.3.14 and A.3.21(a), pp.49--50,55, applied in
Proposition 9.3.1, printed p.732.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Matrix BenderSuzuki.MatrixGroups
open scoped MatrixGroups
open CFSG.Quasithin
open CFSG.Quasithin.ChapterA.Section03
namespace CFSG.Quasithin.Chapter10.SourceOldResidualCartanNormalizationUnitary
variable {G : Type*} [Group G] [Finite G]
omit [Finite G] in
private theorem unitary_card (hm : ClassicalGroup.IsPSU G 3 5) : Nat.card G = 126000 := by
  obtain ⟨F,_,_,J,hF,hc,⟨e⟩⟩ := hm
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hf : Nat.card {x : F // J.conj x = x} = 5 := by
    simpa only [pow_one] using FiniteField.card_fixed_of_quadratic_frobenius
      J.conj 5 1 (by decide) (by simpa only [pow_one] using hF)
      (by simpa only [pow_one] using hc)
  rw [Nat.card_congr e.toEquiv, Representation.SU3.BinaryDegree.card_projective J hF hf]
  norm_num

private theorem small_core (hm : ClassicalGroup.IsPSU G 3 5) (K : Subgroup G)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) : Nat.card (pCore 2 K) ≤ 4 := by
  have hquot : Nat.card (K ⧸ pCore 2 K) = 60 := by
    rw [Nat.card_congr eK.toEquiv,nat_card_alternatingGroup]
    norm_num
  have hmul := card_eq_card_quotient_mul_card_subgroup (pCore 2 K)
  rw [hquot] at hmul
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := K)).exists_card_eq
  have hd : 60 * 2^n ∣ 126000 := by
    rw [←hn,←hmul,←unitary_card hm]
    exact K.card_subgroup_dvd_card
  have hn3 : n < 3 := by
    by_contra h
    have hd8 : 2^3 ∣ 2^n := pow_dvd_pow 2 (by omega)
    have hbad : 480 ∣ 126000 := (Nat.mul_dvd_mul_left 60 hd8).trans hd
    norm_num at hbad
  rw [hn]
  exact Nat.pow_le_pow_right (by decide) (by omega : n ≤ 2)

private theorem section_quasisimple (hm : ClassicalGroup.IsPSU G 3 5)
    (K : Subgroup G) [Group.IsPerfect K]
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) : IsQuasisimple K := by
  have hc : pCore 2 K ≤ center K := by
    have hh := le_centralizer_of_isPerfect_of_card_le_four (⊤ : Subgroup K) (pCore 2 K)
      (small_core hm K eK)
    intro x hx
    exact mem_center_iff.mpr fun y => (hh (mem_top y) x hx).symm
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv eK.symm
  exact (show PerfectCentralCovering.Cover K (K ⧸ pCore 2 K) from
    { toMonoidHom := QuotientGroup.mk' (pCore 2 K)
      surjective := QuotientGroup.mk'_surjective _
      isPerfect := inferInstance
      ker_le_center := by simpa only [QuotientGroup.ker_mk'] using hc }).isQuasisimple

/-- A Sylow-normalized local A₅ section of PSU₃(5) is the actual SL₂(5) cover. -/
theorem local_section_isSL_two_five
    (hm : ClassicalGroup.IsPSU G 3 5) (S : Sylow 2 G) (K : Subgroup G)
    (hl : K ∈ localCComponents S) (hn : (S : Subgroup G) ≤ normalizer (K : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) :
    Chapter1.Section02.LocalModels.IsSL K 2 5 := by
  let : Group.IsPerfect K := by
    let := hl.perfect
    exact Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe (show K ≤ K ⊔ (S : Subgroup G) from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe le_sup_left).surjective
  let : IsQuasisimple K := section_quasisimple hm K eK
  have hc : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by decide)]
    norm_num
  obtain ⟨e4⟩ := ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hc
  have hb : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2^2) :=
    ⟨GaloisField 2 2,inferInstance,inferInstance,hc,⟨eK.trans e4.symm⟩⟩
  rcases ChapterC.Section05.NormalizerControl.EmbeddingSelection.quasisimple_binary_core_models
    (by decide : 1 < 2) hb with hsimple | ⟨_,hcover⟩
  · obtain ⟨E,_,_,hE,⟨eE⟩⟩ := hsimple
    obtain ⟨e5⟩ := ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
      (show Nat.card E = 4 from hE)
    exact (ChapterA.Section03.SourceEmbeddings.AlternatingFive.not_odd_unitary
      S hl hn (eE.trans e5) (by decide) (by decide) hm).elim
  · exact hcover

/-- The literal local image in a PSU₃(5) containing component is SL₂(5). -/
theorem local_image_isSL_two_five
    (P : Sylow 2 G) (K J : Subgroup G)
    (hJ : J.IsCComponent) (hl : K ∈ localCComponents P)
    (hKJ : K ≤ J) (hn : (P : Subgroup G) ≤ normalizer (K : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (hm : ClassicalGroup.IsPSU (J ⧸ pCore 2 J) 3 5) :
    let q := QuotientGroup.mk' (pCore 2 G)
    Chapter1.Section02.LocalModels.IsSL ((K.map q).subgroupOf (J.map q)) 2 5 := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let : Group.IsNilpotent (pCore 2 G) := pCore_isNilpotent
  let : Group.IsSolvable q.ker := by
    rw [QuotientGroup.ker_mk']
    infer_instance
  let S := P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 G))
  let I := J.map q
  let B := K.map q
  have hBI : B ≤ I := map_mono hKJ
  have hlocal : B ∈ localCComponents S :=
    Chapter1.Section02.localCComponents_map_of_solvable_ker hl q
  have hnorm : (S : Subgroup (G ⧸ pCore 2 G)) ≤ normalizer (B : Set _) :=
    (map_mono hn).trans (le_normalizer_map q)
  obtain ⟨R,_,hBR,hRB⟩ := SourceEmbeddings.exists_local_sylow_normalizing S hlocal
    (hJ.map_quotient (pCore 2 G)).subnormal hBI hnorm
  have hmI : ClassicalGroup.IsPSU I 3 5 :=
    hm.of_mulEquiv (cComponentTwoCoreQuotientEquiv hJ).symm
  let k := q.subgroupMap K
  have hk2 : IsPGroup 2 k.ker :=
    ((pCore_isPGroup (p := 2) (G := G)).comap_subtype (K := K)).to_le (by
      intro x hx
      exact (QuotientGroup.eq_one_iff x.val).mp (congrArg Subtype.val hx))
  let eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5) :=
    (k.pCoreQuotientEquiv (q.subgroupMap_surjective K) hk2).symm.trans eK
  let i : B.subgroupOf I ≃* B := subgroupOfEquivOfLe hBI
  let eBI : (B.subgroupOf I ⧸ pCore 2 (B.subgroupOf I)) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ i (pCore_map_iso 2 i)).trans eB
  exact local_section_isSL_two_five hmI R (B.subgroupOf I) hBR hRB eBI

end CFSG.Quasithin.Chapter10.SourceOldResidualCartanNormalizationUnitary

namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterA.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- In the original PSU₃(5) Cartan container, the literal old residual image
is SL₂(5), with its central involution retained. -/
theorem old_residual_image_isSL_two_five_of_unitary_container
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (J : Subgroup G)
    (hJU : J ≤ normalizer (m.tensorLine : Set G))
    (hJ : (J.subgroupOf (normalizer (m.tensorLine : Set G))).IsCComponent)
    (hKJ : (pResidual 2 H).map H.subtype ≤ J)
    (hm : ClassicalGroup.IsPSU (J ⧸ pCore 2 J) 3 5) :
    let N := normalizer (m.tensorLine : Set G)
    let q := QuotientGroup.mk' (pCore 2 N)
    let K := ((pResidual 2 H).map H.subtype).subgroupOf N
    Chapter1.Section02.LocalModels.IsSL ((K.map q).subgroupOf ((J.subgroupOf N).map q)) 2 5 := by
  let N := normalizer (m.tensorLine : Set G)
  let K0 := (pResidual 2 H).map H.subtype
  have hKN : K0 ≤ N := hKJ.trans hJU
  let P := T.subtype m.tensorLine_normalized
  let K := K0.subgroupOf N
  let JN := J.subgroupOf N
  have hlocal : K ∈ localCComponents P := SourceEmbeddings.local_restrict
    (source_hstar_residual_mem_local_of_a5 hH eK).1 hKN
  have hPK : (P : Subgroup N) ≤ normalizer (K : Set N) := by
    rw [←subgroupOf_normalizer_eq hKN]
    exact comap_mono (hH.1.1.2.trans (le_normalizer_embedded_pResidual 2 H))
  let k : K ≃* K0 := subgroupOfEquivOfLe hKN
  let eKN : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ k (pCore_map_iso 2 k)).trans eK
  let j : JN ≃* J := subgroupOfEquivOfLe hJU
  have hmJN : ClassicalGroup.IsPSU (JN ⧸ pCore 2 JN) 3 5 :=
    hm.of_mulEquiv (QuotientGroup.congr _ _ j (pCore_map_iso 2 j))
  exact SourceOldResidualCartanNormalizationUnitary.local_image_isSL_two_five
    P K JN hJ hlocal (comap_mono hKJ) hPK eKN hmJN

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
