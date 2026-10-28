module
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalFFRows
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalOffenderMovement
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.DoubledSylowTransport
public import CFSG.Quasithin.ChapterB.Section02.UniqueOffender
public import CFSG.Quasithin.ChapterB.Section02.BaumannNormalizerImage.Shear
/-!
# The doubled linear-three terminal branch

In the centralizer quotient attached to the actual reduced source module, two
copies of the natural binary three-space identify the unique Sylow offender
with a conjugate shear subgroup. The pointwise-fixer calculation and B.2.20
then identify both the Thompson image and the original Baumann image with
that subgroup.

The restricted Baumann normalizer has image of order 24. Its two-residual
lifts through the original subgroup `K ⊔ R₁` to a two-perfect subgroup of `K`
normalizing the original Baumann subgroup, with order divisible by three.
This supplies the terminal subgroup used by the ambient theta contradiction.

Source: Aschbacher--Smith, proof of Lemma 13.7.4(1), printed p.938.
-/

@[expose] public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open BinaryLinearThree
noncomputable section


namespace CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
variable {F D : Type*} [Group F] [Finite F] [Group D] [Finite D]
open CFSG.Quasithin.ChapterB

omit [Finite F] [Finite D] in
private theorem fixedCentralizer_image_of_fixer
    (U R : Subgroup F) [U.Normal] [IsElementaryAbelian 2 U]
    (q : F →* D) (hq : Function.Surjective q) (hk : q.ker = centralizer (U : Set F))
    (B : Subgroup D) (hBR : B ≤ R.map q)
    (hf : ∀ x ∈ R.map q,
      (∀ v ∈ fixedSpace (NormalElementaryQuotient.representation U q hq hk) B,
        NormalElementaryQuotient.representation U q hq hk x v = v) → x ∈ B) :
    (R ⊓ centralizer (U ⊓ centralizer (B.comap q : Set F) : Set F)).map q = B := by
  let ρ := NormalElementaryQuotient.representation U q hq hk
  have hv (v : Additive U) : v ∈ fixedSpace ρ B ↔
      (v.toMul : F) ∈ centralizer (B.comap q : Set F) := by
    have h := NormalElementaryQuotient.mem_fixedSpace_image U q hq hk (B.comap q) v
    rw [map_comap_eq_self_of_surjective hq] at h
    exact h
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    apply hf _ (mem_map_of_mem q hx.1)
    intro v hvo
    have hc := hx.2 v.toMul ⟨v.toMul.property,(hv v).mp hvo⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [NormalElementaryQuotient.representation_apply,←hc,mul_inv_cancel_right]
  · intro z hz
    obtain ⟨x,hx,rfl⟩ := hBR hz
    refine ⟨x,⟨hx,?_⟩,rfl⟩
    intro v hv'
    exact (hv'.2 x hz).symm

/-- The original Baumann image is a component conjugate of the shear radical. -/
theorem doubled_baumann_image
    (U R : Subgroup F) [U.Normal] [IsElementaryAbelian 2 U]
    (q : F →* D) (hq : Function.Surjective q) (hk : q.ker = centralizer (U : Set F))
    (C E : Subgroup D) [C.Normal] (hCE : C ≤ E)
    (a : ActionEquiv ((NormalElementaryQuotient.representation U q hq hk).comp C.subtype)
      (repeated (linearNatural BinaryField.two 3) 2))
    (P : Sylow 2 E) (hP : (P : Subgroup E).map E.subtype = R.map q)
    (hUR : U ≤ R) (hJ : ¬ elementaryAbelianMaxJ R ≤ q.ker) :
    ∃ g : BinaryLinearThree.Group,
    let j : BinaryLinearThree.Group →* D := C.subtype.comp a.groupEquiv.symm.toMonoidHom
    (elementaryAbelianMaxJ R).map q = (BinaryLinearThree.R.map (MulAut.conj g).toMonoidHom).map j ∧
    (baumann R).map q = (BinaryLinearThree.R.map (MulAut.conj g).toMonoidHom).map j := by
  let ρ := NormalElementaryQuotient.representation U q hq hk
  obtain ⟨g,hBR,hBC,huniq,hfix⟩ := doubled_sylow_geometry ρ
    (NormalElementaryQuotient.representation_injective U q hq hk) C E hCE a P
  let j : BinaryLinearThree.Group →* D := C.subtype.comp a.groupEquiv.symm.toMonoidHom
  let B := (BinaryLinearThree.R.map (MulAut.conj g).toMonoidHom).map j
  rw [hP] at hBR huniq hfix
  refine ⟨g,?_⟩
  apply lemma_B_2_20 U R q hq hk B hUR hJ
  · intro A hAR hA
    exact huniq A hAR (hA.isOffender ρ)
  · exact fixedCentralizer_image_of_fixer U R q hq hk B hBR hfix
end CFSG.Quasithin.Chapter13.Section07.PlusAction.Original

namespace CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
open Theory.GroupTheory CFSG.Quasithin.ChapterB
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₃ H : Subgroup G}

/-- The doubled-natural row identifies the Thompson and Baumann images of the
literal point radical in the original centralizer quotient. -/
theorem source_reduced_doubled_baumann_image
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    {K : Subgroup G}
    (hKC : K ≤ kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
    (hKn : H ≤ normalizer (K : Set G))
    (hcomm : ⁅K,(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁⁆ ≤ K.pCoreIn 2)
    (U : Subgroup ↥(K ⊔ ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔ (T : Subgroup G))))
    (hred : IsPReduced 2 U)
    (hU0 : U ≤ (fixedLayer (ConjugateIntersections.sourceSetup T L V V₃ V₁ H)).subgroupOf
      (K ⊔ ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔ (T : Subgroup G))))
    (hJ : let X := K ⊔ ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔ (T : Subgroup G))
      letI := hred.normal
      letI := hred.elementary
      let q := QuotientGroup.mk' (centralizer (U : Set X))
      ¬ elementaryAbelianMaxJ
        ((((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔
          (T : Subgroup G)).pCoreIn 2).subgroupOf X) ≤ q.ker)
    (hdouble : let X := K ⊔ ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔ (T : Subgroup G))
      letI := hred.normal
      letI := hred.elementary
      let q := QuotientGroup.mk' (centralizer (U : Set X))
      let C := (K.subgroupOf X).map q
      let ρ := NormalElementaryQuotient.representation U q
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
      Nonempty (ActionEquiv (ρ.comp C.subtype)
        (repeated (linearNatural BinaryField.two 3) 2))) :
    let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    let P := F.L₁ ⊔ (T : Subgroup G)
    let X := K ⊔ P
    letI := hred.normal
    letI := hred.elementary
    let q := QuotientGroup.mk' (centralizer (U : Set X))
    let C := (K.subgroupOf X).map q
    ∃ e : C ≃* BinaryLinearThree.Group, ∃ g : BinaryLinearThree.Group,
      let j := C.subtype.comp e.symm.toMonoidHom
      (elementaryAbelianMaxJ ((P.pCoreIn 2).subgroupOf X)).map q =
        (BinaryLinearThree.R.map (MulAut.conj g).toMonoidHom).map j ∧
      (baumann ((P.pCoreIn 2).subgroupOf X)).map q =
        (BinaryLinearThree.R.map (MulAut.conj g).toMonoidHom).map j := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let P := F.L₁ ⊔ (T : Subgroup G)
  let R := P.pCoreIn 2
  let X := K ⊔ P
  let Y := K ⊔ R
  have hRX : R ≤ X := (pCoreIn_le 2 P).trans le_sup_right
  have hYX : Y ≤ X := sup_le le_sup_left hRX
  let RX := R.subgroupOf X
  let YX := Y.subgroupOf X
  let := hred.normal
  let := hred.elementary
  let q := QuotientGroup.mk' (centralizer (U : Set X))
  let C := (K.subgroupOf X).map q
  let E := C ⊔ RX.map q
  have hdata := source_kernel_reduced_actor_image h
    (hKC.trans (kernel_le_H (D := F))) hKn U hred
  let : C.Normal := hdata.2.1
  have hE : YX.map q = E := by
    change ((K ⊔ R).subgroupOf X).map q = (K.subgroupOf X).map q ⊔ (R.subgroupOf X).map q
    rw [subgroupOf_sup (show K ≤ X from le_sup_left) hRX,Subgroup.map_sup]
  have hSyl : Chapter1.IsSylowIn 2 RX YX := by
    apply (Chapter1.IsSylowIn.map_iff X.subtype X.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le hRX,map_subgroupOf_eq_of_le hYX]
    exact source_normal_kernel_sylow_of_commutator h hKC hKn hcomm
  obtain ⟨S,hS⟩ := hSyl
  let Q := S.mapSurjective (f := q.subgroupMap YX) (q.subgroupMap_surjective YX)
  have hQ : (Q : Subgroup (YX.map q)).map (YX.map q).subtype = RX.map q := by
    rw [Sylow.coe_mapSurjective,map_map]
    change (S : Subgroup YX).map (q.comp YX.subtype) = RX.map q
    rw [←map_map,hS]
  let eE : YX.map q ≃* E := MulEquiv.subgroupCongr hE
  let QE := Q.mapSurjective (f := eE.toMonoidHom) eE.surjective
  have hQE : (QE : Subgroup E).map E.subtype = RX.map q := by
    change ((Q : Subgroup (YX.map q)).map eE.toMonoidHom).map E.subtype = RX.map q
    rw [map_map]
    exact hQ
  obtain ⟨a⟩ := hdouble
  have hUR : U ≤ RX := by
    intro u hu
    exact source_fixedLayer_le_point_radical h (hU0 hu)
  obtain ⟨g,hg⟩ := doubled_baumann_image U RX q (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _) C E le_sup_left a QE hQE hUR hJ
  exact ⟨a.groupEquiv,g,hg⟩
end CFSG.Quasithin.Chapter13.Section07.PlusAction.Original

namespace CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
open Theory.GroupTheory CFSG.Quasithin.ChapterB
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₃ H : Subgroup G}

/-- A doubled natural source row supplies the actual two-perfect cubic
subgroup in K and in the original Baumann normalizer. -/
theorem source_reduced_doubled_baumann_terminal
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    {K : Subgroup G}
    (hKC : K ≤ kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
    (hKn : H ≤ normalizer (K : Set G))
    (hcomm : ⁅K,(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁⁆ ≤ K.pCoreIn 2)
    (U : Subgroup ↥(K ⊔ ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔ (T : Subgroup G))))
    (hred : IsPReduced 2 U)
    (hU0 : U ≤ (fixedLayer (ConjugateIntersections.sourceSetup T L V V₃ V₁ H)).subgroupOf
      (K ⊔ ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔ (T : Subgroup G))))
    (hJ : let X := K ⊔ ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔ (T : Subgroup G))
      letI := hred.normal
      letI := hred.elementary
      let q := QuotientGroup.mk' (centralizer (U : Set X))
      ¬ elementaryAbelianMaxJ
        ((((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔
          (T : Subgroup G)).pCoreIn 2).subgroupOf X) ≤ q.ker)
    (hdouble : let X := K ⊔ ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔ (T : Subgroup G))
      letI := hred.normal
      letI := hred.elementary
      let q := QuotientGroup.mk' (centralizer (U : Set X))
      let C := (K.subgroupOf X).map q
      let ρ := NormalElementaryQuotient.representation U q
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
      Nonempty (ActionEquiv (ρ.comp C.subtype)
        (repeated (linearNatural BinaryField.two 3) 2))) :

    ∃ K₀ : Subgroup G, K₀ ≤ K ∧
      K₀ ≤ normalizer (baumann
        (((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔
          (T : Subgroup G)).pCoreIn 2) : Set G) ∧
      IsPPerfect 2 K₀ ∧ 3 ∣ Nat.card K₀ := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let P := F.L₁ ⊔ (T : Subgroup G)
  let R := P.pCoreIn 2
  let X := K ⊔ P
  let Y := K ⊔ R
  have hRX : R ≤ X := (pCoreIn_le 2 P).trans le_sup_right
  have hYX : Y ≤ X := sup_le le_sup_left hRX
  let RX := R.subgroupOf X
  let := hred.normal
  let := hred.elementary
  let q := QuotientGroup.mk' (centralizer (U : Set X))
  let C := (K.subgroupOf X).map q
  let f := q.comp (inclusion hYX)
  let N := K.subgroupOf Y
  have hYn : Y ≤ normalizer (K : Set G) :=
    (sup_le (hKC.trans (kernel_le_H (D := F)))
      ((pCoreIn_le 2 P).trans h.local_le)).trans hKn
  let : N.Normal := normal_subgroupOf_of_le_normalizer hYn
  obtain ⟨S,hS⟩ := source_normal_kernel_sylow_of_commutator h hKC hKn hcomm
  have hNP : N ⊔ (S : Subgroup Y) = ⊤ := by
    apply map_injective Y.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show K ≤ Y from le_sup_left),hS,
      ←MonoidHom.range_eq_map,Y.range_subtype]
  have hC : N.map f = C := by
    ext z
    constructor
    · rintro ⟨k,hk,rfl⟩
      exact ⟨inclusion hYX k,hk,rfl⟩
    · rintro ⟨k,hk,rfl⟩
      exact ⟨⟨k,mem_sup_left hk⟩,hk,rfl⟩
  have hSX : (S : Subgroup Y).map (inclusion hYX) = RX := by
    apply map_injective X.subtype_injective
    rw [map_map,map_subgroupOf_eq_of_le hRX]
    exact hS
  have hBR : (baumann (S : Subgroup Y)).map f = (baumann RX).map q := by
    rw [←map_map]
    simp only [baumann,thompsonAlpha]
    rw [baumann_map_injective (inclusion hYX) (inclusion_injective hYX),hSX]
  obtain ⟨e,g,_,hb⟩ := source_reduced_doubled_baumann_image h hKC hKn hcomm U hred hU0 hJ hdouble
  let A := BinaryLinearThree.R.map (MulAut.conj g).toMonoidHom
  let j := C.subtype.comp e.symm.toMonoidHom
  have hBA : (baumann (S : Subgroup Y)).map f = A.map j := hBR.trans hb
  have hBC : A.map j ≤ C := by
    rintro _ ⟨a,ha,rfl⟩
    exact (e.symm a).property
  have hlocal : (A.map j).subgroupOf C = A.map e.symm.toMonoidHom := by
    apply map_injective C.subtype_injective
    rw [map_subgroupOf_eq_of_le hBC]
    exact (map_map _ _ _).symm
  have hmark : ((A.map j).subgroupOf C).map e.toMonoidHom = A := by
    rw [hlocal,map_map]
    have hi : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id _ := by
      apply MonoidHom.ext
      intro a
      exact e.apply_symm_apply a
    rw [hi,Subgroup.map_id]
  let eN := (MulEquiv.subgroupCongr hC).trans e
  have hBN : (baumann (S : Subgroup Y)).map f ≤ N.map f := by
    rw [hBA,hC]
    exact hBC
  have hmarkN : (((baumann (S : Subgroup Y)).map f).subgroupOf (N.map f)).map
      eN.toMonoidHom = A := by
    rw [hBA]
    have ht : ((A.map j).subgroupOf (N.map f)).map
        (MulEquiv.subgroupCongr hC).toMonoidHom = (A.map j).subgroupOf C := by
      ext a
      constructor
      · rintro ⟨b,hb,rfl⟩
        exact hb
      · intro ha
        refine ⟨(MulEquiv.subgroupCongr hC).symm a,ha,?_⟩
        exact (MulEquiv.subgroupCongr hC).apply_symm_apply a
    change ((A.map j).subgroupOf (N.map f)).map
      (e.toMonoidHom.comp (MulEquiv.subgroupCongr hC).toMonoidHom) = A
    rw [←map_map,ht]
    exact hmark
  obtain ⟨J,hJle,hp,h3,_⟩ :=
    exists_twoPerfect_cubic_le_normal_baumann_normalizer_of_shear_image
      S N hNP f eN hBN g hmarkN
  let K₀ := J.map Y.subtype
  have hBaum : (baumann (S : Subgroup Y)).map Y.subtype = baumann R := by
    simp only [baumann,thompsonAlpha]
    rw [baumann_map_injective Y.subtype Y.subtype_injective,hS]
  refine ⟨K₀,?_,?_,hp.of_surjective (Y.subtype.subgroupMap J)
    (Y.subtype.subgroupMap_surjective J),?_⟩
  · exact (map_mono (hJle.trans inf_le_left)).trans
      (map_subgroupOf_eq_of_le (show K ≤ Y from le_sup_left)).le
  · have hm := (map_mono (hJle.trans inf_le_right)).trans
      ((baumann (S : Subgroup Y)).le_normalizer_map Y.subtype)
    rw [hBaum] at hm
    exact hm
  · rwa [card_map_of_injective Y.subtype_injective]
end CFSG.Quasithin.Chapter13.Section07.PlusAction.Original

namespace CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₃ H M : Subgroup G}
open CFSG.Quasithin.ChapterB
open Theory.GroupTheory
set_option backward.isDefEq.respectTransparency false
/-- On the actual escape branch, the source Baumann bound discharges
Thompson noncentrality before selecting the terminal subgroup. -/
theorem source_reduced_kernel_doubled_baumann_terminal
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    {K : Subgroup G}
    (hKC : K ≤ kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
    (hKn : H ≤ normalizer (K : Set G))
    (hcomm : ⁅K,(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁⁆ ≤ K.pCoreIn 2)
    (U : Subgroup ↥(K ⊔ ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔ (T : Subgroup G))))
    (hred : IsPReduced 2 U)
    (hU0 : U ≤ (fixedLayer (ConjugateIntersections.sourceSetup T L V V₃ V₁ H)).subgroupOf
      (K ⊔ ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔ (T : Subgroup G))))
    (hout : ¬ K ≤ M)
    (hB : normalizer (baumann
      (((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔
        (T : Subgroup G)).pCoreIn 2) : Set G) ≤ M)
    (hkind : ((K.subgroupOf (K ⊔
      ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔ (T : Subgroup G)))).IsCComponent ∧
      IsQuasisimple (K ⧸ pCore 2 K)) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Multiplicative (ZMod 3)))
    (hne : U ≠ ⊥)
    (hmove : ⁅U,K.subgroupOf (K ⊔
      ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔ (T : Subgroup G)))⁆ = U)
    (hdouble : let X := K ⊔ ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔ (T : Subgroup G))
      letI := hred.normal
      letI := hred.elementary
      let q := QuotientGroup.mk' (centralizer (U : Set X))
      let C := (K.subgroupOf X).map q
      let ρ := NormalElementaryQuotient.representation U q
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
      Nonempty (ActionEquiv (V := Additive U) (ρ.comp C.subtype)
        (repeated (linearNatural BinaryField.two 3) 2))) :
    ∃ K₀ : Subgroup G, K₀ ≤ K ∧
      K₀ ≤ normalizer (baumann
        (((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔
          (T : Subgroup G)).pCoreIn 2) : Set G) ∧
      IsPPerfect 2 K₀ ∧ 3 ∣ Nat.card K₀ := by
  exact source_reduced_doubled_baumann_terminal h hKC hKn hcomm U hred hU0
    (source_reduced_kernel_thompson_not_le_kernel h hKC hKn hcomm hout hB hkind
      U hred hU0 hne hmove) hdouble
/-- The literal primitive-component application. The given doubled action
is the output of the original FF-row producer; all Baumann-image and
Thompson noncentrality premises are discharged here. -/
theorem source_component_doubled_baumann_terminal
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (J : Subgroup H) (hJ : J.IsCComponent) (hs : IsSimpleGroup (J ⧸ pCore 2 J))
    (hKC : (J.map H.subtype) ≤ kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
    (hKn : H ≤ normalizer ((J.map H.subtype) : Set G))
    (hcomm : ⁅(J.map H.subtype),(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁⁆ ≤ (J.map H.subtype).pCoreIn 2)
    (U : Subgroup ↥((J.map H.subtype) ⊔ ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔ (T : Subgroup G))))
    (hred : IsPReduced 2 U)
    (hU0 : U ≤ (fixedLayer (ConjugateIntersections.sourceSetup T L V V₃ V₁ H)).subgroupOf
      ((J.map H.subtype) ⊔ ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔ (T : Subgroup G))))
    (hout : ¬ J.map H.subtype ≤ M)
    (hB : normalizer (baumann
      (((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔
        (T : Subgroup G)).pCoreIn 2) : Set G) ≤ M)
    (hne : U ≠ ⊥)
    (hmove : ⁅U,(J.map H.subtype).subgroupOf (J.map H.subtype ⊔
      ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔ (T : Subgroup G)))⁆ = U)
    (hdouble : let X := (J.map H.subtype) ⊔ ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔ (T : Subgroup G))
      letI := hred.normal
      letI := hred.elementary
      let q := QuotientGroup.mk' (centralizer (U : Set X))
      let C := ((J.map H.subtype).subgroupOf X).map q
      let ρ := NormalElementaryQuotient.representation U q
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
      Nonempty (ActionEquiv (V := Additive U) (ρ.comp C.subtype)
        (repeated (linearNatural BinaryField.two 3) 2))) :
    ∃ K₀ : Subgroup G, K₀ ≤ J.map H.subtype ∧
      K₀ ≤ normalizer (baumann
        (((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔
          (T : Subgroup G)).pCoreIn 2) : Set G) ∧
      IsPPerfect 2 K₀ ∧ 3 ∣ Nat.card K₀ := by
  exact source_reduced_doubled_baumann_terminal h hKC hKn hcomm U hred hU0
    (source_component_kernel_thompson_not_le_kernel h J hJ hs hKC hKn hcomm
      hout hB U hred hU0 hne hmove) hdouble
end CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
