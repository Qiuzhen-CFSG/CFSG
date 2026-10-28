module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.NormalizerEight
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.BinaryActorFixedFive
public import Theory.GroupTheory.PrimeOrderLift

/-!
# The original canonical moved module in the contrary normalizer branch

Reuse the actual SL4(2) quotient and B.5.1 on the canonical module
E = R2(K_v S). The original nonzero A6-fixed vector v0 lies in V_v and
hence in [U,K_v]. An element of order five in L_v fixes v0 and retains
its order through the literal two-core action kernel. This excludes the
natural, repeated-natural and natural-plus-dual rows. The actual moved
central quotient is the six-dimensional orthogonal module; its whole
moved space is the natural six-space or the seven-dimensional augmentation
core, with action equivalences on the original module.

The literal commutator comparison gives |[U,K_v]| = 64 or 128, so
V_v < [U,K_v]. The preferred-point application retains V and C_V(L),
and discharges nonquasisimplicity when that original fixed space is nontrivial.
NormalizerLine supplies movement of the original fixed line. The 12.6.16
conjugacy argument remains for normalizer escape with nontrivial fixed space. The HS/J4 exclusions, general canonical-module
arguments, blocks, splitting and fixed-space elimination remain as well;
neither 12.6.2 nor 12.6.23 is asserted. Earlier invariance/TI retain producer
qt-d-1222-source; final discharge remains with qt-d-12634-source.
Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
12.6.13--17, printed pp.826--827, and B.5.1, printed pp.99--103.
-/

public section
namespace CFSG.Quasithin.Chapter12.Section06
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open ChapterB.QuasisimpleSource
open scoped IsMulCommutative

/-- The orthogonal comparison on the original elementary conjugation quotient,
including the actual component image and its offender overgroup. -/
@[expose] def CanonicalOrthogonalMoved {A : Type*} [Group A]
    (E : Subgroup A) [E.Normal] [IsElementaryAbelian 2 E] (K : Subgroup A) : Prop :=
  let ρ := ChapterB.InternalThompsonAction.action E
  let q := ChapterB.InternalThompsonAction.actionMk E
  let B := K.map q
  let O := offenderSubgroup ρ
  B ≤ O ∧ SourceCompletion.BinaryActor.OrthogonalMovedModel (ρ.comp O.subtype) (B.subgroupOf O)
end CFSG.Quasithin.Chapter12.Section06
namespace CFSG.Quasithin.Chapter12.Section06
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open ChapterB.QuasisimpleSource
open scoped IsMulCommutative

private theorem canonical_moved_quintic_fixed
    {A : Type*} [Group A] (E : Subgroup A) [E.Normal] [IsElementaryAbelian 2 E]
    (K : Subgroup A) (O : Subgroup (ChapterB.InternalThompsonAction.ActionQuotient E))
    (hBO : K.map (ChapterB.InternalThompsonAction.actionMk E) ≤ O)
    (s : MovedSection ((ChapterB.InternalThompsonAction.action E).comp O.subtype)
      ((K.map (ChapterB.InternalThompsonAction.actionMk E)).subgroupOf O))
    (x : A) (hx : x ∈ K)
    (hx5 : orderOf (ChapterB.InternalThompsonAction.actionMk E x) = 5)
    (w : A) (hw : w ∈ ⁅E,K⁆) (hw1 : w ≠ 1) (hc : x*w=w*x) :
    ∃ y : (K.map (ChapterB.InternalThompsonAction.actionMk E)).subgroupOf O,
      orderOf y = 5 ∧ ∃ z : s.space.toSubmodule,
        z ≠ 0 ∧ s.space.toRepresentation y.val z = z := by
  let q := ChapterB.InternalThompsonAction.actionMk E
  let ρ := ChapterB.InternalThompsonAction.action E
  let B := K.map q
  let C := B.subgroupOf O
  let u : Additive E := Additive.ofMul ⟨w,commutator_le_left E K hw⟩
  have hu : u ∈ s.space.toSubmodule := by
    rw [s.space_eq]
    change u ∈ subspaceCommutator (ρ.comp O.subtype) ⊤ C
    rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hBO]
    change u ∈ subspaceCommutator (NormalElementaryQuotient.representation E q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) ⊤ (K.map q)
    rw [←NormalElementaryQuotient.commutatorSpace_eq E q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) K]
    exact hw
  let z : s.space.toSubmodule := ⟨u,hu⟩
  have hz : z ≠ 0 := by
    intro hz
    exact hw1 (congrArg (fun z : s.space.toSubmodule => z.val.toMul.val) hz)
  have hxB : q x ∈ B := mem_map_of_mem q hx
  let y : C := ⟨⟨q x,hBO hxB⟩,hxB⟩
  have hy : orderOf y = 5 := by
    rw [←Subgroup.orderOf_coe,←Subgroup.orderOf_coe]
    exact hx5
  refine ⟨y,hy,z,hz,?_⟩
  apply Subtype.ext
  apply Additive.toMul.injective
  apply Subtype.ext
  change ((ChapterB.InternalThompsonAction.action E (q x) u).toMul : A) = w
  rw [ChapterB.InternalThompsonAction.action_apply]
  exact mul_inv_eq_iff_eq_mul.mpr hc
end CFSG.Quasithin.Chapter12.Section06
namespace CFSG.Quasithin.Chapter12.Section06
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open ChapterB.QuasisimpleSource
open scoped MatrixGroups IsMulCommutative

private theorem canonical_orthogonal_of_quintic_fixed
    {A : Type*} [Group A] [Finite A]
    (E : Subgroup A) [E.Normal] [IsElementaryAbelian 2 E] (K : Subgroup A)
    (hBO : K.map (ChapterB.InternalThompsonAction.actionMk E) ≤
      offenderSubgroup (ChapterB.InternalThompsonAction.action E))
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      ((ChapterB.InternalThompsonAction.action E).comp
        (offenderSubgroup (ChapterB.InternalThompsonAction.action E)).subtype)
      ((K.map (ChapterB.InternalThompsonAction.actionMk E)).subgroupOf
        (offenderSubgroup (ChapterB.InternalThompsonAction.action E))))
    (e : (K.map (ChapterB.InternalThompsonAction.actionMk E)).subgroupOf
        (offenderSubgroup (ChapterB.InternalThompsonAction.action E)) ≃* SL(4,ZMod 2))
    (x : A) (hx : x ∈ K)
    (hx5 : orderOf (ChapterB.InternalThompsonAction.actionMk E x) = 5)
    (w : A) (hw : w ∈ ⁅E,K⁆) (hw1 : w ≠ 1) (hc : x*w=w*x) :
    CanonicalOrthogonalMoved E K := by
  let ρ := ChapterB.InternalThompsonAction.action E
  let O := offenderSubgroup ρ
  let s := c.sectionData
  have hcase := SourceCompletion.BinaryActor.actionCase (ρ.comp O.subtype) (Or.inl rfl) e c.clause_one
  obtain ⟨y,hy,z,hz,hfix⟩ := canonical_moved_quintic_fixed E K O hBO s x hx hx5 w hw hw1 hc
  exact ⟨hBO,s,SourceCompletion.BinaryActor.orthogonal_of_quintic_fixed s hcase y hy z hz hfix⟩
end CFSG.Quasithin.Chapter12.Section06
namespace CFSG.Quasithin.Chapter12.Section06
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open ChapterB.QuasisimpleSource
open scoped MatrixGroups IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

set_option backward.isDefEq.respectTransparency false in
/-- The whole moved-module comparison retains the canonical action kernel. -/
theorem SourceHypothesis.nonsingular_normalizer_moved_model_with_kernel
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hnot : ¬ IsQuasisimple (Kv (v : G)))
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (he : ¬ Kv (v : G) ≤ M L)
    (hNM : normalizer (Rv T L (v : G) : Set G) ≤ M L) :
    ∃ S : Sylow 2 (Gv (v : G)),
      let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
      let J := Kv (v : G) ⊔ S₀
      let E := reducedTwoSubgroup J
      letI : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
      Tv T (v : G) ≤ S₀ ∧
      (∃ P : Sylow 2 G, (P : Subgroup G) = S₀) ∧
      U (Kv (v : G)) S₀ = E.map J.subtype ∧
      centralizer (E : Set J) = pCore 2 J ∧
      Vv L V (v : G) ≤ ⁅U (Kv (v : G)) S₀,Kv (v : G)⁆ ∧
      CanonicalOrthogonalMoved E ((Kv (v : G)).subgroupOf J) := by
  obtain ⟨S,hTS,hN,hR,hF,hker,hred,hm,hUR,hff⟩ :=
    H.nonsingular_normalizer_canonical_ff D v hv hTV hnot hs hi he hNM
  let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  let J := Kv (v : G) ⊔ S₀
  let E := reducedTwoSubgroup J
  let : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
  let q := ChapterB.InternalThompsonAction.actionMk E
  let ρ := ChapterB.InternalThompsonAction.action E
  let B := ((Kv (v : G)).subgroupOf J).map q
  let O := offenderSubgroup ρ
  let C := B.subgroupOf O
  obtain ⟨_,_,hBO,⟨c⟩⟩ := H.nonsingular_canonical_quasisimple_of_ff D v hv
    S₀ (map_subtype_le _) (S.isPGroup'.map _) hker hff
  obtain ⟨b⟩ := H.nonsingular_canonical_component_image D v hv S₀ (map_subtype_le _) hker
  obtain ⟨e₄⟩ := H.nonsingular_normalizer_binary_four D v hv hTV hnot hs hi he hNM
  let e : C ≃* SL(4,ZMod 2) := (subgroupOfEquivOfLe hBO).trans (b.trans e₄)
  refine ⟨S,hTS,(H.nonsingular_normalizer_ambient_sylow D v hv hTV hnot hs hi he hNM S hTS).2,
    hred,hker,hm,?_⟩
  let K := (Kv (v : G)).subgroupOf J
  have hLJ : Lv L (v : G) ≤ J :=
    (H.nonsingular_canonical_component D v hv).2.1.trans le_sup_left
  obtain ⟨v₀,hv₀,hv₀ne,_,hline,_⟩ := D.nonsingular_moved_fixed_line H.chosen v hv
  have hcmap : (⁅E,K⁆ : Subgroup J).map J.subtype = ⁅U (Kv (v : G)) S₀,Kv (v : G)⁆ := by
    rw [map_commutator,map_subgroupOf_eq_of_le (show Kv (v : G) ≤ J from le_sup_left),←hred]
  have hwmap : (v₀ : G) ∈ (⁅E,K⁆ : Subgroup J).map J.subtype := by
    rw [hcmap]
    exact hm hv₀
  obtain ⟨w,hw,hwv⟩ := hwmap
  change (w : G) = (v₀ : G) at hwv
  obtain ⟨a⟩ := D.nonsingular_local_quotient H.chosen H.source.quasisimple v hv
  have h5 : 5 ∣ Nat.card (Lv L (v : G)) := by
    apply dvd_trans _ (card_quotient_dvd_card (pCore 2 (Lv L (v : G))))
    rw [Nat.card_congr a.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    decide
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := Lv L (v : G)) 5 h5
  let xJ : J := ⟨x,hLJ x.property⟩
  have hxK : xJ ∈ K := (H.nonsingular_canonical_component D v hv).2.1 x.property
  have hxJ : orderOf xJ = 5 := by
    rw [←Subgroup.orderOf_coe,Subgroup.orderOf_coe x]
    exact hx
  have hxq : orderOf (q xJ) = 5 := by
    exact (q.orderOf_map_eq_of_coprime_of_isPGroup_ker
      (by rw [QuotientGroup.ker_mk',hker]; exact pCore_isPGroup) xJ
      (by rw [hxJ]; decide)).trans hxJ
  have hv₀fix : (v₀ : G) ∈ centralizer (Lv L (v : G) : Set G) :=
    (show zpowers (v₀ : G) ≤ centralizer (Lv L (v : G) : Set G) from
      hline.symm ▸ (inf_le_right : ZV (Lv L (v : G)) (Vv L V (v : G)) ≤ _))
      (mem_zpowers _)
  have hw1 : w ≠ 1 := by
    intro hw1
    apply hv₀ne
    apply Subtype.ext
    exact hwv.symm.trans (congrArg J.subtype hw1)
  have hcomm : xJ * w = w * xJ := by
    apply Subtype.ext
    change (x : G) * w.val = w.val * (x : G)
    rw [hwv]
    exact mem_centralizer_iff.mp hv₀fix x x.property
  exact canonical_orthogonal_of_quintic_fixed E K hBO c e xJ hxK hxq w hw hw1 hcomm

/-- The actual canonical moved module has orthogonal or augmentation coordinates. -/
theorem SourceHypothesis.nonsingular_normalizer_moved_model
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hnot : ¬ IsQuasisimple (Kv (v : G)))
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (he : ¬ Kv (v : G) ≤ M L)
    (hNM : normalizer (Rv T L (v : G) : Set G) ≤ M L) :
    ∃ S : Sylow 2 (Gv (v : G)),
      let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
      let J := Kv (v : G) ⊔ S₀
      let E := reducedTwoSubgroup J
      letI : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
      Tv T (v : G) ≤ S₀ ∧
      (∃ P : Sylow 2 G, (P : Subgroup G) = S₀) ∧
      U (Kv (v : G)) S₀ = E.map J.subtype ∧
      Vv L V (v : G) ≤ ⁅U (Kv (v : G)) S₀,Kv (v : G)⁆ ∧
      CanonicalOrthogonalMoved E ((Kv (v : G)).subgroupOf J) := by
  obtain ⟨S,hTS,hSyl,hred,hker,hm,hmodel⟩ :=
    H.nonsingular_normalizer_moved_model_with_kernel D v hv hTV hnot hs hi he hNM
  exact ⟨S,hTS,hSyl,hred,hm,hmodel⟩
end CFSG.Quasithin.Chapter12.Section06
namespace CFSG.Quasithin.Chapter12.Section06
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open ChapterB.QuasisimpleSource
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The literal ambient moved subgroup has order 64 or 128 and strictly contains V_v. -/
theorem SourceHypothesis.nonsingular_normalizer_moved_card
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hnot : ¬ IsQuasisimple (Kv (v : G)))
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (he : ¬ Kv (v : G) ≤ M L)
    (hNM : normalizer (Rv T L (v : G) : Set G) ≤ M L) :
    ∃ S : Sylow 2 (Gv (v : G)),
      let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
      let W := ⁅U (Kv (v : G)) S₀,Kv (v : G)⁆
      Tv T (v : G) ≤ S₀ ∧
      (∃ P : Sylow 2 G, (P : Subgroup G) = S₀) ∧
      Vv L V (v : G) < W ∧ (Nat.card W = 64 ∨ Nat.card W = 128) := by
  obtain ⟨S,hS⟩ := H.nonsingular_normalizer_moved_model D v hv hTV hnot hs hi he hNM
  let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  let J := Kv (v : G) ⊔ S₀
  let E := reducedTwoSubgroup J
  let : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
  let q := ChapterB.InternalThompsonAction.actionMk E
  let ρ := ChapterB.InternalThompsonAction.action E
  let K := (Kv (v : G)).subgroupOf J
  let B := K.map q
  let O := offenderSubgroup ρ
  let C := B.subgroupOf O
  let W := ⁅U (Kv (v : G)) S₀,Kv (v : G)⁆
  change Tv T (v : G) ≤ S₀ ∧ (∃ P : Sylow 2 G, (P : Subgroup G) = S₀) ∧
    U (Kv (v : G)) S₀ = E.map J.subtype ∧ Vv L V (v : G) ≤ W ∧
    CanonicalOrthogonalMoved E K at hS
  obtain ⟨hTS,hSyl,hred,hm,hBO,s,_,_,hd⟩ := hS
  have hsW : s.space.toSubmodule = subspaceCommutator ρ ⊤ B := by
    rw [s.space_eq]
    change subspaceCommutator (ρ.comp O.subtype) ⊤ C = subspaceCommutator ρ ⊤ B
    rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hBO]
  let Kcomm := (⁅E,K⁆ : Subgroup J)
  let : IsElementaryAbelian 2 Kcomm :=
    IsElementaryAbelian.of_injective (inclusion (commutator_le_left E K))
      (inclusion_injective _)
  let e := NormalElementaryQuotient.movedEquiv E q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) K
  have hcmap : Kcomm.map J.subtype = W := by
    rw [map_commutator,map_subgroupOf_eq_of_le (show Kv (v : G) ≤ J from le_sup_left),←hred]
  have hc : Nat.card W = Nat.card s.space.toSubmodule := by
    rw [←hcmap,Nat.card_congr (Kcomm.equivMapOfInjective J.subtype J.subtype_injective).symm.toEquiv]
    rw [Nat.card_congr (Additive.ofMul : Kcomm ≃ Additive Kcomm)]
    exact (Nat.card_congr e.toEquiv).trans (Nat.card_congr (LinearEquiv.ofEq _ _ hsW.symm).toEquiv)
  have hcard : Nat.card W = 64 ∨ Nat.card W = 128 := by
    rw [hc,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    rcases hd with hd | hd
    · left; rw [hd]; rfl
    · right; rw [hd]; rfl
  have hne : Vv L V (v : G) ≠ W := by
    intro heq
    have hh : Nat.card W = 32 := heq ▸ D.nonsingular_moved_card H.chosen v hv
    rcases hcard with hcard | hcard <;> omega
  exact ⟨S,hTS,hSyl,lt_iff_le_and_ne.mpr ⟨hm,hne⟩,hcard⟩
end CFSG.Quasithin.Chapter12.Section06
namespace CFSG.Quasithin.Chapter12.Section06
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The original preferred point inherits the whole-module comparison, with
nonquasisimplicity discharged by the nontrivial original fixed space. -/
theorem SourceHypothesis.exists_preferred_nonsingular_normalizer_moved_of_fixed
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hz : ZV L V ≠ ⊥)
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L) :
    ∃ w : V, D.Nonsingular w ∧ ¬ Gv (w : G) ≤ M L ∧
      Chapter1.IsSylowIn 2 (Tv T (w : G)) (Mv L (w : G)) ∧
      (Tv T (w : G)).relIndex (T : Subgroup G) = 4 ∧
      Lv L (w : G) < Kv (w : G) ∧ ¬ Kv (w : G) ≤ M L ∧
      V ⊓ centralizer (Kv (w : G) : Set G) = zpowers (w : G) ∧
      ¬ IsQuasisimple (Kv (w : G)) ∧
      (normalizer (Rv T L (w : G) : Set G) ≤ M L →
        ∃ S : Sylow 2 (Gv (w : G)),
          let S₀ := (S : Subgroup (Gv (w : G))).map (Gv (w : G)).subtype
          let W := ⁅U (Kv (w : G)) S₀,Kv (w : G)⁆
          Tv T (w : G) ≤ S₀ ∧
          (∃ P : Sylow 2 G, (P : Subgroup G) = S₀) ∧
          Vv L V (w : G) < W ∧ (Nat.card W = 64 ∨ Nat.card W = 128)) := by
  obtain ⟨w,hw,he,hs,hi,hlt,hnot,hline,hnq,_⟩ :=
    H.exists_preferred_nonsingular_normalizer_symmetric_of_fixed D hTV hTI hz v hv he
  exact ⟨w,hw,he,hs,hi,hlt,hnot,hline,hnq,
    fun hNM => H.nonsingular_normalizer_moved_card D w hw hTV hnq hs hi hnot hNM⟩
end CFSG.Quasithin.Chapter12.Section06
