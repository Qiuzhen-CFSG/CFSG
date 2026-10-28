module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.NormalizerModule
public import Theory.Representation.BinaryPermutation.EightSixMovedFixed
public import Theory.Representation.NormalElementaryQuotient.SubgroupSpace

/-!
# Movement of the original local fixed line

In the contrary normalizer branch, the canonical moved module is the natural
six-space or the seven-dimensional augmentation core for the actual A8 image.
An A6 subgroup fixes two of the eight letters. Its commutator vectors vanish
there, whereas the A8-fixed core vectors are constant; their intersection is
zero. The natural six-space also has no nonzero fixed vector.

Transporting this calculation through the original canonical quotient and
V_v = [V_v,L_v] proves C_{V_v}(K_v)=1. Thus K_v moves the original nontrivial
line C_{V_v}(L_v). The original projection then forces C_V(L) to be nontrivial.
This proves normalizer escape when that original fixed space is trivial and
K_v is not quasisimple. The preferred-point application discharges
nonquasisimplicity in the nontrivial fixed-space branch and retains the
ambient Sylow, the original V and the literal local line.

The 12.6.16 conjugacy argument remains for the nontrivial fixed-space branch
of 12.6.17. HS/J4 exclusions, general canonical-module arguments, blocks,
splitting and fixed-space elimination remain; neither 12.6.2 nor 12.6.23 is
asserted. Earlier invariance/TI retain producer qt-d-1222-source; final
source discharge remains with qt-d-12634-source.
Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
12.6.16--17, printed pp.826--827.
-/

public section
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.Chapter12.Section06
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open ChapterB.QuasisimpleSource
open scoped IsMulCommutative

private theorem orthogonal_local_moved_fixed_eq_zero
    {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W)
    (hm : IsAlternatingNatural ρ 8 ∨ Nonempty (ActionEquiv ρ
      (BinaryPermutation.alternatingCoreRepresentation (Fin 8))))
    (A : Subgroup D) (eA : A ≃* alternatingGroup (Fin 6)) (w : W)
    (hw : w ∈ subspaceCommutator ρ ⊤ A) (hf : ∀ g, ρ g w = w) : w = 0 := by
  rcases hm with hm | hm
  · obtain ⟨e⟩ := hm
    apply e.linearEquiv.injective
    rw [map_zero]
    apply BinaryPermutation.eight_natural_fixed_eq_zero
    intro g
    obtain ⟨a,rfl⟩ := e.groupEquiv.surjective g
    exact (e.intertwines a w).symm.trans (congrArg e.linearEquiv (hf a))
  · obtain ⟨e⟩ := hm
    let B := A.map e.groupEquiv.toMonoidHom
    let b : B ≃* alternatingGroup (Fin 6) :=
      (A.equivMapOfInjective _ e.groupEquiv.injective).symm.trans eA
    have hmap : subspaceCommutator ρ ⊤ A ≤
        (subspaceCommutator (BinaryPermutation.alternatingCoreRepresentation (Fin 8)) ⊤ B).comap
          e.linearEquiv.toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨a,ha,u,_,rfl⟩
      change e.linearEquiv (ρ a u - u) ∈
        subspaceCommutator (BinaryPermutation.alternatingCoreRepresentation (Fin 8)) ⊤ B
      rw [map_sub,e.intertwines]
      exact Submodule.subset_span ⟨_,mem_map_of_mem _ ha,_,Submodule.mem_top,rfl⟩
    apply e.linearEquiv.injective
    rw [map_zero]
    apply BinaryPermutation.eight_core_six_moved_fixed_eq_zero B b _ (hmap hw)
    intro g
    obtain ⟨a,rfl⟩ := e.groupEquiv.surjective g
    exact (e.intertwines a w).symm.trans (congrArg e.linearEquiv (hf a))

private theorem canonical_orthogonal_local_centralizer
    {D : Type*} [Group D]
    (E : Subgroup D) [E.Normal] [IsElementaryAbelian 2 E]
    (K A W : Subgroup D) (hAK : A ≤ K)
    (hm : CanonicalOrthogonalMoved E K)
    (eA : A.map (ChapterB.InternalThompsonAction.actionMk E) ≃* alternatingGroup (Fin 6))
    (hW : W ≤ ⁅E,K⁆) (hgen : ⁅W,A⁆ = W) :
    W ⊓ centralizer (K : Set D) = ⊥ := by
  let q := ChapterB.InternalThompsonAction.actionMk E
  let ρ := ChapterB.InternalThompsonAction.action E
  let B := K.map q
  let O := offenderSubgroup ρ
  let C := B.subgroupOf O
  obtain ⟨hBO,s,_,hmodel,_⟩ := hm
  let A₀ := (A.map q).subgroupOf O
  let A₁ := A₀.subgroupOf C
  have hAO : A.map q ≤ O := (map_mono hAK).trans hBO
  have hAC : A₀ ≤ C := fun _ ha => map_mono hAK ha
  let a : A₁ ≃* alternatingGroup (Fin 6) :=
    (subgroupOfEquivOfLe hAC).trans ((subgroupOfEquivOfLe hAO).trans eA)
  have hspace : s.space.toSubmodule = subspaceCommutator ρ ⊤ B := by
    rw [s.space_eq]
    change subspaceCommutator (ρ.comp O.subtype) ⊤ C = _
    rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hBO]
  let I := NormalElementaryQuotient.subgroupSpace E W
  have hI : I ≤ s.space.toSubmodule := by
    rw [hspace]
    change I ≤ subspaceCommutator (NormalElementaryQuotient.representation E q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) ⊤ (K.map q)
    rw [←NormalElementaryQuotient.commutatorSpace_eq E q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) K]
    exact fun _ hx => hW hx
  have hIgen : subspaceCommutator ρ I (A.map q) = I := by
    change subspaceCommutator (NormalElementaryQuotient.representation E q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) I (A.map q) = I
    rw [←NormalElementaryQuotient.subgroupSpace_commutator E q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) W A
      (hW.trans (commutator_le_left E K)),hgen]
  have hmap : (subspaceCommutator (s.space.toRepresentation.comp C.subtype) ⊤ A₁).map
      s.space.toSubmodule.subtype = subspaceCommutator ρ s.space.toSubmodule (A.map q) := by
    rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hAC]
    have hh := subspaceCommutator_map_embedding (ρ.comp O.subtype) s.space.toRepresentation
      (MonoidHom.id O) s.space.toSubmodule.subtype (fun _ _ => rfl) A₀ ⊤
    rw [Submodule.map_top,Submodule.range_subtype,Subgroup.map_id,
      subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hAO] at hh
    exact hh.symm
  apply bot_unique
  intro x hx
  let u : Additive E := Additive.ofMul ⟨x,hW.trans (commutator_le_left E K) hx.1⟩
  have hu : u ∈ I := hx.1
  let z : s.space.toSubmodule := ⟨u,hI hu⟩
  have hz : z ∈ subspaceCommutator (s.space.toRepresentation.comp C.subtype) ⊤ A₁ := by
    have hh : u ∈ subspaceCommutator ρ s.space.toSubmodule (A.map q) :=
      (subspaceCommutator_mono_left ρ hI _) (hIgen.symm ▸ hu)
    rw [←hmap] at hh
    obtain ⟨y,hy,he⟩ := hh
    exact (show y = z from Subtype.ext he) ▸ hy
  have hzfix : ∀ c : C, (s.space.toRepresentation.comp C.subtype) c z = z := by
    intro c
    obtain ⟨k,hk,hkc⟩ := c.property
    change q k = c.val.val at hkc
    apply Subtype.ext
    change ρ c.val.val u = u
    rw [←hkc]
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [ChapterB.InternalThompsonAction.action_apply]
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hx.2 k hk)
  have hz0 := orthogonal_local_moved_fixed_eq_zero _ hmodel A₁ a z hz hzfix
  exact congrArg (fun z : s.space.toSubmodule => z.val.toMul.val) hz0
end CFSG.Quasithin.Chapter12.Section06

namespace CFSG.Quasithin.Chapter12.Section06
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open ChapterB.QuasisimpleSource
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- In the contrary normalizer branch the original moved five-space has no
nonidentity vector centralized by K_v. -/
theorem SourceHypothesis.nonsingular_normalizer_local_centralizer
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hnot : ¬ IsQuasisimple (Kv (v : G)))
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (he : ¬ Kv (v : G) ≤ M L)
    (hNM : normalizer (Rv T L (v : G) : Set G) ≤ M L) :
    Vv L V (v : G) ⊓ centralizer (Kv (v : G) : Set G) = ⊥ := by
  obtain ⟨S,hTS,_,hred,hker,hm,hmodel⟩ :=
    H.nonsingular_normalizer_moved_model_with_kernel D v hv hTV hnot hs hi he hNM
  let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  let J := Kv (v : G) ⊔ S₀
  let E := reducedTwoSubgroup J
  let : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
  let K := (Kv (v : G)).subgroupOf J
  let A := (Lv L (v : G)).subgroupOf J
  let W := (Vv L V (v : G)).subgroupOf J
  let q := ChapterB.InternalThompsonAction.actionMk E
  have hLK := (H.nonsingular_canonical_component D v hv).2.1
  have hLJ : Lv L (v : G) ≤ J := hLK.trans le_sup_left
  have hWJ : Vv L V (v : G) ≤ J := (Vv_le_Lv H.chosen v).trans hLJ
  have hAmap : A.map J.subtype = Lv L (v : G) := map_subgroupOf_eq_of_le hLJ
  have hKmap : K.map J.subtype = Kv (v : G) := map_subgroupOf_eq_of_le le_sup_left
  have hWmap : W.map J.subtype = Vv L V (v : G) := map_subgroupOf_eq_of_le hWJ
  have hcmap : (⁅E,K⁆ : Subgroup J).map J.subtype = ⁅U (Kv (v : G)) S₀,Kv (v : G)⁆ := by
    rw [map_commutator,hKmap,←hred]
  have hW : W ≤ ⁅E,K⁆ := by
    intro w hw
    have hh : (w : G) ∈ (⁅E,K⁆ : Subgroup J).map J.subtype := by
      rw [hcmap]
      exact hm hw
    obtain ⟨y,hy,hyw⟩ := hh
    exact (J.subtype_injective hyw) ▸ hy
  have hgen : ⁅W,A⁆ = W := by
    apply map_injective J.subtype_injective
    rw [map_commutator,hWmap,hAmap,D.local_moved_generated H.chosen v hv]
  obtain ⟨eA⟩ :=
    (H.nonsingular_normalizer_symmetric_quotient D v hv hTV hnot hs hi he hNM S hTS).2.2.1
  let eQ : ChapterB.InternalThompsonAction.ActionQuotient E ≃* Star J :=
    QuotientGroup.quotientMulEquivOfEq hker
  have hAq : (A.map q).map eQ.toMonoidHom = starImage J (Lv L (v : G)) := by
    rw [map_map]
    rfl
  let a : A.map q ≃* alternatingGroup (Fin 6) :=
    ((A.map q).equivMapOfInjective _ eQ.injective).trans
      ((MulEquiv.subgroupCongr hAq).trans eA)
  have hc := canonical_orthogonal_local_centralizer E K A W
    (fun _ hx => hLK hx) hmodel a hW hgen
  apply bot_unique
  intro x hx
  have hh : (⟨x,hWJ hx.1⟩ : J) ∈ W ⊓ centralizer (K : Set J) := by
    refine ⟨hx.1,?_⟩
    apply mem_centralizer_iff.mpr
    intro k hk
    apply Subtype.ext
    exact mem_centralizer_iff.mp hx.2 k hk
  have hh1 := Subgroup.mem_bot.mp (hc.le hh)
  exact congrArg J.subtype hh1

/-- The original local fixed line is moved, and its original quotient
projection forces the original global fixed space to be nontrivial. -/
theorem SourceHypothesis.nonsingular_normalizer_local_line_moved
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hnot : ¬ IsQuasisimple (Kv (v : G)))
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (he : ¬ Kv (v : G) ≤ M L)
    (hNM : normalizer (Rv T L (v : G) : Set G) ≤ M L) :
    ¬ ZV (Lv L (v : G)) (Vv L V (v : G)) ≤ centralizer (Kv (v : G) : Set G) ∧
      ZV L V ≠ ⊥ := by
  have hline : ¬ ZV (Lv L (v : G)) (Vv L V (v : G)) ≤ centralizer (Kv (v : G) : Set G) := by
    intro hc
    have hz : ZV (Lv L (v : G)) (Vv L V (v : G)) = ⊥ := by
      apply bot_unique
      exact (le_inf inf_le_left hc).trans
        (H.nonsingular_normalizer_local_centralizer D v hv hTV hnot hs hi he hNM).le
    have hh := D.nonsingular_moved_fixed_card H.chosen v hv
    rw [hz,card_bot] at hh
    norm_num at hh
  exact ⟨hline,D.fixed_ne_bot_of_local_line_moved H.chosen v hv hline⟩

/-- The trivial original fixed-space branch of normalizer escape, with the
quasisimplicity exclusion still explicit. -/
theorem SourceHypothesis.nonsingular_normalizer_escape_of_fixed_eq_bot
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hnot : ¬ IsQuasisimple (Kv (v : G)))
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (he : ¬ Kv (v : G) ≤ M L) (hz : ZV L V = ⊥) :
    ¬ normalizer (Rv T L (v : G) : Set G) ≤ M L := by
  intro hNM
  exact (H.nonsingular_normalizer_local_line_moved D v hv hTV hnot hs hi he hNM).2 hz
end CFSG.Quasithin.Chapter12.Section06

namespace CFSG.Quasithin.Chapter12.Section06
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- At the original preferred point, nontrivial C_V(L) supplies the remaining
nonquasisimplicity premise. The contrary normalizer assumption then moves the
original local fixed line and puts the selected local Sylow in Syl₂(G). -/
theorem SourceHypothesis.exists_preferred_nonsingular_normalizer_line_of_fixed
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
        (Vv L V (w : G) ⊓ centralizer (Kv (w : G) : Set G) = ⊥) ∧
        (¬ ZV (Lv L (w : G)) (Vv L V (w : G)) ≤ centralizer (Kv (w : G) : Set G)) ∧
        ∃ S : Sylow 2 (Gv (w : G)),
          let S₀ := (S : Subgroup (Gv (w : G))).map (Gv (w : G)).subtype
          let W := ⁅U (Kv (w : G)) S₀,Kv (w : G)⁆
          Tv T (w : G) ≤ S₀ ∧
          (∃ P : Sylow 2 G, (P : Subgroup G) = S₀) ∧
          Vv L V (w : G) < W ∧ (Nat.card W = 64 ∨ Nat.card W = 128)) := by
  obtain ⟨w,hw,he,hs,hi,hlt,hnot,hline,hnq,hm⟩ :=
    H.exists_preferred_nonsingular_normalizer_moved_of_fixed D hTV hTI hz v hv he
  refine ⟨w,hw,he,hs,hi,hlt,hnot,hline,hnq,fun hNM => ?_⟩
  exact ⟨H.nonsingular_normalizer_local_centralizer D w hw hTV hnq hs hi hnot hNM,
    (H.nonsingular_normalizer_local_line_moved D w hw hTV hnq hs hi hnot hNM).1,hm hNM⟩
end CFSG.Quasithin.Chapter12.Section06
