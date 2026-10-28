module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.CanonicalSevenModule

/-!
# The canonical SL4(2) case at the original nonsingular point

An order-five element of the original L_v fixes its nonzero local fixed
vector. B.5.1 therefore selects the orthogonal whole moved module: the
natural six-space or the seven-dimensional augmentation core. The A6 image
has trivial two-core inside A8. In either whole module its moved subspace
has zero intersection with the A8-fixed space, so C_{V_v}(K_v)=1.

The original projection V -> V/C_V(L) then forces C_V(L) nontrivial.
This extends the contrary-normalizer calculation to every selected Sylow
with the stated canonical geometry. CanonicalFixedSpace applies it in the
fixed-free branch. The canonical FF premise remains explicit.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
12.6.17--18, printed p.827, and B.5.1, printed pp.99--103.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
open ChapterB.QuasisimpleSource
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

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- A fixed quintic vector in the original local five-space selects the whole
orthogonal canonical module for an SL4(2) component. -/
theorem SourceHypothesis.nonsingular_canonical_four_moved
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (S : Sylow 2 (Gv (v : G)))
    (hfour : Nonempty (Star (Kv (v : G)) ≃* SL(4,ZMod 2)))
    (hred : U (Kv (v : G)) ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) =
      (reducedTwoSubgroup (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G)).map
        (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G).subtype)
    (hm : Vv L V (v : G) ≤ ⁅U (Kv (v : G)) ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype),Kv (v : G)⁆)
    (hker : centralizer (reducedTwoSubgroup (Kv (v : G) ⊔
      (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G) :
      Set (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G)) =
        pCore 2 (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G)) :
    let J := Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
    let E := reducedTwoSubgroup J
    letI : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
    IsFFModule (ChapterB.InternalThompsonAction.action E) →
      CanonicalOrthogonalMoved E ((Kv (v : G)).subgroupOf J) := by
  let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  let J := Kv (v : G) ⊔ S₀
  let E := reducedTwoSubgroup J
  let : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
  let K := (Kv (v : G)).subgroupOf J
  let q := ChapterB.InternalThompsonAction.actionMk E
  let ρ := ChapterB.InternalThompsonAction.action E
  let B := K.map q
  let O := offenderSubgroup ρ
  let C := B.subgroupOf O
  change IsFFModule ρ → CanonicalOrthogonalMoved E K
  intro hff
  obtain ⟨_,_,hBO,⟨c⟩⟩ := H.nonsingular_canonical_quasisimple_of_ff D v hv
    S₀ (map_subtype_le _) (S.isPGroup'.map _) hker hff
  obtain ⟨b⟩ := H.nonsingular_canonical_component_image D v hv S₀ (map_subtype_le _) hker
  obtain ⟨e₄⟩ := hfour
  let e : C ≃* SL(4,ZMod 2) := (subgroupOfEquivOfLe hBO).trans (b.trans e₄)
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
  let s := c.sectionData
  have hcase := SourceCompletion.BinaryActor.actionCase (ρ.comp O.subtype) (Or.inl rfl) e c.clause_one
  obtain ⟨y,hy,z,hz,hfix⟩ := canonical_moved_quintic_fixed E K O hBO s xJ hxK hxq w hw hw1 hcomm
  exact ⟨hBO,s,SourceCompletion.BinaryActor.orthogonal_of_quintic_fixed s hcase y hy z hz hfix⟩

/-- The literal local five-space has no nonidentity K_v-fixed vector in the
canonical SL4(2) case; no normalizer-containment premise is needed. -/
theorem SourceHypothesis.nonsingular_canonical_four_local_centralizer
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (S : Sylow 2 (Gv (v : G)))
    (hfour : Nonempty (Star (Kv (v : G)) ≃* SL(4,ZMod 2)))
    (hred : U (Kv (v : G)) ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) =
      (reducedTwoSubgroup (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G)).map
        (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G).subtype)
    (hm : Vv L V (v : G) ≤ ⁅U (Kv (v : G)) ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype),Kv (v : G)⁆)
    (hker : centralizer (reducedTwoSubgroup (Kv (v : G) ⊔
      (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G) :
      Set (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G)) =
        pCore 2 (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G)) :
    let J := Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
    let E := reducedTwoSubgroup J
    letI : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
    IsFFModule (ChapterB.InternalThompsonAction.action E) →
      Vv L V (v : G) ⊓ centralizer (Kv (v : G) : Set G) = ⊥ := by
  dsimp only
  intro hff
  have hmodel := H.nonsingular_canonical_four_moved D v hv S hfour hred hm hker hff
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
  obtain ⟨b⟩ := H.nonsingular_canonical_component_image D v hv S₀ (map_subtype_le _) hker
  obtain ⟨e₄⟩ := hfour
  let eB : K.map q ≃* alternatingGroup (Fin 8) := b.trans (e₄.trans
    ((BinaryLinear.OuterCyclic.projectiveEquivSL (by decide : 0 < 4)).symm.trans
      Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.symm))
  let a₀ : A ≃* Lv L (v : G) := subgroupOfEquivOfLe hLJ
  obtain ⟨eA⟩ := D.nonsingular_local_quotient H.chosen H.source.quasisimple v hv
  have hkA : IsPGroup 2 (q.subgroupMap A).ker := by
    rw [Subgroup.ker_subgroupMap,QuotientGroup.ker_mk',hker]
    exact pCore_isPGroup.comap_subtype
  let a₁ : (A.map q ⧸ pCore 2 (A.map q)) ≃* alternatingGroup (Fin 6) :=
    ((q.subgroupMap A).pCoreQuotientEquiv (q.subgroupMap_surjective A) hkA).symm.trans
      ((QuotientGroup.congr _ _ a₀ (pCore_map_iso 2 a₀)).trans eA)
  have h5 : 5 ∣ Nat.card (A.map q) := by
    apply dvd_trans _ (card_quotient_dvd_card (pCore 2 (A.map q)))
    rw [Nat.card_congr a₁.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    decide
  have hcore := Theory.SpecificGroups.Alternating.EightSectionExtension.twoCore_eq_bot_of_five
    (K.map q) (A.map q) eB (map_mono (show A ≤ K from fun _ hx => hLK hx)) h5
  let a : A.map q ≃* alternatingGroup (Fin 6) := QuotientGroup.quotientBot.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hcore.symm).trans a₁)
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

/-- The canonical SL4(2) FF case forces the original global fixed space to
be nontrivial, through the unchanged local line and central projection. -/
theorem SourceHypothesis.fixed_ne_bot_of_canonical_four
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (S : Sylow 2 (Gv (v : G)))
    (hfour : Nonempty (Star (Kv (v : G)) ≃* SL(4,ZMod 2)))
    (hred : U (Kv (v : G)) ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) =
      (reducedTwoSubgroup (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G)).map
        (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G).subtype)
    (hm : Vv L V (v : G) ≤ ⁅U (Kv (v : G)) ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype),Kv (v : G)⁆)
    (hker : centralizer (reducedTwoSubgroup (Kv (v : G) ⊔
      (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G) :
      Set (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G)) =
        pCore 2 (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G)) :
    let J := Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
    let E := reducedTwoSubgroup J
    letI : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
    IsFFModule (ChapterB.InternalThompsonAction.action E) →
      ZV L V ≠ ⊥ := by
  dsimp only
  intro hff
  have hc := H.nonsingular_canonical_four_local_centralizer D v hv S hfour hred hm hker hff
  apply D.fixed_ne_bot_of_local_line_moved H.chosen v hv
  intro hline
  have hz : ZV (Lv L (v : G)) (Vv L V (v : G)) = ⊥ :=
    bot_unique ((le_inf inf_le_left hline).trans hc.le)
  have hh := D.nonsingular_moved_fixed_card H.chosen v hv
  rw [hz,card_bot] at hh
  norm_num at hh


end CFSG.Quasithin.Chapter12.Section06
