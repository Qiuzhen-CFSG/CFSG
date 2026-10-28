module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.CentralCore
public import Theory.Representation.SpecialLinearThreeTransitivity
public import Theory.GroupTheory.GeneralizedFitting.InternalModuleResidual

/-!
# Recognizing the actual block in the natural whole-core row

A natural whole-core section is transitive on nonzero vectors. Its nonzero
initial moved subgroup is K-invariant, so it is the whole core. The initial
splitting therefore supplies centrality in O₂(KR) and a trivial fixed factor.
Transport through the literal inclusion identifies the intrinsic blockU(K).
Transitivity proves its invariant-subgroup interval; subnormal Fitting
monotonicity and the original quotient supply the remaining short conditions.
The section coordinates give the actual block module and its conjugation law.

Thus a whole natural section yields both the relative block in KR and an
SL₃-even block with the original full quotient marking. Combined with the
central-core recognition, this gives a genuine block or a doubled whole core.
The original nonblock application excludes the block on its original c.K.
The doubled-row radical inequality and noncentral-core branches remain open.
Source: Aschbacher--Smith C.1.7, C.1.34(1)--(2), printed pp.123,136--137,
and original 4.3.8--10, pp.616--617.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {K R : Subgroup G}
variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
variable (h : LinearThreeMSPair KnownSimple.IsKnownSimple K R n F) (hn : 1 < n)

include h hn
omit [CharP F 2] in
private theorem moved_ne_bot : initialMoved K R ≠ ⊥ := by
  intro hu
  have hc : K ≤ centralizer (initialOmega K R : Set G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hu)
  apply component_not_le_centralOmegaKernel h hn
  intro k hk v hv
  exact Subtype.ext (hc hk v (mem_map_of_mem _ hv))

omit [CharP F 2] in
private theorem moved_normalized : K ≤ normalizer (initialMoved K R) := by
  let := component_normal h hn
  have he : initialMoved K R =
      (⁅centralOmegaLayer K R,K.subgroupOf (K ⊔ R)⁆).map (K ⊔ R).subtype := by
    rw [map_commutator,map_subgroupOf_eq_of_le (show K ≤ K ⊔ R from le_sup_left)]
    rfl
  rw [he]
  exact (le_sup_left : K ≤ K ⊔ R).trans
    ((normal_subgroupOf_iff_le_normalizer (map_subtype_le _)).mp
      (by simpa only [subgroupOf,comap_map_eq_self_of_injective (K ⊔ R).subtype_injective]
        using (inferInstance : (⁅centralOmegaLayer K R,K.subgroupOf (K ⊔ R)⁆).Normal)))

omit h hn [Finite G] [Finite F] [CharP F 2] in
private theorem core_coordinates
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K (msQ K R) ⊥ (linearThreeActor e)
      (specialLinearNatural (k := F) 3)) :
    ∃ E : msQ K R ≃* Multiplicative (Fin 3 → F),
      ∀ (k : K) (x y : msQ K R), (y : G) = k * (x : G) * (k : G)⁻¹ →
        (E y).toAdd = specialLinearNatural 3 (linearThreeActor e k) (E x).toAdd := by
  rw [HasSectionModel,bot_subgroupOf] at hm
  obtain ⟨_,_,_,hbot,E,hE⟩ := hm
  let := hbot
  exact ⟨QuotientGroup.quotientBot.symm.trans E,hE⟩

omit [CharP F 2] in
/-- A whole natural section forces equality with the nonzero initial moved
subgroup by transitivity on nonzero vectors. -/
theorem msQ_eq_initialMoved_of_natural
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K (msQ K R) ⊥ (linearThreeActor e)
      (specialLinearNatural (k := F) 3)) : msQ K R = initialMoved K R := by
  obtain ⟨E,hE⟩ := core_coordinates e hm
  obtain ⟨u,hu,hu1⟩ := (initialMoved K R).bot_or_exists_ne_one.resolve_left (moved_ne_bot h hn)
  let uu : msQ K R := ⟨u,initialMoved_le_msQ hu⟩
  have hune : (E uu).toAdd ≠ 0 := by
    intro hz
    exact hu1 (congrArg Subtype.val (E.map_eq_one_iff.mp (Multiplicative.toAdd.injective hz)))
  apply le_antisymm _ initialMoved_le_msQ
  intro x hx
  by_cases hxe : x = 1
  · exact hxe ▸ (initialMoved K R).one_mem
  let xx : msQ K R := ⟨x,hx⟩
  have hxne : (E xx).toAdd ≠ 0 := by
    intro hz
    exact hxe (congrArg Subtype.val (E.map_eq_one_iff.mp (Multiplicative.toAdd.injective hz)))
  obtain ⟨g,hg⟩ := Matrix.SpecialLinearGroup.exists_mulVec_eq_three _ _ hune hxne
  obtain ⟨k,hk⟩ := e.surjective.comp (QuotientGroup.mk'_surjective _) g
  let y : msQ K R := (msQ K R).normalizerMonoidHom ⟨k,hm.2.1 k.property⟩ uu
  have hy : (y : G) = k * u * (k : G)⁻¹ := normalizerMonoidHom_apply_apply_coe _ _ _
  have he : E y = E xx := by
    apply Multiplicative.toAdd.injective
    rw [hE k uu y hy]
    change specialLinearNatural 3 (e (QuotientGroup.mk' _ k)) (E uu).toAdd = _
    rw [show e (QuotientGroup.mk' _ k) = g from hk]
    exact hg
  have hxy : x = k * u * (k : G)⁻¹ :=
    (congrArg Subtype.val (E.injective he)).symm.trans hy
  rw [hxy]
  exact (mem_normalizer_iff.mp (moved_normalized h hn k.property) u).mp hu

omit [CharP F 2] in
private theorem intrinsicCore_map : (blockU K).map K.subtype = msQ K R := by
  rw [msQ_eq_intrinsic h hn,blockU,map_commutator,
    ← MonoidHom.range_eq_map,K.range_subtype]
  rfl

omit [CharP F 2] in
private theorem intrinsicCore_coordinates
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K (msQ K R) ⊥ (linearThreeActor e)
      (specialLinearNatural (k := F) 3)) :
    ∃ E : blockU K ≃* Multiplicative (Fin 3 → F),
      ∀ (k : K) (u : blockU K), (E (blockConjugate K k u)).toAdd =
        specialLinearNatural 3 (e (QuotientGroup.mk' _ k)) (E u).toAdd := by
  obtain ⟨a,ha⟩ := core_coordinates e hm
  let b := ((blockU K).equivMapOfInjective K.subtype K.subtype_injective).trans
    (MulEquiv.subgroupCongr (intrinsicCore_map h hn))
  exact ⟨b.trans a,fun k u => ha k (b u) (b (blockConjugate K k u)) rfl⟩

private theorem intrinsicCore_fixed
    (hz : msQ K R ≤ centralizer ((K ⊔ R).pCoreIn 2 : Set G)) :
    blockU K ⊓ center K = ⊥ := by
  apply bot_unique
  intro x hx
  have hxQ : (x : G) ∈ msQ K R := (intrinsicCore_map h hn).le (mem_map_of_mem _ hx.1)
  have he : (x : G) ∈ msQ K R ⊓ centralizer (K : Set G) :=
    ⟨hxQ,fun k hk => congrArg K.subtype ((mem_center_iff.mp hx.2) ⟨k,hk⟩)⟩
  exact Subtype.ext ((msQ_fixed_eq_bot_of_central h hn hz).le he)

omit hn [CharP F 2] in
private theorem component_fitting : generalizedFitting K = pCore 2 K := by
  let J := (K ⊔ R : Subgroup G)
  let L := K.subgroupOf J
  have hL : generalizedFitting L = pCore 2 L := by
    apply le_antisymm _ ((pCore_le_fitting L 2).trans (fitting_le_generalizedFitting L))
    rw [pCore_subnormal_eq_comap 2 h.component.2.subnormal]
    apply map_le_iff_le_comap.mp
    rw [← h.fitting]
    exact generalizedFitting_map_subtype_le_of_isSubnormal L h.component.2.subnormal
  let a : L ≃* K := subgroupOfEquivOfLe (show K ≤ J from le_sup_left)
  rw [← map_generalizedFitting_equiv a,hL,pCore_map_iso]

/-- Every short-group clause follows from an actual natural whole-core
section. The initial-layer comparison supplies centrality and removes its
fixed factor; nonzero-vector transitivity proves the invariant interval. -/
theorem short_of_natural_msQ
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K (msQ K R) ⊥ (linearThreeActor e)
      (specialLinearNatural (k := F) 3)) : IsShort K := by
  have hz := (msQ_eq_initialMoved_iff h hn).mp (msQ_eq_initialMoved_of_natural h hn e hm)
  have hc : IsMulCommutative (msQ K R) :=
    le_centralizer_iff_isMulCommutative.mp (hz.trans (centralizer_le msQ_le_joinCore))
  let := abelian_msQ_elementary h hn hc
  let b := ((blockU K).equivMapOfInjective K.subtype K.subtype_injective).trans
    (MulEquiv.subgroupCongr (intrinsicCore_map h hn))
  obtain ⟨E,hE⟩ := intrinsicCore_coordinates h hn e hm
  have hfix := intrinsicCore_fixed h hn hz
  refine ⟨inferInstance,component_twoPerfect h hn,component_fitting h,
    IsElementaryAbelian.of_injective b.toMonoidHom b.injective,?_,
    Or.inl (quotient_quasisimple h),?_⟩
  · intro u hu z hz'
    apply Subtype.ext
    exact hz ((intrinsicCore_map h hn).le (mem_map_of_mem _ hu)) z
      (pCoreIn_mono_of_normalizes (show K ≤ K ⊔ R from le_sup_left)
        ((normal_subgroupOf_iff_le_normalizer (show K ≤ K ⊔ R from le_sup_left)).mp
          (component_normal h hn)) (mem_map_of_mem _ hz'))
  · rw [BlockModuleIrreducible,hfix]
    have hU : blockU K ≠ ⊥ := by
      intro hb
      have hQ : msQ K R = ⊥ := by rw [← intrinsicCore_map h hn,hb,Subgroup.map_bot]
      exact moved_ne_bot h hn (bot_unique (initialMoved_le_msQ.trans_eq hQ))
    refine ⟨bot_lt_iff_ne_bot.mpr hU,?_⟩
    intro N hN _ hNU
    by_cases hNb : N = ⊥
    · exact Or.inl hNb
    right
    apply le_antisymm hNU
    obtain ⟨u,hu,hu1⟩ := N.bot_or_exists_ne_one.resolve_left hNb
    let uu : blockU K := ⟨u,hNU hu⟩
    have hu0 : (E uu).toAdd ≠ 0 := by
      intro he
      exact hu1 (congrArg Subtype.val (E.map_eq_one_iff.mp (Multiplicative.toAdd.injective he)))
    intro x hx
    by_cases hx1 : x = 1
    · exact hx1 ▸ N.one_mem
    let xx : blockU K := ⟨x,hx⟩
    have hx0 : (E xx).toAdd ≠ 0 := by
      intro he
      exact hx1 (congrArg Subtype.val (E.map_eq_one_iff.mp (Multiplicative.toAdd.injective he)))
    obtain ⟨g,hg⟩ := Matrix.SpecialLinearGroup.exists_mulVec_eq_three _ _ hu0 hx0
    obtain ⟨k,hk⟩ := e.surjective.comp (QuotientGroup.mk'_surjective _) g
    have he : blockConjugate K k uu = xx := by
      apply E.injective
      apply Multiplicative.toAdd.injective
      rw [hE,show e (QuotientGroup.mk' _ k) = g from hk]
      exact hg
    have hval : k * u * k⁻¹ = x := congrArg Subtype.val he
    exact hval ▸ hN.conj_mem u hu k

private def naturalAction : SL(3,F) →* MulAut (Multiplicative (Fin 3 → F)) where
  toFun g := (Matrix.SpecialLinearGroup.toLin' g).toAddEquiv.toMultiplicative
  map_one' := by
    ext v : 1
    change Matrix.SpecialLinearGroup.toLin' 1 v.toAdd = v.toAdd
    rw [map_one]
    rfl
  map_mul' g k := by
    ext v : 1
    change Matrix.SpecialLinearGroup.toLin' (g*k) v.toAdd =
      Matrix.SpecialLinearGroup.toLin' g (Matrix.SpecialLinearGroup.toLin' k v.toAdd)
    rw [map_mul]
    rfl

/-- The natural whole-core row is an actual SL₃ block, including its literal
intrinsic module and the original full quotient marking. -/
theorem block_of_natural_msQ
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K (msQ K R) ⊥ (linearThreeActor e)
      (specialLinearNatural (k := F) 3)) :
    IsBlock (K.subgroupOf (K ⊔ R)) ∧ IsSL3EvenBlock K n := by
  have hs := short_of_natural_msQ h hn e hm
  have hz := (msQ_eq_initialMoved_iff h hn).mp (msQ_eq_initialMoved_of_natural h hn e hm)
  have hf : blockFixed K = ⊥ := by
    apply bot_unique
    intro u hu
    exact Subtype.ext ((intrinsicCore_fixed h hn hz).le ⟨u.property,hu⟩)
  obtain ⟨E,hE⟩ := intrinsicCore_coordinates h hn e hm
  let m : BlockModule K ≃* Multiplicative (Fin 3 → F) :=
    (QuotientGroup.quotientMulEquivOfEq hf).trans (QuotientGroup.quotientBot.trans E)
  refine ⟨⟨inferInstance,hs.of_mulEquiv
    (subgroupOfEquivOfLe (show K ≤ K ⊔ R from le_sup_left)).symm,h.component.2.subnormal⟩,
    h.positive,hs,F,inferInstance,inferInstance,h.field_card,naturalAction,
    ⟨{quotientIso := e,moduleIso := m,intertwining := ?_}⟩,fun _ _ => rfl⟩
  intro k u
  exact Multiplicative.toAdd.injective (hE k u)

/-- The central-core branch gives a genuine block or a doubled whole core.
The doubled-row Sylow radical inequality remains a separate obligation. -/
theorem block_or_doubled_msQ_of_central
    (hz : msQ K R ≤ centralizer ((K ⊔ R).pCoreIn 2 : Set G)) :
    ∃ e : (K ⧸ pCore 2 K) ≃* SL(3,F),
      (IsBlock (K.subgroupOf (K ⊔ R)) ∧ IsSL3EvenBlock K n ∧
        HasSectionModel K (msQ K R) ⊥ (linearThreeActor e)
          (specialLinearNatural (k := F) 3)) ∨
      HasSectionModel K (msQ K R) ⊥ (linearThreeActor e)
        ((specialLinearNatural (k := F) 3).prod (specialLinearNatural (k := F) 3)) := by
  obtain ⟨e,he⟩ := msQ_section_models_of_central h hn hz
  refine ⟨e,?_⟩
  rcases he with he | he
  · exact Or.inl ⟨(block_of_natural_msQ h hn e he).1,(block_of_natural_msQ h hn e he).2,he⟩
  · exact Or.inr he

end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource
