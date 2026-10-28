module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.Quotient
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Exceptional
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.InternalModule
public import Theory.GroupTheory.Commutator.SimpleSubnormal

/-!
# The genuine star kernel in a faithful short block

Put W = [U_I,L] and U = [O₂(L),L]. Characteristic two puts U_I in O₂(I),
so the already proved core-commutator equality gives W ≤ U. Perfectness
and the three-subgroup lemma show W is not central: otherwise L would
centralize U_I, contrary to the nontrivial star component. Short-block
irreducibility now gives W C_U(L) = U.

Every element of the star kernel centralizes W, since W ≤ U_I, and it
centralizes C_U(L) because it belongs to L. Thus it centralizes U.
When C_L(U) = O₂(L), as in the A-hat₆ block definition, the star kernel
is exactly O₂(L). The resulting compatible quotient equivalence carries
the genuine triple cover to L*, where the precise 15.3.27(3) excludes it.
No simplicity or block exclusion is assumed in this comparison.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.7,
printed p.123; C.1.22, p.129; 15.3.27(3), p.1131; and the first paragraph
of the proof of 15.3.31, p.1132.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
variable {G : Type*} [Group G]

private theorem local_span_le_core [Finite G] (d : LocalData G) {I : Subgroup G}
    (hf : HasCharacteristicTwo I) (hS : Chapter1.IsSylowIn 2 d.S I) :
    d.UI I ≤ I.pCoreIn 2 := by
  have hVT : d.V ≤ (d.T : Subgroup G) :=
    d.action.le_sylow d.T d.sylow_le (localModule_le d.T d.sylow_le)
  have hZI := (d.Z_le_S hVT).trans (Chapter1.isSylowIn_iff.mp hS).2.1
  have hU := d.UI_subgroupOf_le_coreOmega hS (d.Z_le_S hVT) hf
  intro x hx
  have h : (⟨x, d.UI_le hZI hx⟩ : I) ∈ pCore 2 I :=
    (Stellmacher.mem_omegaOneCenterAmbient_iff (pCore 2 I) _).mp (hU hx) |>.1
  exact mem_map_of_mem I.subtype h

/-- The actual moving subgroup generates the short block module modulo
its central layer. This uses neither a constituent marking nor simplicity. -/
theorem componentModule_sup_blockFixed (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hYL : d.Yplus ≤ c.L)
    (hnormal : (c.L.subgroupOf I).Normal)
    (hU : d.UI I ≤ I.pCoreIn 2) (hshort : IsShort c.L) :
    (d.componentModule I c.L).subgroupOf c.L ⊔
      (blockU c.L ⊓ center c.L) = blockU c.L := by
  have he : (blockU c.L).map c.L.subtype = extensionCore c.L := by
    rw [blockU, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
    rfl
  have hW : d.componentModule I c.L ≤ (blockU c.L).map c.L.subtype := by
    rw [he, extensionCore_eq_overgroup d c hYL hnormal]
    exact commutator_mono hU le_rfl
  have hWL : d.componentModule I c.L ≤ c.L := hW.trans (map_subtype_le _)
  let W := (d.componentModule I c.L).subgroupOf c.L
  have hWb : W ≤ blockU c.L := by
    intro x hx
    obtain ⟨y, hy, heq⟩ := hW hx
    exact (Subtype.ext heq : y = x) ▸ hy
  let : W.Normal := normal_subgroupOf_of_le_normalizer
    (normalizer_commutator_ge_right (d.UI I) c.L)
  rcases hshort.irreducible.2 (W ⊔ (blockU c.L ⊓ center c.L)) inferInstance
      le_sup_right (sup_le hWb inf_le_left) with hcentral | hwhole
  · have hWC : d.componentModule I c.L ≤ centralizer (c.L : Set G) := by
      intro w hw l hl
      have hc : (⟨w, hWL hw⟩ : c.L) ∈ center c.L :=
        ((le_sup_left : W ≤ W ⊔ (blockU c.L ⊓ center c.L)).trans
          (hcentral.le.trans inf_le_right)) hw
      exact congrArg Subtype.val (mem_center_iff.mp hc ⟨l, hl⟩)
    let := component_isPerfect_of_containment d c hYL
    have hbot : d.componentModule I c.L = ⊥ :=
      commutator_eq_bot_of_iterated_eq_bot (d.UI I) c.L
        (commutator_eq_bot_iff_le_centralizer.mpr hWC)
    have hLC : c.L ≤ centralizer (d.UI I : Set G) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hbot)
    have hk : (componentMap d c).ker = ⊤ := by
      apply top_unique
      intro x _
      apply Subtype.ext
      change d.starMap I ⟨x, _⟩ = 1
      exact (QuotientGroup.eq_one_iff _).mpr (hLC x.property)
    have htriv := MonoidHom.ker_eq_top_iff.mp hk
    have hz : d.starImage I c.L = ⊥ := by
      apply le_bot_iff.mp
      intro x hx
      obtain ⟨l, hl⟩ := componentMap_surjective d c ⟨x, hx⟩
      have heq : (⟨x, hx⟩ : d.starImage I c.L) = 1 := by
        rw [← hl, htriv]
        rfl
      exact congrArg Subtype.val heq
    exact (component_star_ne_bot d c hz).elim
  · exact hwhole

/-- Faithfulness on U(L) forces the actual star kernel into O₂(L). -/
theorem componentMap_ker_le_core_of_faithful_block (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hYL : d.Yplus ≤ c.L)
    (hnormal : (c.L.subgroupOf I).Normal) (hU : d.UI I ≤ I.pCoreIn 2)
    (hshort : IsShort c.L) (hfaith : centralizer (blockU c.L : Set c.L) = pCore 2 c.L) :
    (componentMap d c).ker ≤ pCore 2 c.L := by
  rw [← hfaith]
  have hgen := componentModule_sup_blockFixed d c hYL hnormal hU hshort
  have hWUI : d.componentModule I c.L ≤ d.UI I :=
    le_normalizer_iff_commutator_le_left.mp
      ((component_le c).trans (le_normalizer_conjugateSpanBy d.Z I))
  intro x hx
  have hxUI : (x : G) ∈ centralizer (d.UI I : Set G) := by
    have heq : d.starMap I ⟨x, component_le c x.property⟩ = 1 :=
      congrArg Subtype.val (show componentMap d c x = 1 from hx)
    change (⟨(x : G), component_le c x.property⟩ : I) ∈ localActionKernel d.Z I
    exact (QuotientGroup.eq_one_iff _).mp heq
  have hW : (d.componentModule I c.L).subgroupOf c.L ≤
      centralizer ({x} : Set c.L) := by
    intro w hw z hz
    have hzx : z = x := Set.mem_singleton_iff.mp hz
    subst z
    exact Subtype.ext (hxUI w (hWUI hw)).symm
  have hfixed : blockU c.L ⊓ center c.L ≤ centralizer ({x} : Set c.L) := by
    intro w hw z hz
    exact mem_center_iff.mp hw.2 z
  have hblock : blockU c.L ≤ centralizer ({x} : Set c.L) :=
    hgen ▸ sup_le hW hfixed
  intro u hu
  exact (hblock hu x (Set.mem_singleton x)).symm

/-- The core quotient identifies with the actual star image, by the
faithful block action rather than an assumed simple quotient. -/
noncomputable def faithfulBlockCoreEquivStar (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hYL : d.Yplus ≤ c.L)
    (hnormal : (c.L.subgroupOf I).Normal)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hU : d.UI I ≤ I.pCoreIn 2) (hshort : IsShort c.L)
    (hfaith : centralizer (blockU c.L : Set c.L) = pCore 2 c.L) :
    (c.L ⧸ pCore 2 c.L) ≃* d.starImage I c.L := by
  have hk : (componentMap d c).ker = pCore 2 c.L :=
    le_antisymm (componentMap_ker_le_core_of_faithful_block d c hYL hnormal hU hshort hfaith)
      (core_le_componentMap_ker d c (component_core_centralizes_span d c hnormal P hP))
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (componentMap d c)
      (componentMap_surjective d c))

/-- The faithful block comparison preserves the original action quotient map. -/
theorem faithfulBlockCoreEquivStar_apply (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hYL : d.Yplus ≤ c.L)
    (hnormal : (c.L.subgroupOf I).Normal)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hU : d.UI I ≤ I.pCoreIn 2) (hshort : IsShort c.L)
    (hfaith : centralizer (blockU c.L : Set c.L) = pCore 2 c.L) (l : c.L) :
    faithfulBlockCoreEquivStar d c hYL hnormal P hP hU hshort hfaith
      (QuotientGroup.mk' (pCore 2 c.L) l) = componentMap d c l := by
  rfl

/-- Transfer an A-hat₆ block through the actual star action and use the
precise triple-cover exclusion for L* in 15.3.27(3). -/
theorem not_exceptionalAhat6Block [Finite G]
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hf : HasCharacteristicTwo I) (hYL : d.Yplus ≤ c.L)
    (hnormal : (c.L.subgroupOf I).Normal)
    (hS : Chapter1.IsSylowIn 2 d.S I)
    (h27 : ¬ Parabolics.IsTripleCoverAlternatingSix (d.starImage I c.L)) :
    ¬ IsExceptionalAhat6Block c.L := by
  intro h
  obtain ⟨P, hP⟩ := hS
  let e := faithfulBlockCoreEquivStar d c hYL hnormal P hP
    (local_span_le_core d hf ⟨P, hP⟩) h.1 h.centralizer
  apply h27
  refine ⟨c.star_quasisimple, ?_, ?_⟩
  · exact (Nat.card_congr (centerCongr e).symm.toEquiv).trans h.2.2.1
  · obtain ⟨q⟩ := h.2.2.2.1
    have hc : (center (c.L ⧸ pCore 2 c.L)).map e.toMonoidHom =
        center (d.starImage I c.L) := by
      apply le_antisymm
      · rintro _ ⟨x, hx, rfl⟩
        exact (centerCongr e ⟨x, hx⟩).property
      · intro x hx
        exact ⟨e.symm x, (centerCongr e).symm ⟨x, hx⟩ |>.property,
          e.apply_symm_apply x⟩
    exact ⟨(QuotientGroup.congr _ _ e hc).symm.trans q⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

end
