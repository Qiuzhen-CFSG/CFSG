module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.LinearTwo.Setup
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Action
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.FourGroup
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.GroupTheory.SylowNormalSupplementIntersection

/-!
# The actual invariant plane for the L₂ block exclusion

Relative component normality and perfectness identify [O₂(I),L] with
U(L). The full Y₊-action then puts V₂ inside U(L). The elementary
four-group fixed-point lemma proves that V₂ meets C_U(L) trivially.
Consequently every equivariant block model carries an invariant subgroup
of order four, with the actor explicitly the image of M ∩ L.

The Sylow helper isolates the remaining Borel calculation: if Y₊ normalizes
L ∩ S, that intersection lies in R = O₂(Y₊S), and Sylow restriction to LR
gives exactly R. This helper does not assume that LR is a minimal parabolic.

The A₅ module obstruction, the pushing-up application, and the L₂
block automorphism calculation are still required for 15.3.30. None is
asserted by these reductions.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.30, printed pp.1131–1132 (PDF pp.1148–1149).
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo
variable {G : Type*} [Group G]
/-- The first coordinate plane lies in the common Sylow subgroup. -/
theorem plane_one_le_sylow [Finite G] (d : LocalData G) : d.V₁ ≤ d.S :=
  (d.action.plane_le 1).trans
    (d.action.le_planeStabilizer d.T d.sylow_le (localModule_le d.T d.sylow_le) 1)

/-- The second coordinate plane also lies in the common Sylow subgroup. -/
theorem plane_two_le_sylow [Finite G] (d : LocalData G) : d.V₂ ≤ d.S :=
  (d.action.plane_le _).trans
    (d.action.le_planeStabilizer d.T d.sylow_le (localModule_le d.T d.sylow_le) 1)

/-- The elementary normal span U_I lies in the intrinsic two-core of I. -/
theorem span_le_core [Finite G] (d : LocalData G) {I : Subgroup G}
    (hSI : d.S ≤ I) (hUI : IsElementaryAbelian 2 (d.UI I)) : d.UI I ≤ I.pCoreIn 2 := by
  let := hUI
  have hVS : d.V ≤ d.S :=
    d.action.le_planeStabilizer d.T d.sylow_le (localModule_le d.T d.sylow_le) 1
  have hZI : d.Z ≤ I := ((le_conjugateSpanBy d.Z d.M).trans hVS).trans hSI
  exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 (d.UI I))
    (conjugateSpanBy_le_self hZI) (le_normalizer_conjugateSpanBy d.Z I)

private theorem normalizes_commutator {A B N : Subgroup G}
    (hA : N ≤ normalizer (A : Set G)) (hB : N ≤ normalizer (B : Set G)) :
    N ≤ normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  apply le_normalizer_iff.mpr
  intro n hn x hx
  have hmap : (⁅A, B⁆).map (MulAut.conj n).toMonoidHom ≤ ⁅A, B⁆ := by
    rw [map_commutator]
    apply commutator_mono
    · rintro _ ⟨a, ha, rfl⟩
      exact (hA hn a).mp ha
    · rintro _ ⟨b, hb, rfl⟩
      exact (hB hn b).mp hb
  exact hmap (mem_map_of_mem _ hx)

/-- The actual M_I-action preserves V₂ = [V,Y₊]. -/
theorem Earlier.plane_normalized (d : LocalData G) {I : Subgroup G}
    {c : ComponentWitness d I} (h : Earlier d I c) :
    d.MI I ≤ normalizer (d.V₂ : Set G) := by
  rw [← h.plane_eq]
  exact normalizes_commutator (inf_le_left.trans d.action.normalizes)
    (h.normalizer_eq.ge.trans inf_le_right)

/-- Perfectness and relative normality place V₂ in U(L) = [O₂(L),L]. -/
theorem Earlier.plane_le_blockU [Finite G] (d : LocalData G) {I : Subgroup G}
    {c : ComponentWitness d I} (h : Earlier d I c) (hSI : d.S ≤ I) :
    d.V₂ ≤ (ChapterC.blockU c.L).map c.L.subtype := by
  have hU := span_le_core d hSI h.span_elementary
  have he : (ChapterC.blockU c.L).map c.L.subtype = extensionCore c.L := by
    rw [ChapterC.blockU, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
    rfl
  rw [he, extensionCore_eq_overgroup d c h.contains h.component_normal, ← h.plane_full]
  exact commutator_mono (h.plane_le_span.trans hU) h.contains

/-- The full action of the order-three-generated group on the four-group
leaves no nonidentity fixed element. -/
theorem Earlier.plane_centralizer_eq_bot [Finite G] (d : LocalData G) {I : Subgroup G}
    {c : ComponentWitness d I} (h : Earlier d I c) :
    d.V₂ ⊓ centralizer (d.Yplus : Set G) = ⊥ := by
  let : IsElementaryAbelian 2 d.V₂ := d.action.elementary_of_le (d.action.plane_le _)
  have hc : Nat.card d.V₂ = 4 := d.action.card_plane _
  let : Nontrivial d.V₂ := Finite.one_lt_card_iff_nontrivial.mp (by rw [hc]; decide)
  let : IsKleinFour d.V₂ := ⟨hc, IsElementaryAbelian.exponent_eq_prime⟩
  have hgen : theta d.Yplus = d.Yplus := by rw [← h.theta_eq, theta_idempotent]
  have hYM : d.Yplus ≤ d.MI I := h.theta_eq ▸ theta_le (d.MI I)
  exact Section03.RankOne.fourGroup_centralizer_eq_bot hgen
    (hYM.trans (h.plane_normalized d)) h.plane_full

/-- The actual four-group restricted to the intrinsic commutator layer of L. -/
def planeInBlock (d : LocalData G) (L : Subgroup G) : Subgroup (ChapterC.blockU L) :=
  (d.V₂.subgroupOf L).subgroupOf (ChapterC.blockU L)

/-- The intrinsic plane maps back to the original V₂ in G. -/
theorem Earlier.planeInBlock_image [Finite G] (d : LocalData G) {I : Subgroup G}
    {c : ComponentWitness d I} (h : Earlier d I c) (hSI : d.S ≤ I) :
    ((planeInBlock d c.L).map (ChapterC.blockU c.L).subtype).map c.L.subtype = d.V₂ := by
  have hV := h.plane_le_blockU d hSI
  have hVL : d.V₂ ≤ c.L := hV.trans (map_subtype_le _)
  have hVU : d.V₂.subgroupOf c.L ≤ ChapterC.blockU c.L := by
    intro v hv
    obtain ⟨u, hu, he⟩ := hV hv
    have huv : u = v := Subtype.ext he
    exact huv ▸ hu
  rw [planeInBlock, map_subgroupOf_eq_of_le hVU, map_subgroupOf_eq_of_le hVL]

/-- Restriction to the intrinsic block layer preserves the four elements. -/
theorem Earlier.planeInBlock_card [Finite G] (d : LocalData G) {I : Subgroup G}
    {c : ComponentWitness d I} (h : Earlier d I c) (hSI : d.S ≤ I) :
    Nat.card (planeInBlock d c.L) = 4 := by
  have hi := congrArg (fun X : Subgroup G => Nat.card X) (h.planeInBlock_image d hSI)
  rw [card_map_of_injective c.L.subtype_injective,
    card_map_of_injective (ChapterC.blockU c.L).subtype_injective] at hi
  exact hi.trans (d.action.card_plane _)

/-- The quotient by C_U(L) is faithful on V₂ because Y₊ ≤ L and
C_{V₂}(Y₊) = 1. -/
theorem Earlier.planeInBlock_quotient_injective [Finite G] (d : LocalData G)
    {I : Subgroup G} {c : ComponentWitness d I} (h : Earlier d I c) :
    Function.Injective ((QuotientGroup.mk' (ChapterC.blockFixed c.L)).comp
      (planeInBlock d c.L).subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro v hv
  have hvfix : (v : ChapterC.blockU c.L) ∈ ChapterC.blockFixed c.L :=
    (QuotientGroup.eq_one_iff _).mp hv
  have hvcent : ((v : ChapterC.blockU c.L) : c.L) ∈ center c.L := hvfix
  have hx : (((v : ChapterC.blockU c.L) : c.L) : G) ∈
      d.V₂ ⊓ centralizer (d.Yplus : Set G) := by
    refine ⟨v.property, ?_⟩
    intro y hy
    exact congrArg c.L.subtype ((mem_center_iff.mp hvcent) ⟨y, h.contains hy⟩)
  rw [h.plane_centralizer_eq_bot d] at hx
  exact Subtype.ext (Subtype.ext (Subtype.ext hx))

/-- The plane remains a four-group in the genuine module quotient. -/
theorem Earlier.planeInBlock_module_card [Finite G] (d : LocalData G)
    {I : Subgroup G} {c : ComponentWitness d I} (h : Earlier d I c) (hSI : d.S ≤ I) :
    Nat.card ((planeInBlock d c.L).map (QuotientGroup.mk' (ChapterC.blockFixed c.L))) = 4 := by
  have hrange : ((QuotientGroup.mk' (ChapterC.blockFixed c.L)).comp
      (planeInBlock d c.L).subtype).range =
      (planeInBlock d c.L).map (QuotientGroup.mk' (ChapterC.blockFixed c.L)) := by
    rw [MonoidHom.range_comp, range_subtype]
  rw [← hrange, Nat.card_congr (MonoidHom.ofInjective
    (h.planeInBlock_quotient_injective d)).toEquiv.symm]
  exact h.planeInBlock_card d hSI

/-- M ∩ L preserves the intrinsic plane by its literal conjugation action. -/
theorem Earlier.planeInBlock_invariant (d : LocalData G) {I : Subgroup G}
    {c : ComponentWitness d I} (h : Earlier d I c) :
    ∀ l ∈ d.M.subgroupOf c.L, ∀ u ∈ planeInBlock d c.L,
      ChapterC.blockConjugate c.L l u ∈ planeInBlock d c.L := by
  intro l hl u hu
  have hlMI : (l : G) ∈ d.MI I := ⟨hl, component_le c l.property⟩
  exact ((h.plane_normalized d) hlMI _).mp hu


/-- Transport the actual plane through an equivariant block model. -/
theorem Earlier.blockModel_plane [Finite G] (d : LocalData G) {I : Subgroup G}
    {c : ComponentWitness d I} (h : Earlier d I c) (hSI : d.S ≤ I)
    {A W : Type*} [Group A] [Group W] {rho : A →* MulAut W}
    (model : ChapterC.BlockModuleModel c.L rho) :
    ∃ P : Subgroup W, Nat.card P = 4 ∧
      ∀ a ∈ (d.M.subgroupOf c.L).map
        (model.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 c.L))),
        ∀ v ∈ P, rho a v ∈ P := by
  let Q := (planeInBlock d c.L).map (QuotientGroup.mk' (ChapterC.blockFixed c.L))
  refine ⟨Q.map model.moduleIso.toMonoidHom, ?_, ?_⟩
  · rw [card_map_of_injective model.moduleIso.injective]
    exact h.planeInBlock_module_card d hSI
  · rintro a ⟨l, hl, rfl⟩ v ⟨q, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨QuotientGroup.mk' (ChapterC.blockFixed c.L)
      (ChapterC.blockConjugate c.L l u),
      ⟨ChapterC.blockConjugate c.L l u, h.planeInBlock_invariant d l hl u hu, rfl⟩, ?_⟩
    exact model.intertwining l u

/-- The Sylow calculation for LR, after the Borel calculation proves
that Y normalizes L intersect S. R is the two-core, never the residual. -/
theorem sylow_core_join_of_normalizes_intersection [Finite G]
    (S : Sylow 2 G) (L Y : Subgroup G) [L.Normal]
    (hgen : L ⊔ (S : Subgroup G) = ⊤)
    (hY : Y ≤ normalizer ((L ⊓ (S : Subgroup G) : Subgroup G) : Set G)) :
    ∃ P : Sylow 2 ↥(L ⊔ (Y ⊔ (S : Subgroup G)).pCoreIn 2),
      (P : Subgroup _).map (L ⊔ (Y ⊔ (S : Subgroup G)).pCoreIn 2).subtype =
        (Y ⊔ (S : Subgroup G)).pCoreIn 2 := by
  let R := (Y ⊔ (S : Subgroup G)).pCoreIn 2
  have hRS : R ≤ (S : Subgroup G) := by
    have hr := pCoreIn_le_sylow (Y ⊔ (S : Subgroup G)) (S.subtype le_sup_right)
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using hr
  have hLSR : L ⊓ (S : Subgroup G) ≤ R := by
    apply le_pCoreIn_of_normalizes (S.isPGroup'.to_le inf_le_right)
      (inf_le_right.trans le_sup_right)
    apply sup_le hY
    exact (le_inf le_normalizer_of_normal (S : Subgroup G).le_normalizer).trans
      inf_normalizer_le_normalizer_inf
  have hint : (S : Subgroup G) ⊓ (L ⊔ R) = R := by
    apply le_antisymm ?_ (le_inf hRS le_sup_right)
    rintro x ⟨hxS, hxLR⟩
    obtain ⟨l, hl, r, hr, he⟩ := mem_sup_of_normal_left.mp hxLR
    have hlS : l ∈ (S : Subgroup G) := by
      have hz := (S : Subgroup G).mul_mem hxS ((S : Subgroup G).inv_mem (hRS hr))
      simpa only [← he, mul_inv_cancel_right] using hz
    rw [← he]
    exact R.mul_mem (hLSR ⟨hl, hlS⟩) hr
  obtain ⟨P, hP⟩ := S.exists_map_eq_inf_of_normal_supplement L (L ⊔ R) hgen le_sup_left
  exact ⟨P, hP.trans hint⟩
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo

end
