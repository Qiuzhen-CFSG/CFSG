module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup.Intersections
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Structure
public import Theory.GroupTheory.FixedPointFreeCyclicJoin

/-!
# The marked G.2.5 setup for the HS overgroup

The original natural action and the same-ambient structural predecessors
construct the literal star quotient and three independent conjugate points.
This specializes the natural setup used in CaseOneLarge to the HS inputs,
without introducing universal earlier-source hypotheses. The cyclic-center
local structure supplies Sylow containment of the original closure.

Source: Aschbacher--Smith, 12.8.8(4), G.2.5 and 14.3.33,
printed pp.851--852,335--336,1004.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem complementary_point [IsElementaryAbelian 2 V]
    (A : Subgroup G) (hAV : A ≤ V) (hlt : Nat.card A < Nat.card V) :
    ∃ B : Subgroup G, B ≤ V ∧ Nat.card B = 2 ∧ Disjoint A B ∧
      Nat.card (A ⊔ B : Subgroup G) = Nat.card A * 2 := by
  have hn : ¬ V ≤ A := fun hh => (not_lt_of_ge (card_le_of_le hh)) hlt
  obtain ⟨v, hv, hvA⟩ := SetLike.not_le_iff_exists.mp hn
  have hv1 : v ≠ 1 := fun he => hvA (he ▸ A.one_mem)
  have ho : orderOf v = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) v hv) hv1
  have hb : Nat.card (zpowers v) = 2 := (Nat.card_zpowers v).trans ho
  have hd : Disjoint A (zpowers v) := by
    apply disjoint_def.mpr
    intro x hx hxB
    by_contra hx1
    have hvx : v ∈ zpowers x := by
      have he := mem_zpowers_of_prime_card hb
        (show (⟨x, hxB⟩ : zpowers v) ≠ 1 from fun he => hx1 (congrArg Subtype.val he))
        (g' := (⟨v, mem_zpowers v⟩ : zpowers v))
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp he
      exact mem_zpowers_iff.mpr ⟨k, congrArg Subtype.val hk⟩
    exact hvA ((zpowers_le.mpr hx) hvx)
  have hnB : zpowers v ≤ normalizer (A : Set G) := by
    apply zpowers_le.mpr
    apply Subgroup.centralizer_le_normalizer
    intro a ha
    exact congrArg Subtype.val (mul_comm (⟨a, hAV ha⟩ : V) ⟨v, hv⟩)
  refine ⟨zpowers v, zpowers_le.mpr hv, hb, hd, ?_⟩
  rw [card_sup_of_disjoint_of_normalizes A (zpowers v) hd hnB, hb]

abbrev sourceSetup (F : InvariantFlag T V 3) (L : Subgroup G) :
    ChapterG.Section02.Setup G :=
  { V := V, V₁ := F.Vi 1, L := L, T := T, H := F.H }

private theorem star_kernel (H : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) :
    (ChapterG.Section02.LinearThree.starProjection (sourceSetup F L)).ker = pCore 2 L := by
  ext l
  rw [MonoidHom.mem_ker, Subtype.ext_iff]
  change QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))
    ⟨l, mem_sup_left l.property⟩ = 1 ↔ l ∈ pCore 2 L
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have heLT (x : (L ⊔ (T : Subgroup G) : Subgroup G)) :
      x ∈ pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G) ↔ (x : G) ∈ centralizer (V : Set G) := by
    constructor
    · intro hx
      exact H.chosen.core_centralizes (mem_map_of_mem _ hx)
    · intro hx
      have hm := H.centralizer_LT_at structural ▸ (show (x : G) ∈
        (L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G) from ⟨x.property, hx⟩)
      obtain ⟨y, hy, he⟩ := hm
      exact (Subtype.ext he : y = x) ▸ hy
  rw [heLT]
  constructor
  · intro hl
    obtain ⟨y, hy, he⟩ := H.centralizer_L ▸
      (show (l : G) ∈ L ⊓ centralizer (V : Set G) from ⟨l.property, hl⟩)
    exact (Subtype.ext he : y = l) ▸ hy
  · intro hl
    have hm : (l : G) ∈ L.pCoreIn 2 := mem_map_of_mem L.subtype hl
    exact (H.centralizer_L.ge hm).2

private noncomputable def starModel (H : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) :
    (sourceSetup F L).star L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) := by
  let π := ChapterG.Section02.LinearThree.starProjection (sourceSetup F L)
  let := H.chosen.elementary
  exact (QuotientGroup.quotientKerEquivOfSurjective π
    (ChapterG.Section02.LinearThree.starProjection_surjective _)).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq (G := L) (star_kernel H structural F)).trans
        (H.naturalMarking.quotientEquiv.trans (BinaryLinear.OuterCyclic.slEquivLinear 3).symm))

private theorem starModel_apply (H : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (l : L) :
    let := H.chosen.elementary
    BinaryLinear.OuterCyclic.slEquivLinear 3
      (starModel H structural F
        (ChapterG.Section02.LinearThree.starProjection (sourceSetup F L) l)) =
      H.naturalMarking.quotientEquiv
        (QuotientGroup.mk' (pCore 2 L) l) := by
  let π := ChapterG.Section02.LinearThree.starProjection (sourceSetup F L)
  let e := QuotientGroup.quotientKerEquivOfSurjective π
    (ChapterG.Section02.LinearThree.starProjection_surjective _)
  have he : e (QuotientGroup.mk' π.ker l) = π l := rfl
  have he' : e.symm (π l) = QuotientGroup.mk' π.ker l := e.symm_apply_eq.mpr he.symm
  dsimp only [starModel, MulEquiv.trans_apply]
  rw [he', QuotientGroup.mk'_apply, QuotientGroup.quotientMulEquivOfEq_mk, MulEquiv.apply_symm_apply]
  rfl

/-- Complete the two original points to a frame, keeping the prescribed g.
The third transporter lies outside the original plane parabolic L₂T. -/
theorem source_frame (H : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (F : InvariantFlag T V 3) (g : G)
    (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ l : G, l ∈ L ∧ l ∉ F.Li L 2 ⊔ (T : Subgroup G) ∧
      Disjoint (F.Vi 1) (conjugate (F.Vi 1) g) ∧
      F.Vi 1 ⊔ conjugate (F.Vi 1) g = F.Vi 2 ∧
      Disjoint (F.Vi 2) (conjugate (F.Vi 1) l) ∧
      F.Vi 2 ⊔ conjugate (F.Vi 1) l = V := by
  let := H.chosen.elementary
  have hc : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  have hc₂ : Nat.card (F.Vi 2) = 4 := by simpa using F.card 2 (by decide)
  have hv : Nat.card V = 8 := by simpa [F.last] using F.card 3 (by decide)
  have hcG : Nat.card (conjugate (F.Vi 1) g) = 2 := by
    rw [conjugate, card_map_of_injective (MulAut.conj g⁻¹).injective, hc]
  have hneq : F.Vi 1 ≠ conjugate (F.Vi 1) g := by
    intro he
    exact hgH ((conjugate_eq_iff (F.Vi 1) g).mp he.symm)
  have hdis : Disjoint (F.Vi 1) (conjugate (F.Vi 1) g) :=
    disjoint_iff.mpr (inf_eq_bot_of_card_two_of_ne _ _ hc hcG hneq)
  have hg₂ : conjugate (F.Vi 1) g ≤ F.Vi 2 :=
    conjugate_le_of_normalizes (F.monotone (by decide)) g
      (F.P_le_G₂ (by decide) L H.chosen.normalizes hgP)
  have hnorm : conjugate (F.Vi 1) g ≤ normalizer (F.Vi 1 : Set G) := by
    apply (show conjugate (F.Vi 1) g ≤ centralizer (F.Vi 1 : Set G) from ?_).trans
      (Subgroup.centralizer_le_normalizer _)
    intro b hb a ha
    exact congrArg Subtype.val (mul_comm (⟨a, F.le_seed 1 ha⟩ : V)
      ⟨b, F.le_seed 2 (hg₂ hb)⟩)
  have hplane : F.Vi 1 ⊔ conjugate (F.Vi 1) g = F.Vi 2 := by
    apply eq_of_le_of_card_ge (sup_le (F.monotone (by decide)) hg₂)
    rw [card_sup_of_disjoint_of_normalizes _ _ hdis hnorm, hc, hcG, hc₂]
  obtain ⟨C, hCV, hC, hdC, hcC⟩ := complementary_point (F.Vi 2) (F.le_seed 2)
    (by rw [hc₂, hv]; decide)
  obtain ⟨l, hl, he⟩ := H.subspace_transitive (F.Vi 1) C (F.le_seed 1) hCV (hc.trans hC.symm)
  have hspan : F.Vi 2 ⊔ C = V :=
    eq_of_le_of_card_ge (sup_le (F.le_seed 2) hCV) (by rw [hcC, hc₂, hv])
  refine ⟨l, hl, ?_, hdis, hplane, he.symm ▸ hdC, he.symm ▸ hspan⟩
  intro hlP
  have hl₂ : l ∈ normalizer (F.Vi 2 : Set G) :=
    (sup_le ((F.Li_le L 2).trans inf_le_right) (F.invariant 2)) hlP
  have hle : C ≤ F.Vi 2 := he ▸
    conjugate_le_of_normalizes (F.monotone (by decide)) l hl₂
  have hz : C = ⊥ := (inf_eq_right.mpr hle).symm.trans hdC.eq_bot
  rw [hz, Subgroup.card_bot] at hC
  omega

theorem source_almostSpecial (H : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ l : G, l ∈ L ∧ l ∉ F.Li L 2 ⊔ (T : Subgroup G) ∧
      F.Vi 1 ⊔ conjugate (F.Vi 1) g = F.Vi 2 ∧
      Nonempty (ChapterG.Section02.LinearThree.Hypothesis
        (sourceSetup F L) (ZMod 2) 1 g l) := by
  let := H.chosen.elementary
  let D := sourceSetup F L
  let A := H.naturalMarking
  obtain ⟨h, hh, hhP, hdis, hplane, hdis', hspan⟩ := source_frame H F g hgP hgH
  rw [← hplane] at hdis' hspan
  have hpointspan : conjugateSpanBy (F.Vi 1) L = V := by
    apply le_antisymm (conjugateSpanBy_le (F.le_seed 1) H.chosen.normalizes)
    apply hspan.symm.le.trans
    apply sup_le (sup_le (le_conjugateSpanBy _ _) ?_) ?_
    · exact conjugate_le_of_normalizes (le_conjugateSpanBy _ _) g
        (le_normalizer_conjugateSpanBy _ _ hg)
    · exact conjugate_le_of_normalizes (le_conjugateSpanBy _ _) h
        (le_normalizer_conjugateSpanBy _ _ hh)
  have hUT := closure_le_sylow F s
  have hUstar : D.star D.U ≠ ⊥ := by
    intro hz
    have hUC : F.U ≤ centralizer (V : Set G) := by
      intro x hx
      have hm : QuotientGroup.mk' (pCore 2 D.LT) ⟨x, mem_sup_right (hUT hx)⟩ ∈ D.star D.U :=
        mem_map_of_mem _ hx
      have hm1 := mem_bot.mp (hz ▸ hm)
      have hcore := (QuotientGroup.eq_one_iff _).mp hm1
      exact H.chosen.core_centralizes (mem_map_of_mem D.LT.subtype hcore)
    have hVZ : V ≤ F.ZU := by
      rw [ZU, centerIn_eq_inf_centralizer]
      exact le_inf (le_conjugateSpanBy V F.H) (le_centralizer_iff.mp hUC)
    exact hne (le_centralizer_iff_isMulCommutative.mp
      ((conjugateSpanBy_le hVZ F.H_normalizes_ZU).trans (centerIn_le_centralizer F.U)))
  refine ⟨h, hh, hhP, hplane, ⟨{
    setup := F.localKernel_hypothesis H.source.simpleQTKE L (normalizer (L : Set G)) F.H
      (by decide) H.chosen.le_sylow H.chosen.normalizes (H.sylow_normalizes_at structural)
      H.residual (fun _ => ⟨A⟩) (H.point_mem_Hz_at F alternatives)
    exponent_pos := by decide
    field_card := by norm_num
    span_eq := hpointspan
    model := starModel H structural F
    coordinates := A.coordinates.toAddEquiv.toMultiplicativeRight
    equivariant := ?_
    point := F.naturalFlagSpace A.coordinates 1
    point_dimension := F.naturalFlagSpace_finrank A.coordinates 1 (by decide)
    point_mem := fun v => (F.mem_naturalFlagSpace A.coordinates 1 v).symm
    star_U_ne_bot := hUstar
    g_mem := hg
    h_mem := hh
    points_disjoint := hdis
    third_disjoint := hdis'
    points_span := hspan }⟩⟩
  intro l v
  have he := congrArg (fun a : BinaryLinear.OuterCyclic.LinearGroup 3 =>
    a (A.coordinates (Additive.ofMul v)))
      (starModel_apply H structural F l)
  exact (A.equivariant l (Additive.ofMul v)).trans he.symm


/-- The omitted-point transporter can be chosen in the original L itself. -/
theorem exists_source_conjugator
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) : ∃ g : G, g ∈ L ∧ g ∈ F.P L ∧ g ∉ F.H := by
  obtain ⟨_, F', huniq, z, hz, he, g, hgP, hgH⟩ := h.exists_flag_geometry_at structural
  have hcuts (i : ℕ) : F.Vi i = F'.Vi i := by
    by_cases hi : i ≤ 3
    · exact huniq i hi (F.Vi i) (F.le_seed i) (F.card i hi) (F.invariant i)
    · have hf : F.Vi i = V := le_antisymm (F.le_seed i)
        ((le_of_eq F.last.symm).trans (F.monotone (by omega : 3 ≤ i)))
      have hf' : F'.Vi i = V := le_antisymm (F'.le_seed i)
        ((le_of_eq F'.last.symm).trans (F'.monotone (by omega : 3 ≤ i)))
      exact hf.trans hf'.symm
  have hH : F.H = F'.H := by simp only [H, Gi, hcuts]
  have hP : F.P L = F'.P L := by simp only [P, Gi, hcuts]
  rw [← hP] at hgP
  rw [← hH] at hgH
  have hTP : (T : Subgroup G) ≤ F.P L := by
    refine le_inf le_sup_right (le_iInf fun i => le_iInf fun _ => F.invariant i)
  have hprod : g ∈ (L : Set G) * ((T : Subgroup G) : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left L (T : Subgroup G)
      (h.sylow_normalizes_at structural)]
    exact hgP.1
  obtain ⟨l, hl, t, ht, rfl⟩ := hprod
  refine ⟨l, hl, ?_, ?_⟩
  · have hh := (F.P L).mul_mem hgP ((F.P L).inv_mem (hTP ht))
    simpa only [mul_inv_cancel_right] using hh
  · intro hlH
    exact hgH (F.H.mul_mem hlH (F.invariant 1 ht))

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup
