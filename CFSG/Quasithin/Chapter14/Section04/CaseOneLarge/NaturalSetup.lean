module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.CoreGeometry
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Structure

/-!
# G.2.5 on the original nonabelian flag

Retain the source transporter g in N_L(V₂) outside H. Its moved point and
V₁ span V₂; transitivity on the points of V supplies a third point outside
that plane. The original natural marking identifies the literal star image
with SL₃(2). Nonabelianness of the H-closure makes its star image nontrivial.
Thus G.2.5 applies to these three actual marked conjugates. Its two earlier
inputs follow from original Sylow containment and the Frattini calculation.

Source: Aschbacher--Smith, 12.8.8(4), G.2.5 and 14.4.7,
printed pp.852,335--336,1009; refs/quasithin.pdf.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.NaturalSetup
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
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

private theorem star_kernel (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) :
    (ChapterG.Section02.LinearThree.starProjection (sourceSetup F L)).ker = pCore 2 L := by
  let H := higherRankHypothesis d earlier hq chosen
  ext l
  rw [MonoidHom.mem_ker, Subtype.ext_iff]
  change QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))
    ⟨l, mem_sup_left l.property⟩ = 1 ↔ l ∈ pCore 2 L
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have heLT (x : (L ⊔ (T : Subgroup G) : Subgroup G)) :
      x ∈ pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G) ↔ (x : G) ∈ centralizer (V : Set G) := by
    constructor
    · intro hx
      exact chosen.core_centralizes (mem_map_of_mem _ hx)
    · intro hx
      have hm := H.centralizer_LT structural ▸ (show (x : G) ∈
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

private noncomputable def starModel (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) :
    (sourceSetup F L).star L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) := by
  let π := ChapterG.Section02.LinearThree.starProjection (sourceSetup F L)
  let H := higherRankHypothesis d earlier hq chosen
  let := chosen.elementary
  exact (QuotientGroup.quotientKerEquivOfSurjective π
    (ChapterG.Section02.LinearThree.starProjection_surjective _)).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq (G := L) (star_kernel d earlier hq chosen structural F)).trans
        (H.naturalMarking.quotientEquiv.trans (BinaryLinear.OuterCyclic.slEquivLinear 3).symm))

private theorem starModel_apply (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (l : L) :
    let := chosen.elementary
    BinaryLinear.OuterCyclic.slEquivLinear 3
      (starModel d earlier hq chosen structural F
        (ChapterG.Section02.LinearThree.starProjection (sourceSetup F L) l)) =
      (higherRankHypothesis d earlier hq chosen).naturalMarking.quotientEquiv
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
theorem source_frame (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (F : InvariantFlag T V 3) (g : G)
    (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ l : G, l ∈ L ∧ l ∉ F.Li L 2 ⊔ (T : Subgroup G) ∧
      Disjoint (F.Vi 1) (conjugate (F.Vi 1) g) ∧
      F.Vi 1 ⊔ conjugate (F.Vi 1) g = F.Vi 2 ∧
      Disjoint (F.Vi 2) (conjugate (F.Vi 1) l) ∧
      F.Vi 2 ⊔ conjugate (F.Vi 1) l = V := by
  let := chosen.elementary
  let H := higherRankHypothesis d earlier hq chosen
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
      (F.P_le_G₂ (by decide) L chosen.normalizes hgP)
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

theorem source_almostSpecial (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ l : G, l ∈ L ∧ l ∉ F.Li L 2 ⊔ (T : Subgroup G) ∧
      F.Vi 1 ⊔ conjugate (F.Vi 1) g = F.Vi 2 ∧
      Nonempty (ChapterG.Section02.LinearThree.Hypothesis
        (sourceSetup F L) (ZMod 2) 1 g l) := by
  let := chosen.elementary
  let H := higherRankHypothesis d earlier hq chosen
  let D := sourceSetup F L
  let A := H.naturalMarking
  obtain ⟨h, hh, hhP, hdis, hplane, hdis', hspan⟩ := source_frame d earlier hq chosen F g hgP hgH
  rw [← hplane] at hdis' hspan
  have hpointspan : conjugateSpanBy (F.Vi 1) L = V := by
    apply le_antisymm (conjugateSpanBy_le (F.le_seed 1) chosen.normalizes)
    apply hspan.symm.le.trans
    apply sup_le (sup_le (le_conjugateSpanBy _ _) ?_) ?_
    · exact conjugate_le_of_normalizes (le_conjugateSpanBy _ _) g
        (le_normalizer_conjugateSpanBy _ _ hg)
    · exact conjugate_le_of_normalizes (le_conjugateSpanBy _ _) h
        (le_normalizer_conjugateSpanBy _ _ hh)
  have hUT := source_closure_le_sylow d earlier hq chosen structural alternatives F
  have hUstar : D.star D.U ≠ ⊥ := by
    intro hz
    have hUC : F.U ≤ centralizer (V : Set G) := by
      intro x hx
      have hm : QuotientGroup.mk' (pCore 2 D.LT) ⟨x, mem_sup_right (hUT hx)⟩ ∈ D.star D.U :=
        mem_map_of_mem _ hx
      have hm1 := mem_bot.mp (hz ▸ hm)
      have hcore := (QuotientGroup.eq_one_iff _).mp hm1
      exact chosen.core_centralizes (mem_map_of_mem D.LT.subtype hcore)
    have hVZ : V ≤ F.ZU := by
      rw [ZU, centerIn_eq_inf_centralizer]
      exact le_inf (le_conjugateSpanBy V F.H) (le_centralizer_iff.mp hUC)
    exact hne (le_centralizer_iff_isMulCommutative.mp
      ((conjugateSpanBy_le hVZ F.H_normalizes_ZU).trans (centerIn_le_centralizer F.U)))
  refine ⟨h, hh, hhP, hplane, ⟨{
    setup := F.localKernel_hypothesis d.qtke L (normalizer (L : Set G)) F.H
      (by decide) chosen.le_sylow chosen.normalizes (H.sylow_normalizes structural)
      H.residual (fun _ => ⟨A⟩) (H.point_mem_Hz F alternatives)
    exponent_pos := by decide
    field_card := by norm_num
    span_eq := hpointspan
    model := starModel d earlier hq chosen structural F
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
      (starModel_apply d earlier hq chosen structural F l)
  exact (A.equivariant l (Additive.ofMul v)).trans he.symm


end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.NaturalSetup
