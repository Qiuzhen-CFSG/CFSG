module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.Preparation
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Structure
public import Theory.GroupTheory.FixedPointFreeCyclicJoin
public import Theory.GroupTheory.PCoreImage
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Fundamental

/-!
# The actual order-32 closure inside the natural L₃(2) block

The original natural marking supplies the full G.2.5 hypothesis, including
its literal star quotient and three independent conjugate points. G.2.5(3)
expresses O₂(LU) as the product of three conjugates of U ∩ O₂(LU). Each
intersection is V: the two-core centralizes V, and C_U(V)=V. Consequently
O₂(LU)=V, and relative normality gives O₂(L)=V. Equality of the actual
starred images then places U inside L.

No normalizer-product, nonsplitting, or quotient recognition conclusion is
assumed. The later 14.4.4–5 arguments and the full SourceLocalData constructor
remain with qt-d-14414-g2-source. This module supplies the block-core step
needed by that constructor and its configuration consumer.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
14.4.4(4), printed p.1007, using G.2.5(1–3), printed pp.335–336.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour
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

private theorem source_frame (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (F : InvariantFlag T V 3) :
    ∃ g h : G, g ∈ L ∧ h ∈ L ∧
      Disjoint (F.Vi 1) (conjugate (F.Vi 1) g) ∧
      Disjoint (F.Vi 1 ⊔ conjugate (F.Vi 1) g) (conjugate (F.Vi 1) h) ∧
      (F.Vi 1 ⊔ conjugate (F.Vi 1) g) ⊔ conjugate (F.Vi 1) h = V := by
  let := chosen.elementary
  let H := higherRankHypothesis d earlier hq chosen
  have hc : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  have hv : Nat.card V = 8 := by simpa [F.last] using F.card 3 (by decide)
  obtain ⟨B, hBV, hB, hdB, hcB⟩ := complementary_point (F.Vi 1) (F.le_seed 1)
    (by rw [hc, hv]; decide)
  obtain ⟨C, hCV, hC, hdC, hcC⟩ := complementary_point (F.Vi 1 ⊔ B)
    (sup_le (F.le_seed 1) hBV) (by rw [hcB, hc, hv]; decide)
  obtain ⟨g, hg, heg⟩ := H.subspace_transitive (F.Vi 1) B (F.le_seed 1) hBV (hc.trans hB.symm)
  obtain ⟨h, hh, heh⟩ := H.subspace_transitive (F.Vi 1) C (F.le_seed 1) hCV (hc.trans hC.symm)
  refine ⟨g, h, hg, hh, heg.symm ▸ hdB, ?_, ?_⟩
  · rwa [heg, heh]
  · rw [heg, heh]
    exact eq_of_le_of_card_ge (sup_le (sup_le (F.le_seed 1) hBV) hCV)
      (by rw [hcC, hcB, hc, hv])

private abbrev almostSpecialSetup (F : InvariantFlag T V 3) (L : Subgroup G) :
    ChapterG.Section02.Setup G :=
  { V := V, V₁ := F.Vi 1, L := L, T := T, H := F.H }

private theorem star_kernel (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) :
    (ChapterG.Section02.LinearThree.starProjection (almostSpecialSetup F L)).ker = pCore 2 L := by
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
    (almostSpecialSetup F L).star L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) := by
  let π := ChapterG.Section02.LinearThree.starProjection (almostSpecialSetup F L)
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
        (ChapterG.Section02.LinearThree.starProjection (almostSpecialSetup F L) l)) =
      (higherRankHypothesis d earlier hq chosen).naturalMarking.quotientEquiv
        (QuotientGroup.mk' (pCore 2 L) l) := by
  let π := ChapterG.Section02.LinearThree.starProjection (almostSpecialSetup F L)
  let e := QuotientGroup.quotientKerEquivOfSurjective π
    (ChapterG.Section02.LinearThree.starProjection_surjective _)
  have he : e (QuotientGroup.mk' π.ker l) = π l := rfl
  have he' : e.symm (π l) = QuotientGroup.mk' π.ker l := e.symm_apply_eq.mpr he.symm
  dsimp only [starModel, MulEquiv.trans_apply]
  rw [he', QuotientGroup.mk'_apply, QuotientGroup.quotientMulEquivOfEq_mk, MulEquiv.apply_symm_apply]
  rfl

private theorem source_almostSpecial (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32) :
    ∃ g h : G, Nonempty (ChapterG.Section02.LinearThree.Hypothesis
      (almostSpecialSetup F L) (ZMod 2) 1 g h) := by
  let := chosen.elementary
  let H := higherRankHypothesis d earlier hq chosen
  let D := almostSpecialSetup F L
  let A := H.naturalMarking
  obtain ⟨g, h, hg, hh, hdis, hdis', hspan⟩ := source_frame d earlier hq chosen F
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
    have hUV : F.U ≤ V := by
      intro x hx
      apply (source_seed_centralizer d earlier hq chosen structural alternatives F hne hZ hcard).le
      refine ⟨hx, ?_⟩
      have hm : QuotientGroup.mk' (pCore 2 D.LT) ⟨x, mem_sup_right (hUT hx)⟩ ∈ D.star D.U :=
        mem_map_of_mem _ hx
      have hm1 := mem_bot.mp (hz ▸ hm)
      have hcore := (QuotientGroup.eq_one_iff _).mp hm1
      exact chosen.core_centralizes (mem_map_of_mem D.LT.subtype hcore)
    have hc := card_le_of_le hUV
    have hv : Nat.card V = 8 := by simpa [F.last] using F.card 3 (by decide)
    rw [hcard, hv] at hc
    omega
  refine ⟨g, h, ⟨{
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

/-- The source block-core conclusions: V=O₂(L), and the original closure lies in L. -/
theorem source_block_core (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32) :
    V = L.pCoreIn 2 ∧ F.U ≤ L := by
  let := chosen.elementary
  let H := higherRankHypothesis d earlier hq chosen
  obtain ⟨g, h, ⟨B⟩⟩ := source_almostSpecial d earlier hq chosen structural alternatives
    F hne hZ hcard
  let D := almostSpecialSetup F L
  have hUT := source_closure_le_sylow d earlier hq chosen structural alternatives F
  have hphi : (frattini D.U).map D.U.subtype ≤ D.V₁ := by
    obtain ⟨_, he, _⟩ := source_closure d earlier hq chosen structural alternatives F hne
    change (frattini F.U).map F.U.subtype ≤ F.Vi 1
    rw [he, map_subgroupOf_eq_of_le (show F.Vi 1 ≤ F.U from
      (F.le_seed 1).trans (le_conjugateSpanBy V F.H))]
  have hS := B.S_eq_star_kernel hUT hphi
  have hW : ChapterG.Section02.LinearThree.W D g h = V := by
    apply le_antisymm
    · change D.U ⊓ ChapterG.Section02.LinearThree.S D g h ≤ V
      rw [hS]
      exact (inf_le_inf_left _ (inf_le_right.trans chosen.core_centralizes)).trans_eq
        (source_seed_centralizer d earlier hq chosen structural alternatives F hne hZ hcard)
    · exact le_inf (le_conjugateSpanBy V F.H) ((B.central_first_of_source hUT hphi).trans inf_le_left)
  have hcore : ChapterG.Section02.LinearThree.S D g h = V := by
    rw [B.S_eq_WProduct hUT hphi]
    change (ChapterG.Section02.LinearThree.W D g h ⊔
      conjugate (ChapterG.Section02.LinearThree.W D g h) g) ⊔
      conjugate (ChapterG.Section02.LinearThree.W D g h) h = V
    rw [hW, (conjugate_eq_iff V g).mpr (chosen.normalizes B.g_mem),
      (conjugate_eq_iff V h).mpr (chosen.normalizes B.h_mem), sup_idem]
    simp only [sup_idem]
  have hLcore : L.pCoreIn 2 ≤ V := by
    rw [← hcore]
    apply pCoreIn_mono_of_normalizes (B.L_le_I hUT hphi)
    rw [B.I_eq_LU hUT hphi]
    exact sup_le L.le_normalizer (hUT.trans (H.sylow_normalizes structural))
  have hIL : ChapterG.Section02.LinearThree.I D g h ≤ L := by
    intro x hx
    let xLT : D.LT := ⟨x, B.I_le_LT hUT hx⟩
    have hm : QuotientGroup.mk' (pCore 2 D.LT) xLT ∈
        D.star (ChapterG.Section02.LinearThree.I D g h) := mem_map_of_mem _ hx
    rw [B.star_I_eq_star_L hUT hphi] at hm
    obtain ⟨l, hl, he⟩ := hm
    have hk : xLT * l⁻¹ ∈ pCore 2 D.LT := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' (pCore 2 D.LT) (xLT * l⁻¹) = 1
      rw [map_mul, map_inv, he, mul_inv_cancel]
    have hv : x * (l : G)⁻¹ ∈ V := by
      apply hcore.le
      rw [hS]
      exact ⟨(ChapterG.Section02.LinearThree.I D g h).mul_mem hx
        ((ChapterG.Section02.LinearThree.I D g h).inv_mem (B.L_le_I hUT hphi hl)),
        mem_map_of_mem D.LT.subtype hk⟩
    have hxL := L.mul_mem (chosen.le_component hv) hl
    change x * (l : G)⁻¹ * (l : G) ∈ L at hxL
    simpa only [inv_mul_cancel_right] using hxL
  exact ⟨le_antisymm chosen.le_componentCore hLcore,
    (show F.U ≤ ChapterG.Section02.LinearThree.I D g h from le_sup_left.trans le_sup_left).trans hIL⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour
