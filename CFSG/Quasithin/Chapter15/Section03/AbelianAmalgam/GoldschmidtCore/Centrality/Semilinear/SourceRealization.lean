module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.SourceModule
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.DoubledAction
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.AmbientTransport
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.AmbientPair

/-!
# The actual bad-character module in the ambient group

The constructed faithful action and full conditional source comparison identify
W=C_U(Q) with the marked natural binary three-space. Source 15.3.46 then
forces ⟨F^{X_E}⟩=W. The cubic splitting is equivariant for the actual
character kernel, so U is two compatible natural summands. Commutation of
X_E with that cubic operator gives ⟨V^{X_E}⟩=U, and the genuine local
product identifies this subgroup with V_E.

The earlier source placement V_E≤V_Mc and abelianness of V_Mc give the
commuting conjugate Uˢ≤C_G(V). The literal Y-product and the two cosets
of T_E in T make UUˢ a nontrivial elementary subgroup normalized by M.
All intermediate action, generation and ambient identities are proved here;
the hypotheses retain the complete permitted universal F.6.18/B.5.6 inputs
and genuine earlier source conclusions.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.46, 15.3.50, 15.3.66–68 and the terminal argument,
printed pp.1141–1145 and 1152–1155.
-/

@[expose] public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The actual doubled natural module and its ambient source transport. -/
theorem terminal_bad_character_ambient {κ : GroupClass.{u}}
    (hG : IsSimpleQTKE κ G)
    (sourceF : Recognition.FSource.ClassificationInput κ)
    (sourceB : GeneralClassificationInput.{u,u} κ)
    (T : Sylow 2 G) (M Mc Y V E F : Subgroup G) [IsElementaryAbelian 2 V]
    (d : OrthogonalFourBinary.NaturalAction V M)
    (c : TerminalConfiguration T M Y V E F d)
    (hTM : (T : Subgroup G) ≤ M) (hYM : Y ≤ M)
    (hEV : E ≤ V) (hEcard : Nat.card E = 4)
    (hE : ∀ e : E, d.singular ⟨e,hEV e.property⟩)
    (hZE : centralInvolutions T ≤ E) (hZcard : Nat.card (centralInvolutions T) = 2)
    (himage : LocalRelations.actionImage d Y =
      pResidual 2 OrthogonalFourBinary.TerminalLines.IsometryGroup)
    (hYcore : twoCoreAmbient Y = Y ⊓ centralizer (V : Set G))
    (hCT : centralizer (V : Set G) ≤ (T : Subgroup G))
    (h66F : twoCoreAmbient (firstAmalgamGroup Y T E F) =
      firstAmalgamGroup Y T E F ⊓ centralizer (F : Set G))
    (hc : Nat.card (lineY Y E ⧸ localTwoCore (lineY Y E)) = 3)
    (hXM : ¬ lineX E ≤ M)
    (hXJ : lineX E = ⁅lineX E,elementaryAbelianMaxJ (lineT T E)⁆)
    (hY : Y = residualY M Mc)
    (hMproduct : (M : Set G) = (Y : Set G) * (T : Set G))
    (hindex : (lineT T E).relIndex (T : Subgroup G) = 2)
    (hTMc : (T : Subgroup G) ≤ Mc)
    (h46 : ∀ g : G, g ∉ M → ∀ v : V,
      (v : G) ∈ V.map (MulAut.conj g).toMonoidHom → d.singular v)
    (hGEproduct : (lineNormalizer E : Set G) =
      (lineY Y E : Set G) * (lineX E : Set G) * (lineT T E : Set G))
    (hVE : lineV V E ≤ conjugateSpanBy V Mc)
    [IsMulCommutative (conjugateSpanBy V Mc)]
    (hbad : ∃ q : ambientTwoCore (amalgamGroup Y T E F),
      quotientAction _ (lineY Y E) c.normalizes_lineY
        ⟨q.1,pCoreIn_le 2 (amalgamGroup Y T E F) q.2⟩ ≠ 1) :
    let H := amalgamGroup Y T E F
    let B := lineY Y E
    let U := conjugateSpanBy V H
    ∃ hU : IsElementaryAbelian 2 U, letI := hU
      let W := coreFixed H U
      W = conjugateSpanBy (centralInvolutions T) H ∧ Nat.card W = 8 ∧
      W = conjugateSpanBy F (lineX E) ∧
      ∃ m : (H ⧸ pCore 2 H) ≃* Matrix.PSL3Two.SL,
        ((lineT T E).subgroupOf H).map
          (m.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.borelSL ∧
        ((firstAmalgamGroup Y T E F).subgroupOf H).map
          (m.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.lineParabolicSL ∧
        ((secondAmalgamGroup T E).subgroupOf H).map
          (m.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.pointParabolicSL ∧
        ∃ Φ : Additive U ≃ₗ[ZMod 2] (BinaryLinearThree.Vector × BinaryLinearThree.Vector),
          (∀ (h : H), quotientAction H B c.normalizes_lineY h = 1 → ∀ u : Additive U,
            Φ (spanAction H U (le_normalizer_conjugateSpanBy V H) h u) =
              (BinaryLinearThree.W (m (QuotientGroup.mk' _ h)) (Φ u).1,
               BinaryLinearThree.W (m (QuotientGroup.mk' _ h)) (Φ u).2)) ∧
          U = lineV V E ∧ U ≤ conjugateSpanBy V Mc ∧
          ∀ s ∈ (T : Subgroup G), s ∉ lineT T E →
            otherLine U s ≤ conjugateSpanBy V Mc ∧
            otherLine U s ≤ centralizer (V : Set G) ∧
            ⁅otherLine U s,U⁆ = ⊥ ∧
            IsElementaryAbelian 2 (U ⊔ otherLine U s : Subgroup G) ∧
            U ⊔ otherLine U s ≠ ⊥ ∧
            M ≤ normalizer ((U ⊔ otherLine U s : Subgroup G) : Set G) := by
  let H := amalgamGroup Y T E F
  let B := lineY Y E
  let U := conjugateSpanBy V H
  obtain ⟨hU,hWZ,ρ,hfaith,hconj,_hB,_hI,m,hS,h₁,h₂,⟨e⟩,_hOrbit,_b,_hb,_hdouble,_he⟩ :=
    terminal_bad_character_natural hG sourceF sourceB T M Y V E F d c hTM hYM
      hEV hEcard hE hZE hZcard himage hYcore hCT h66F hc hXM hXJ hbad
  let := hU
  let W := coreFixed H U
  have hWcard : Nat.card W = 8 := by
    change Nat.card (Additive W) = 8
    rw [Nat.card_congr e.toLinearEquiv.toEquiv]
    simp [BinaryLinearThree.Vector, Nat.card_eq_fintype_card]
  have hWF : W = conjugateSpanBy F H := hWZ.trans
    (plane_span_eq_seed_span H (lineY Y F) (centralInvolutions T) F
      (le_sup_left.trans le_sup_left) c.seed_le c.seed_span).symm
  have hFW : F ≤ W := hWF ▸ le_conjugateSpanBy F H
  have hXH : lineX E ≤ H := le_sup_left.trans le_sup_right
  have hHU : H ≤ normalizer (U : Set G) := le_normalizer_conjugateSpanBy V H
  have hWX : W = conjugateSpanBy F (lineX E) := (plane_X_span_eq V M E F W (lineX E) d
    hEV c.line_le hEcard c.line_card c.line_ne h46
    ((lineX_le_centralizer E).trans (centralizer_le_normalizer (E : Set G))) hXM
    hFW (hXH.trans (coreFixed_normalized H U hHU)) hWcard).symm
  have hZ : centralInvolutions T ≠ ⊥ := by
    intro he
    rw [he] at hZcard
    norm_num at hZcard
  obtain ⟨h0Q,h0U,hlocal,hN⟩ := terminal_kernel_reduction T M Y V E F d c
    hYM hEV hEcard hE hZE hZ himage hYcore hCT h66F
  have hBV : B ≤ normalizer (V : Set G) :=
    (lineY_le Y E).trans (inf_le_left.trans (hYM.trans d.normalizes))
  have hVc : V = ⁅V,B⁆ := Orthogonal.lineY_commutator d Y E hYM hEV hEcard hE himage
  have hBU := external_normalizes_span H B V c.normalizes_lineY hBV
  have hgen := external_span_eq_commutator H B V c.normalizes_lineY hBV hVc
  have h0V : ambientTwoCore B ≤ centralizer (V : Set G) :=
    (Orthogonal.lineY_twoCore d Y E hYM hEV himage hYcore).le.trans inf_le_right
  obtain ⟨z,hz⟩ := ne_bot_iff_exists_ne_one.mp hZ
  obtain ⟨b,hb,hV,hdis⟩ := exists_lineY_complementary_conjugate V M Y E F d hYM hEV
    c.line_le hEcard c.line_card hE c.line_singular (Ne.symm c.line_ne)
    ⟨z,(fun he => hz (Subtype.ext he)),hZE z.property,c.seed_le z.property⟩ himage
  have hb0 : (⟨b,hb⟩ : B) ∉ localTwoCore B := by
    intro he
    have hbf : b ∈ centralizer (F : Set G) := centralizer_le c.line_le (h0V he)
    have hFbot : F = ⊥ := bot_unique (by
      intro f hf
      apply hdis.le_bot
      refine ⟨hf,mem_map.mpr ⟨f,hf,?_⟩⟩
      change b * f * b⁻¹ = f
      rw [← hbf f hf,mul_inv_cancel_right])
    have hh := c.line_card
    rw [hFbot] at hh
    norm_num at hh
  obtain ⟨q,hqχ⟩ := hbad
  let qH : H := ⟨q.1,pCoreIn_le 2 H q.2⟩
  let P := coreFixedPairEquiv H B U c.normalizes_lineY hHU hBU h0U hN hc hgen qH q.2 hqχ ⟨b,hb⟩ hb0
  obtain ⟨Φ,hΦ⟩ := doubled_natural_of_cubic_pair H B U W c.normalizes_lineY hHU hBU h0U
    inf_le_left (QuotientGroup.mk' (pCore 2 H)) ρ hconj ⟨b,hb⟩ P
    (coreFixedPairEquiv_apply H B U c.normalizes_lineY hHU hBU h0U hN hc hgen qH q.2 hqχ ⟨b,hb⟩ hb0)
    m e
  have hdouble : U = W ⊔ W.map (MulAut.conj b).toMonoidHom := by
    rw [hWF]
    exact span_eq_cubicPair H B V F U c.normalizes_lineY hBU h0U hc hgen rfl ⟨b,hb⟩ hb0 hV
  have hXV : conjugateSpanBy V (lineX E) = U :=
    X_span_eq_of_cubic_pair H B V F U W (lineX E) c.normalizes_lineY hHU hBU h0U
      (le_conjugateSpanBy V H) hXH (lineX_le_characterKernel H B E c.normalizes_lineY hc hXH)
      ⟨b,hb⟩ hV hWX hdouble
  have hUVE : U = lineV V E := hXV.symm.trans
    (lineV_eq_X_span (T : Subgroup G) M Y V E hTM hYM d.normalizes hGEproduct).symm
  have hUMc : U ≤ conjugateSpanBy V Mc := hUVE.le.trans hVE
  refine ⟨hU,hWZ,hWcard,hWX,m,hS,h₁,h₂,Φ,hΦ,hUVE,hUMc,?_⟩
  intro s hs hsE
  have hVne : V ≠ ⊥ := fun he => hZ (bot_unique ((hZE.trans hEV).trans he.le))
  obtain ⟨hUs,hR,hcomm,hA,hne⟩ := ambient_pair_in_local_span V Mc U
    (le_conjugateSpanBy V H) hVne hUMc (s⁻¹) (Mc.inv_mem (hTMc hs))
  refine ⟨hUs,hR,hcomm,hA,hne,?_⟩
  have hRH : centralizer (V : Set G) ≤ H := hlocal.ge.trans
    (inf_le_left.trans ((pCoreIn_le 2 (firstAmalgamGroup Y T E F)).trans le_sup_left))
  have hYU := terminal_Y_normalizes_span T M Y V E F d c hYM hYcore hRH
  have hMY : M ≤ normalizer (Y : Set G) := by
    apply (normal_subgroupOf_iff_le_normalizer hYM).mp
    rw [hY]
    exact residualY_normal M Mc
  exact pair_normalized_by_product M Y (lineT T E) (T : Subgroup G) U hMproduct
    (hTM.trans hMY) hYU ((le_sup_right.trans le_sup_left).trans hHU)
    hindex (s⁻¹) (T.inv_mem hs) (fun hi => hsE ((lineT T E).inv_mem_iff.mp hi))

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear
