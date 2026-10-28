module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.FixedSpan
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.OffenderTransfer
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.ExternalQuotient

/-!
# Natural recognition for the actual bad-character module

The action and seed-span construction supplies a faithful binary action of
H/O₂(H) on W=C_U(O₂(H)), with literal ambient conjugation. The maximum
elementary offender argument transfers X_E=[X_E,J(T_E)] into its offender
subgroup. The external cubic factor in the actual proper two-local bounds
the quotient's three-rank. These facts discharge the action, offender,
rank and generation premises of the full conditional recognition theorem.
Its compatible Fano marking identifies this actual W with the natural
SL₃(2) representation.

The complete universal F.6.18 and B.5.6 implications remain explicit source
inputs, as do genuine earlier local source conclusions. This module does
not assert those universal theorems or the still separate ambient U=V_E
transport and terminal centrality conclusion.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.66–68 and the terminal argument, printed pp.1152–1155.
-/

@[expose] public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The actual bad-character module reaches full conditional recognition.
Only the complete universal F.6.18 and B.5.6 implications remain source inputs;
its action, offender, three-rank and Fano-generation premises are discharged. -/
theorem terminal_bad_character_natural {κ : GroupClass.{u}}
    (hG : IsSimpleQTKE κ G)
    (sourceF : Recognition.FSource.ClassificationInput κ)
    (sourceB : GeneralClassificationInput.{u,u} κ)
    (T : Sylow 2 G) (M Y V E F : Subgroup G) [IsElementaryAbelian 2 V]
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
    (hbad : ∃ q : ambientTwoCore (amalgamGroup Y T E F),
      quotientAction _ (lineY Y E) c.normalizes_lineY
        ⟨q.1,pCoreIn_le 2 (amalgamGroup Y T E F) q.2⟩ ≠ 1) :
    let H := amalgamGroup Y T E F
    let B := lineY Y E
    let U := conjugateSpanBy V H
    ∃ hU : IsElementaryAbelian 2 U, letI := hU
      let W := coreFixed H U
      W = conjugateSpanBy (centralInvolutions T) H ∧
      ∃ ρ : Representation (ZMod 2) (H ⧸ pCore 2 H) (Additive W),
        Function.Injective ρ ∧
        (∀ (h : H) (w : Additive W),
          ((ρ (QuotientGroup.mk' _ h) w).toMul : G) = (h : G) * (w.toMul : G) * (h : G)⁻¹) ∧
        SourceAlternative (ρ.comp (offenderSubgroup ρ).subtype) ∧
        offenderSubgroup ρ = ⊤ ∧
        ∃ m : (H ⧸ pCore 2 H) ≃* Matrix.PSL3Two.SL,
          ((lineT T E).subgroupOf H).map
            (m.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.borelSL ∧
          ((firstAmalgamGroup Y T E F).subgroupOf H).map
            (m.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.lineParabolicSL ∧
          ((secondAmalgamGroup T E).subgroupOf H).map
            (m.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.pointParabolicSL ∧
          Nonempty (ρ.Equiv (BinaryLinearThree.W.comp m.toMonoidHom)) ∧
          (∀ z : Additive W, z ≠ 0 → Nat.card (Set.range (fun g => ρ g z)) = 7) ∧
          ∃ b : B, b ∉ localTwoCore B ∧
            U = W ⊔ W.map (MulAut.conj (b : G)).toMonoidHom ∧
            Nonempty ((Additive W × Additive W) ≃ₗ[ZMod 2] Additive U) := by
  let H := amalgamGroup Y T E F
  let B := lineY Y E
  let U := conjugateSpanBy V H
  have hZ : centralInvolutions T ≠ ⊥ := by
    intro he
    rw [he] at hZcard
    norm_num at hZcard
  obtain ⟨hU,hW,ρ,hfaith,hconj,b,hb,hdouble,he⟩ :=
    terminal_bad_character_action T M Y V E F d c hYM hEV hEcard hE hZE hZ
      himage hYcore hCT h66F hc hbad
  let := hU
  let W := coreFixed H U
  have hSH : lineT (T : Subgroup G) E ≤ H := le_sup_right.trans le_sup_left
  have hWS : W ≤ lineT (T : Subgroup G) E := inf_le_left.trans
    ((span_le_core Y T V E F c.module_le_core).trans (core_le_lineT Y T E F c.sylow))
  have hXH : lineX E ≤ H := le_sup_left.trans le_sup_right
  have hHW := coreFixed_normalized H U (le_normalizer_conjugateSpanBy V H)
  have hker := faithful_conjugation_kernel H W (hWS.trans hSH)
    (QuotientGroup.mk' (pCore 2 H)) ρ hfaith hconj
  have hXI := internal_thompson_commutator_image_le_offender H (lineT T E) W (lineX E)
    hSH hWS hXH hHW (QuotientGroup.mk' (pCore 2 H)) (QuotientGroup.mk'_surjective _)
    hker ρ hconj hXJ
  obtain ⟨h0Q,h0U,hlocal,hN⟩ := terminal_kernel_reduction T M Y V E F d c
    hYM hEV hEcard hE hZE hZ himage hYcore hCT h66F
  have h0N := ExternalQuotient.external_core_le_kernel_inter H B U c.normalizes_lineY h0Q h0U hN
  have hBV : B ≤ normalizer (V : Set G) :=
    (lineY_le Y E).trans (inf_le_left.trans (hYM.trans d.normalizes))
  have hVc : V = ⁅V,B⁆ := Orthogonal.lineY_commutator d Y E hYM hEV hEcard hE himage
  have hVB : V ≤ B := hVc.le.trans (le_normalizer_iff_commutator_le_right.mp
    ((c.module_le_core.trans (pCoreIn_le 2 H)).trans c.normalizes_lineY))
  have hV0 : V ≤ ambientTwoCore B :=
    le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 V) hVB hBV
  have h0 : ambientTwoCore B ≠ ⊥ := fun he => hZ
    (bot_unique ((hZE.trans hEV).trans (hV0.trans he.le)))
  have hr := ExternalQuotient.quotient_three_rank hG H B c.normalizes_lineY hc h0 h0N hbad
  have hr' : primeRank 3 (H ⧸ pCore 2 H) ≤ 1 := by
    exact (Theory.GroupTheory.primeRank_equiv 3
      (QuotientGroup.quotientMulEquivOfEq (localTwoCore_eq_pCore H))).symm.le.trans hr
  have hHN : H ≤ normalizer (ambientTwoCore B : Set G) :=
    c.normalizes_lineY.trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B))
  have hSQ : IsSQTK κ H := (IsSQTK.equiv (subgroupOfEquivOfLe hHN)).mp
    ((ExternalQuotient.external_normalizer_proper_sqtk hG B h0).2.subgroup _)
  obtain ⟨hB,hI,m,hS,h₁,h₂,hNat,hOrbit⟩ := Recognition.terminal_natural_of_full_classifications
    sourceF sourceB T M Y V E F W d c hSQ hTM hXM hZE hZcard hW ρ hfaith hconj hXI hr'
  exact ⟨hU,hW,ρ,hfaith,hconj,hB,hI,m,hS,h₁,h₂,hNat,hOrbit,b,hb,hdouble,he⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear
