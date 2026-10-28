module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.FixedSpan
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.CubicField
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.FixedDisplacement

/-!
# Constructed source instances of the semilinear operator identities

The source-local kernel theorem and the actual cubic action supply every
hypothesis of the dimension-independent operator lemmas. This endpoint
constructs the source U and its chosen cubic/inverting elements, identifies
W with both the Z-span and the actual commutator [U,q], proves that the
two cubic summands are disjoint and generate U, and constructs the F₄
scalar structure with literal conjugation as multiplication by its root.
No recognition or classification input is required for these identities.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.66–68 and the terminal semilinear argument, printed pp.1152–1155.
-/

@[expose] public section
open Subgroup Stellmacher Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear
variable {G : Type*} [Group G] [Finite G]

/-- The actual source instance of the four-element field action, fixed
commutator identity, and internal direct sum. -/
theorem terminal_bad_character_operators
    (T : Sylow 2 G) (M Y V E F : Subgroup G) [IsElementaryAbelian 2 V]
    (d : OrthogonalFourBinary.NaturalAction V M)
    (c : TerminalConfiguration T M Y V E F d)
    (hYM : Y ≤ M) (hEV : E ≤ V) (hEcard : Nat.card E = 4)
    (hE : ∀ e : E, d.singular ⟨e,hEV e.property⟩)
    (hZE : centralInvolutions T ≤ E) (hZ : centralInvolutions T ≠ ⊥)
    (himage : LocalRelations.actionImage d Y =
      pResidual 2 OrthogonalFourBinary.TerminalLines.IsometryGroup)
    (hYcore : twoCoreAmbient Y = Y ⊓ centralizer (V : Set G))
    (hCT : centralizer (V : Set G) ≤ (T : Subgroup G))
    (h66F : twoCoreAmbient (firstAmalgamGroup Y T E F) =
      firstAmalgamGroup Y T E F ⊓ centralizer (F : Set G))
    (hc : Nat.card (lineY Y E ⧸ localTwoCore (lineY Y E)) = 3)
    (hbad : ∃ q : ambientTwoCore (amalgamGroup Y T E F),
      quotientAction _ (lineY Y E) c.normalizes_lineY
        ⟨q.1,pCoreIn_le 2 (amalgamGroup Y T E F) q.2⟩ ≠ 1) :
    let H := amalgamGroup Y T E F
    let B := lineY Y E
    let U := conjugateSpanBy V H
    ∃ hU : IsElementaryAbelian 2 U, letI := hU
      let W := coreFixed H U
      W = conjugateSpanBy (centralInvolutions T) H ∧
      ∃ b : B, b ∉ localTwoCore B ∧ ∃ q : H,
        q ∈ localTwoCore H ∧ quotientAction H B c.normalizes_lineY q ≠ 1 ∧
        W = ⁅U,zpowers (q : G)⁆ ∧
        U = W ⊔ W.map (MulAut.conj (b : G)).toMonoidHom ∧
        Disjoint W (W.map (MulAut.conj (b : G)).toMonoidHom) ∧
        ∃ μ : Module CubicField (Additive U), letI := μ
          ∀ u : Additive U, (((AdjoinRoot.root cubicPolynomial) • u).toMul : G) =
            (b : G) * (u.toMul : G) * (b : G)⁻¹ := by
  let H := amalgamGroup Y T E F
  let B := lineY Y E
  let U := conjugateSpanBy V H
  obtain ⟨hU,hW,_ρ,_hfaith,_hconj,b,hb,hdouble,_he⟩ :=
    terminal_bad_character_action T M Y V E F d c hYM hEV hEcard hE hZE hZ
      himage hYcore hCT h66F hc hbad
  let := hU
  obtain ⟨_h0Q,h0U,_hlocal,hN⟩ := terminal_kernel_reduction T M Y V E F d c
    hYM hEV hEcard hE hZE hZ himage hYcore hCT h66F
  have hBV : B ≤ normalizer (V : Set G) :=
    (lineY_le Y E).trans (inf_le_left.trans (hYM.trans d.normalizes))
  have hBU := external_normalizes_span H B V c.normalizes_lineY hBV
  have hHU := le_normalizer_conjugateSpanBy V H
  have hgen := external_span_eq_commutator H B V c.normalizes_lineY hBV
    (Orthogonal.lineY_commutator d Y E hYM hEV hEcard hE himage)
  obtain ⟨q,hqχ⟩ := hbad
  let qH : H := ⟨q.1,pCoreIn_le 2 H q.2⟩
  exact ⟨hU,hW,b,hb,qH,q.2,hqχ,
    coreFixed_eq_commutator H B U c.normalizes_lineY hHU hBU h0U hN hc hgen qH q.2 hqχ b hb,
    hdouble,coreFixed_disjoint_cubic H B U c.normalizes_lineY hHU hBU h0U hN hc hgen qH q.2 hqχ b hb,
    externalCubicFieldModule B U hBU h0U hc hgen b hb,
    externalCubicFieldModule_root_smul B U hBU h0U hc hgen b hb⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear
