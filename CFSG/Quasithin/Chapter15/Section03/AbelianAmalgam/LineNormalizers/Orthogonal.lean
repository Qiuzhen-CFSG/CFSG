module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Orthogonal.ProductKernel
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Orthogonal.ResidualFullAction
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Orthogonal.SylowGeometry
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.Basic

/-!
# Singular-line geometry for 15.3.66

The actual quadratic action gives full `M_E` action, the centralization of
`E` by `Q_E`, the identity `V=[V,Y_E]`, and the action kernel of `Y_E` on `V`.
The two-group kernel calculation then turns full `Y_E T_E` action into the
actual S₃ quotient, the asserted two-core equality, and the literal product
`G_E=Y_E T_E C_G(E)`.

`source_lemma_15_3_66` assembles all seven clauses for the genuine
`Y = residualY M Mc`. Its inputs are the selected singular line and Sylow
witness, the actual compatible natural action, and the earlier fixed-space,
residual-image, residual-kernel and centralizer conclusions. Full action of
`Y_E T_E` is proved from its cubic residual image and selected Sylow image.
Normality of the defined residual supplies the normalization needed to
identify its join with `T_E` as a setwise product. Finally `Z≤E` gives
`C_G(E)≤Mc` using 15.3.4.

The re-exported `line_sylow_geometry_of_source` also supplies
`[V,C_T(E)]=E`. `residualY_lineY_action_ker_eq_twoCore` identifies the
intrinsic action kernel needed immediately after 15.3.66. The original
conditional product helper remains available independently.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.2, 15.3.7, 15.3.49(3), and 15.3.66, printed pp.1121–1122,
1142, and 1152 (PDF pp.1138–1139, 1159, and 1169).
-/

public section

open Subgroup OrthogonalFourBinary OrthogonalFourBinary.TerminalLines
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Orthogonal
open CFSG.Quasithin.Chapter15.Section03 GoldschmidtCore.LocalRelations
variable {G : Type*} [Group G] [Finite G] {V M : Subgroup G}

/-- Clauses (5)–(6) after full action of the residual product has been established.
The full-action premise remains an obligation of the source assembly. -/
theorem lineNormalizer_consequences_of_residual_full_action
    (d : NaturalAction V M) (Y T E : Subgroup G)
    (hYM : Y ≤ M) (hEV : E ≤ V) (hcard : Nat.card E = 4)
    (hs : ∀ e : E, d.singular ⟨e, hEV e.property⟩)
    (himage : actionImage d Y = pResidual 2 TerminalLines.IsometryGroup)
    (hYcore : Stellmacher.twoCoreAmbient Y = Y ⊓ centralizer (V : Set G))
    (hT : IsPGroup 2 T) (hTY : T ≤ normalizer (Y : Set G))
    (hfull : Function.Surjective
      (lineAction E (lineY Y E ⊔ lineT T E) (lineProduct_le_normalizer Y T E))) :
    Nonempty (((lineY Y E ⊔ lineT T E : Subgroup G) ⧸
        pCore 2 (lineY Y E ⊔ lineT T E : Subgroup G)) ≃* Equiv.Perm (Fin 3)) ∧
      V = ⁅V,lineY Y E⁆ ∧
      lineQ E ≤ centralizer (E : Set G) ∧
      Stellmacher.twoCoreAmbient (lineY Y E ⊔ lineT T E) =
        (lineY Y E ⊔ lineT T E) ⊓ centralizer (E : Set G) ∧
      (lineNormalizer E : Set G) =
        (lineY Y E : Set G) * (lineT T E : Set G) * (centralizer (E : Set G) : Set G) := by
  let := singularLine_isKleinFour d E hEV hcard hs
  have hk := lineProduct_kernel_isPGroup d Y T E hYM hEV hcard hs himage hYcore hT hTY
  exact ⟨⟨lineProductQuotientEquiv E _ (lineProduct_le_normalizer Y T E) hfull hk⟩,
    lineY_commutator d Y E hYM hEV hcard hs himage,
    lineQ_le_centralizer d E hEV hcard hs,
    lineProduct_twoCore_of_full_action E _ (lineProduct_le_normalizer Y T E) hfull hk,
    lineNormalizer_three_factor_product Y T E hTY hfull⟩

/-- Clauses (5)–(6) for the defined source residual, with full action proved
from the selected Sylow subgroup and the earlier residual image. -/
theorem residualY_lineNormalizer_consequences
    (d : NaturalAction V M) (Mc : Subgroup G) (T : Sylow 2 G) (E : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hEV : E ≤ V) (hcard : Nat.card E = 4)
    (hs : ∀ e : E, d.singular ⟨e, hEV e.property⟩)
    (himage : actionImage d (residualY M Mc) = pResidual 2 TerminalLines.IsometryGroup)
    (hYcore : Stellmacher.twoCoreAmbient (residualY M Mc) =
      residualY M Mc ⊓ centralizer (V : Set G))
    (P : Sylow 2 (lineM M E))
    (hP : (P : Subgroup (lineM M E)).map (lineM M E).subtype = lineT T E) :
    Nonempty (((lineY (residualY M Mc) E ⊔ lineT T E : Subgroup G) ⧸
        pCore 2 (lineY (residualY M Mc) E ⊔ lineT T E : Subgroup G)) ≃*
          Equiv.Perm (Fin 3)) ∧
      V = ⁅V,lineY (residualY M Mc) E⁆ ∧
      lineQ E ≤ centralizer (E : Set G) ∧
      Stellmacher.twoCoreAmbient (lineY (residualY M Mc) E ⊔ lineT T E) =
        (lineY (residualY M Mc) E ⊔ lineT T E) ⊓ centralizer (E : Set G) ∧
      (lineNormalizer E : Set G) =
        (lineY (residualY M Mc) E : Set G) * (lineT T E : Set G) *
          (centralizer (E : Set G) : Set G) := by
  have hYM := Chapter14.SourcePreliminaries.sourceResidual_le M Mc
  have hTY : (T : Subgroup G) ≤ normalizer (residualY M Mc : Set G) :=
    hTM.trans ((normal_subgroupOf_iff_le_normalizer hYM).mp (residualY_normal M Mc))
  exact lineNormalizer_consequences_of_residual_full_action d (residualY M Mc) T E
    hYM hEV hcard hs himage hYcore T.isPGroup' hTY
    (residualY_lineProduct_full_action d Mc T E hEV hcard hs himage P hP)

/-- All seven clauses of source 15.3.66, conditional only on the selected
singular line and genuine earlier local conclusions. The bar denotes the
image through the specified compatible quadratic action, and `S=N_T(V₁)`
is the stabilizer of the actual definite plane. The last two factors of
clause (5) use ambient images of intrinsic two-cores. -/
theorem source_lemma_15_3_66
    (d : NaturalAction V M) (Mc : Subgroup G) (T : Sylow 2 G) (V₁ E : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M)
    (hV₁V : V₁ ≤ V) (hV₁card : Nat.card V₁ = 4)
    (hV₁definite : ∀ v : V₁, v ≠ 1 → ¬ d.singular ⟨v, hV₁V v.property⟩)
    (hEV : E ≤ V) (hcard : Nat.card E = 4)
    (hs : ∀ e : E, d.singular ⟨e, hEV e.property⟩)
    (hZV : centralInvolutions T = V ⊓ centralizer (T : Set G))
    (himage : actionImage d (residualY M Mc) = pResidual 2 TerminalLines.IsometryGroup)
    (hYcore : Stellmacher.twoCoreAmbient (residualY M Mc) =
      residualY M Mc ⊓ centralizer (V : Set G))
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (P : Sylow 2 (lineM M E))
    (hP : (P : Subgroup (lineM M E)).map (lineM M E).subtype = lineT T E) :
    actionImage d (lineT T E) =
        actionImage d (T : Subgroup G) ⊓ (OrthogonalFourBinary.omega :
          Subgroup OrthogonalFourBinary.IndexTwoNormalizer.IsometryGroup) ∧
      (lineT T E).relIndex (T : Subgroup G) = 2 ∧
      (IsKleinFour (actionImage d (lineT T E)) ∧
        actionImage d (lineT T E) ≠ actionImage d (planeStabilizer T V₁)) ∧
      centralInvolutions T ≤ E ∧
      (Nonempty (((lineY (residualY M Mc) E ⊔ lineT T E : Subgroup G) ⧸
          pCore 2 (lineY (residualY M Mc) E ⊔ lineT T E : Subgroup G)) ≃*
            Equiv.Perm (Fin 3)) ∧
        V = ⁅V,lineY (residualY M Mc) E⁆ ∧
        lineQ E ≤ centralizer (E : Set G) ∧
        Stellmacher.twoCoreAmbient (lineY (residualY M Mc) E ⊔ lineT T E) =
          (lineY (residualY M Mc) E ⊔ lineT T E) ⊓ centralizer (E : Set G)) ∧
      (lineNormalizer E : Set G) =
        (lineY (residualY M Mc) E : Set G) * (lineT T E : Set G) *
          (centralizer (E : Set G) : Set G) ∧
      centralizer (E : Set G) ≤ Mc := by
  obtain ⟨ho, hi, hk, hd, hz, _⟩ := line_sylow_geometry_of_source d T V₁ E hTM
    hV₁V hV₁card hV₁definite hEV hcard hs hZV P hP
  obtain ⟨hq, hv, hQ, hc, hp⟩ := residualY_lineNormalizer_consequences d Mc T E
    hTM hEV hcard hs himage hYcore P hP
  exact ⟨ho, hi, ⟨hk, hd⟩, hz, ⟨hq, hv, hQ, hc⟩, hp,
    centralizer_line_le_of_Z_le E (centralInvolutions T) Mc hz hMc⟩

/-- The action kernel of the actual `Y_E` on `V` is its intrinsic two-core;
this is the kernel calculation used after source 15.3.66. -/
theorem residualY_lineY_action_ker_eq_twoCore
    (d : NaturalAction V M) (Mc E : Subgroup G) (hEV : E ≤ V)
    (himage : actionImage d (residualY M Mc) = pResidual 2 TerminalLines.IsometryGroup)
    (hYcore : Stellmacher.twoCoreAmbient (residualY M Mc) =
      residualY M Mc ⊓ centralizer (V : Set G)) :
    (d.action.comp (inclusion ((lineY_le (residualY M Mc) E).trans
      (inf_le_left.trans (Chapter14.SourcePreliminaries.sourceResidual_le M Mc))))).ker =
        pCore 2 (lineY (residualY M Mc) E) :=
  lineY_action_ker_eq_twoCore d (residualY M Mc) E
    (Chapter14.SourcePreliminaries.sourceResidual_le M Mc) hEV himage hYcore

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Orthogonal
