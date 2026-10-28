module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Kernel
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.OrthogonalSplitting
/-!
# Source-local kernel assembly and the trivial-character branch

Conjugating the genuine centralizer identity of 15.3.66(5) gives
O₂(G₁)=C_{G₁}(F). The literal terminal configuration, the external Y_E
core identity, and the complementary singular-plane calculation then prove
O₂(G₁) ∩ ker χ = C_G(V) and O₂(H) ∩ ker χ = C_H(⟨Vᴴ⟩).
Consequently trivial action of O₂(H) on Y_E/O₂(Y_E) implies centralization
of V. No inclusion Y_E ≤ H or bound on the common local core is used.

The explicit inputs are genuine earlier source conclusions: the natural
action and residual image, O₂(Y)=C_Y(V), C_G(V)≤T, the nontrivial central
seed, source 66's centralizer identity, and the four already assembled
noncentrality clauses of 68. The bad-character module and ambient transport
are separate obligations; this module does not assert the full 68(2).

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.2,7,49,66–68, printed pp.1121–1122,1142,1152–1155.
-/

public section
open Subgroup Stellmacher OrthogonalFourBinary OrthogonalFourBinary.TerminalLines
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear
open LocalRelations LocalRelations.OrthogonalProducts
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem core_map_equiv (e : G ≃* G) (A : Subgroup G) :
    twoCoreAmbient (A.map e.toMonoidHom) = (twoCoreAmbient A).map e.toMonoidHom := by
  let eA : A ≃* A.map e.toMonoidHom := e.subgroupMap A
  have hc := pCore_map_iso 2 eA
  unfold twoCoreAmbient
  rw [← hc, map_map, map_map]
  rfl

omit [Finite G] in
private theorem centralizer_map_equiv (A : Subgroup G) (e : G ≃* G) :
    (centralizer (A : Set G)).map e.toMonoidHom = centralizer (A.map e.toMonoidHom : Set G) := by
  apply le_antisymm (map_centralizer_le_centralizer_image _ _)
  intro x hx
  refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
  intro y hy
  apply e.injective
  simpa only [map_mul, e.apply_symm_apply] using hx (e y) (mem_map_of_mem _ hy)

/-- Conjugate source 66(5) along the actual chosen Sylow element. -/
theorem first_core_eq_line_centralizer (Y T E : Subgroup G) (s : G)
    (hs : s ∈ T) (hTY : T ≤ normalizer (Y : Set G))
    (hi : (lineT T E).relIndex T = 2)
    (h66 : twoCoreAmbient (lineY Y E ⊔ lineT T E) =
      (lineY Y E ⊔ lineT T E) ⊓ centralizer (E : Set G)) :
    twoCoreAmbient (firstAmalgamGroup Y T E (otherLine E s)) =
      firstAmalgamGroup Y T E (otherLine E s) ⊓ centralizer (otherLine E s : Set G) := by
  rw [firstAmalgam_eq_conjugate Y T E s hs hTY hi]
  change twoCoreAmbient ((lineY Y E ⊔ lineT T E).map (MulAut.conj s⁻¹).toMonoidHom) = _
  rw [core_map_equiv, h66, map_inf _ _ _ (MulAut.conj s⁻¹).injective,
    centralizer_map_equiv]
  rfl

/-- The two external-core containments and both kernel equalities from genuine terminal data. -/
theorem terminal_kernel_reduction
    (T : Sylow 2 G) (M Y V E F : Subgroup G) (d : NaturalAction V M)
    (c : TerminalConfiguration T M Y V E F d)
    (hYM : Y ≤ M) (hEV : E ≤ V) (hEcard : Nat.card E = 4)
    (hE : ∀ e : E, d.singular ⟨e,hEV e.property⟩)
    (hZE : centralInvolutions T ≤ E) (hZ : centralInvolutions T ≠ ⊥)
    (himage : actionImage d Y = pResidual 2 TerminalLines.IsometryGroup)
    (hYcore : twoCoreAmbient Y = Y ⊓ centralizer (V : Set G))
    (hCT : centralizer (V : Set G) ≤ (T : Subgroup G))
    (h66F : twoCoreAmbient (firstAmalgamGroup Y (T : Subgroup G) E F) =
      firstAmalgamGroup Y (T : Subgroup G) E F ⊓ centralizer (F : Set G)) :
    let H := amalgamGroup Y (T : Subgroup G) E F
    let B := lineY Y E
    let K := characterKernel H B c.normalizes_lineY
    let U := conjugateSpanBy V H
    ambientTwoCore B ≤ ambientTwoCore H ∧
      ambientTwoCore B ≤ centralizer (U : Set G) ∧
      twoCoreAmbient (firstAmalgamGroup Y (T : Subgroup G) E F) ⊓ K =
        centralizer (V : Set G) ∧
      ambientTwoCore H ⊓ K = H ⊓ centralizer (U : Set G) := by
  let H := amalgamGroup Y (T : Subgroup G) E F
  let B := lineY Y E
  let Q₁ := twoCoreAmbient (firstAmalgamGroup Y (T : Subgroup G) E F)
  have hBV : B ≤ normalizer (V : Set G) :=
    (lineY_le Y E).trans (inf_le_left.trans (hYM.trans d.normalizes))
  have hB0 : ambientTwoCore B = B ⊓ centralizer (V : Set G) :=
    Orthogonal.lineY_twoCore d Y E hYM hEV himage hYcore
  have hRTE : centralizer (V : Set G) ≤ lineT (T : Subgroup G) E :=
    le_inf hCT ((centralizer_le hEV).trans (centralizer_le_normalizer (E : Set G)))
  have hRH : centralizer (V : Set G) ≤ H := hRTE.trans (le_sup_right.trans le_sup_left)
  have hQH : Q₁ ≤ H := (map_subtype_le _).trans le_sup_left
  have hQF : Q₁ ≤ centralizer (F : Set G) := h66F.le.trans inf_le_right
  have hRQ : centralizer (V : Set G) ≤ Q₁ := by
    rw [show Q₁ = _ from h66F]
    exact le_inf (hRTE.trans le_sup_right) (centralizer_le c.line_le)
  obtain ⟨z,hz⟩ := ne_bot_iff_exists_ne_one.mp hZ
  obtain ⟨b,hb,hspan,_⟩ := exists_lineY_complementary_conjugate V M Y E F d hYM hEV
    c.line_le hEcard c.line_card hE c.line_singular (Ne.symm c.line_ne)
    ⟨z,(fun he => hz (Subtype.ext he)),hZE z.property,c.seed_le z.property⟩ himage
  have hk := local_kernel_eq_centralizer H B V F Q₁ c.normalizes_lineY hBV hB0
    hQH hQF hRQ b hb hspan
  have hQQ : ambientTwoCore H ≤ Q₁ := by
    apply le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 H)
      ((core_le_lineT Y T E F c.sylow).trans le_sup_right)
    exact le_sup_left.trans (H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
  have hCQ := span_centralizer_le_core Y T V E F (T.isPGroup'.to_le hCT)
  exact ⟨external_twoCore_le_core H B c.normalizes_lineY (hB0.le.trans (inf_le_right.trans hRH)),
    external_twoCore_centralizes_span H B V c.normalizes_lineY (hB0.le.trans inf_le_right),
    hk,kernel_inter_eq_span_centralizer H B V Q₁ c.normalizes_lineY hBV hB0 hk hQQ hCQ⟩

omit [Finite G] in
/-- The trivial-character branch gives the centrality needed by source 68(2). -/
theorem trivial_character_core_centralizes (H B V : Subgroup G)
    (hHB : H ≤ normalizer (B : Set G))
    (hN : ambientTwoCore H ⊓ characterKernel H B hHB =
      H ⊓ centralizer (conjugateSpanBy V H : Set G))
    (htriv : ∀ q : ambientTwoCore H,
      quotientAction H B hHB ⟨q.1,pCoreIn_le 2 H q.2⟩ = 1) :
    ambientTwoCore H ≤ centralizer (V : Set G) := by
  have hk := trivial_branch_quotient_kernel_le H B (ambientTwoCore H) hHB
    (pCoreIn_le 2 H) htriv
  exact (le_inf le_rfl hk).trans (hN.le.trans
    (inf_le_right.trans (centralizer_le (le_conjugateSpanBy V H))))

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear
