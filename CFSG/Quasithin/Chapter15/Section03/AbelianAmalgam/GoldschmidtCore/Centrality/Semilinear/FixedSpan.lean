module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.ActualAction

/-!
# Identifying the actual fixed module with the source seed span

The character action preserves W₀ + βW₀ for every H-invariant binary
subspace W₀. Apply this to W₀ = ⟨Fᴴ⟩ and the actual complementary
planes V = F + Fᵇ. The resulting decomposition spans U = ⟨Vᴴ⟩.
As Q centralizes F, W₀ lies in C_U(Q); uniqueness of the previously
constructed cubic splitting proves equality. Source F=⟨Z^{Y_F}⟩
then identifies this subgroup with ⟨Zᴴ⟩.

`terminal_bad_character_action` constructs elementary U, the literal
seed-span equality, the faithful H/O₂(H) conjugation representation,
and the two actual cubic summands from TerminalConfiguration and the
earlier orthogonal, residual and source-66 conclusions. It proves the
kernel and action premises rather than taking them as a configuration.
Offender transfer, natural recognition and ambient U=V_E transport remain
separate obligations of the source reduction.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.66–68 and the terminal module argument, printed pp.1152–1155.
-/

@[expose] public section
open Subgroup Stellmacher Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear
variable {G : Type*} [Group G] [Finite G]

private theorem binary_add_self {X : Type*} [AddCommGroup X] [Module (ZMod 2) X] (x : X) :
    x + x = 0 := by
  have h := @two_smul (ZMod 2) X _ _ _ x
  have hz : (2 : ZMod 2) = 0 := by decide
  rw [hz,zero_smul] at h
  exact h.symm

private theorem binary_quadratic {X : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    (β : Module.End (ZMod 2) X) (hβ : β ^ 2 + β + 1 = 0) (x : X) :
    β (β x) = x + β x := by
  apply add_right_cancel (b := β x + x)
  calc
    β (β x) + (β x + x) = 0 := by
      have h : β (β x) + β x + x = 0 := LinearMap.congr_fun hβ x
      simpa only [add_assoc] using h
    _ = (x + β x) + (β x + x) := by
      rw [add_assoc,← add_assoc (β x),binary_add_self,zero_add,binary_add_self]

/-- The cubic closure of an H-invariant subspace is again H-invariant.
The proof uses the actual character action, not an assumed linearity over F₄. -/
theorem cubicPair_normalized (H B U W : Subgroup G) [IsElementaryAbelian 2 U]
    (hHB : H ≤ normalizer (B : Set G)) (hHU : H ≤ normalizer (U : Set G))
    (hBU : B ≤ normalizer (U : Set G))
    (h0U : ambientTwoCore B ≤ centralizer (U : Set G))
    (hc : Nat.card (B ⧸ localTwoCore B) = 3) (hgen : U = ⁅U,B⁆)
    (hWU : W ≤ U) (hHW : H ≤ normalizer (W : Set G))
    (b : B) (hb : b ∉ localTwoCore B) :
    H ≤ normalizer ((W ⊔ W.map (MulAut.conj (b : G)).toMonoidHom : Subgroup G) : Set G) := by
  let D := W ⊔ W.map (MulAut.conj (b : G)).toMonoidHom
  let β := externalCubicAction B U hBU h0U (QuotientGroup.mk' _ b)
  have hp := externalCubicAction_polynomial B U hBU h0U hc hgen b hb
  have hbW (w : Additive U) (hw : (w.toMul : G) ∈ W) : (β w).toMul.val ∈ D :=
    Subgroup.mem_sup_right (mem_map.mpr ⟨w.toMul,hw,rfl⟩)
  have hb2W (w : Additive U) (hw : (w.toMul : G) ∈ W) : (β (β w)).toMul.val ∈ D := by
    rw [binary_quadratic β hp w]
    exact D.mul_mem (Subgroup.mem_sup_left hw) (hbW w hw)
  apply le_normalizer_iff.mpr
  intro h hh x hx
  have hpres : D.map (MulAut.conj h).toMonoidHom ≤ D := by
    dsimp [D]
    rw [Subgroup.map_sup]
    apply sup_le
    · rintro _ ⟨w,hw,rfl⟩
      exact Subgroup.mem_sup_left ((mem_normalizer_iff.mp (hHW hh) w).mp hw)
    · rintro _ ⟨_,⟨w,hw,rfl⟩,rfl⟩
      let u : Additive U := Additive.ofMul ⟨w,hWU hw⟩
      let hH : H := ⟨h,hh⟩
      let v := spanAction H U hHU hH u
      have hv : (v.toMul : G) ∈ W := (mem_normalizer_iff.mp (hHW hh) w).mp hw
      by_cases hχ : quotientAction H B hHB hH = 1
      · have hi := LinearMap.congr_fun
          (externalCubicAction_intertwining H B U hHB hHU hBU h0U hH (QuotientGroup.mk' _ b)) u
        rw [hχ] at hi
        have he := congrArg (fun v : Additive U => (v.toMul : G)) hi
        change MulAut.conj h (MulAut.conj (b : G) w) = (β v).toMul.val at he
        change MulAut.conj h (MulAut.conj (b : G) w) ∈ D
        rw [he]
        exact hbW v hv
      · have hi := LinearMap.congr_fun
          (coreAction_inverts_cubic H B U hHB hHU hBU h0U hc hH hχ b) u
        have he := congrArg (fun v : Additive U => (v.toMul : G)) hi
        change MulAut.conj h (MulAut.conj (b : G) w) = (β (β v)).toMul.val at he
        change MulAut.conj h (MulAut.conj (b : G) w) ∈ D
        rw [he]
        exact hb2W v hv
  exact hpres (mem_map_of_mem _ hx)


/-- The H-span of a complementary plane and its cubic translate is the
cubic double of that plane's H-span. -/
theorem span_eq_cubicPair (H B V F U : Subgroup G) [IsElementaryAbelian 2 U]
    (hHB : H ≤ normalizer (B : Set G))
    (hBU : B ≤ normalizer (U : Set G))
    (h0U : ambientTwoCore B ≤ centralizer (U : Set G))
    (hc : Nat.card (B ⧸ localTwoCore B) = 3) (hgen : U = ⁅U,B⁆)
    (hU : U = conjugateSpanBy V H)
    (b : B) (hb : b ∉ localTwoCore B)
    (hV : V = F ⊔ F.map (MulAut.conj (b : G)).toMonoidHom) :
    U = conjugateSpanBy F H ⊔
      (conjugateSpanBy F H).map (MulAut.conj (b : G)).toMonoidHom := by
  have hFV : F ≤ V := hV.ge.trans' le_sup_left
  have hWU : conjugateSpanBy F H ≤ U := by
    rw [hU]; exact conjugateSpanBy_mono hFV le_rfl
  have hHU : H ≤ normalizer (U : Set G) := hU ▸ le_normalizer_conjugateSpanBy V H
  apply le_antisymm
  · rw [hU]
    apply conjugateSpanBy_le _ (cubicPair_normalized H B U (conjugateSpanBy F H)
      hHB hHU hBU h0U hc hgen hWU (le_normalizer_conjugateSpanBy F H) b hb)
    rw [hV]
    exact sup_le_sup (le_conjugateSpanBy F H) (map_mono (le_conjugateSpanBy F H))
  · apply sup_le hWU
    rintro _ ⟨w,hw,rfl⟩
    exact (mem_normalizer_iff.mp (hBU b.property) w).mp (hWU hw)

/-- If the seed plane is centralized by Q, its H-span is exactly C_U(Q).
The conclusion is proved from the actual splitting, with no dimension premise. -/
theorem coreFixed_eq_plane_span (H B V F U : Subgroup G) [IsElementaryAbelian 2 U]
    (hHB : H ≤ normalizer (B : Set G))
    (hBU : B ≤ normalizer (U : Set G))
    (h0U : ambientTwoCore B ≤ centralizer (U : Set G))
    (hN : ambientTwoCore H ⊓ characterKernel H B hHB = H ⊓ centralizer (U : Set G))
    (hc : Nat.card (B ⧸ localTwoCore B) = 3) (hgen : U = ⁅U,B⁆)
    (hU : U = conjugateSpanBy V H)
    (q : H) (hq : q ∈ localTwoCore H) (hqχ : quotientAction H B hHB q ≠ 1)
    (b : B) (hb : b ∉ localTwoCore B)
    (hV : V = F ⊔ F.map (MulAut.conj (b : G)).toMonoidHom)
    (hFQ : F ≤ centralizer (ambientTwoCore H : Set G)) :
    coreFixed H U = conjugateSpanBy F H := by
  let W := conjugateSpanBy F H
  let Wb := W.map (MulAut.conj (b : G)).toMonoidHom
  have hdouble : U = W ⊔ Wb := span_eq_cubicPair H B V F U hHB hBU h0U hc hgen hU b hb hV
  have hWU : W ≤ U := hdouble.ge.trans' le_sup_left
  have hWbU : Wb ≤ U := hdouble.ge.trans' le_sup_right
  have hHU : H ≤ normalizer (U : Set G) := hU ▸ le_normalizer_conjugateSpanBy V H
  have hQ : H ≤ normalizer (ambientTwoCore H : Set G) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hCQ : H ≤ normalizer (centralizer (ambientTwoCore H : Set G) : Set G) :=
    hQ.trans ((normal_subgroupOf_iff_le_normalizer
      (centralizer_le_normalizer (ambientTwoCore H : Set G))).mp inferInstance)
  have hWF : W ≤ coreFixed H U := le_inf hWU (conjugateSpanBy_le hFQ hCQ)
  let e := coreFixedPairEquiv H B U hHB hHU hBU h0U hN hc hgen q hq hqχ b hb
  have htop : W.subgroupOf U ⊔ Wb.subgroupOf U = ⊤ := by
    apply Subgroup.map_injective U.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hWU,map_subgroupOf_eq_of_le hWbU,
      ← MonoidHom.range_eq_map,Subgroup.range_subtype,← hdouble]
  apply le_antisymm _ hWF
  intro x hx
  have hm : (⟨x,hx.1⟩ : U) ∈ W.subgroupOf U ⊔ Wb.subgroupOf U := by rw [htop]; trivial
  obtain ⟨y,hy,z,hz,hyz⟩ := Subgroup.mem_sup.mp hm
  obtain ⟨v,hv,hvz⟩ := hz
  let xx : Additive (coreFixed H U) := Additive.ofMul ⟨x,hx⟩
  let yy : Additive (coreFixed H U) := Additive.ofMul ⟨y,hWF hy⟩
  let vv : Additive (coreFixed H U) := Additive.ofMul ⟨v,hWF hv⟩
  have he : e (xx,0) = e (yy,vv) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    change x * ((b : G) * 1 * (b : G)⁻¹) = (y : G) * ((b : G) * v * (b : G)⁻¹)
    change (b : G) * v * (b : G)⁻¹ = (z : G) at hvz
    rw [hvz,mul_one,mul_inv_cancel,mul_one]
    exact (congrArg Subtype.val hyz).symm
  have hxy := congrArg (fun a : Additive (coreFixed H U) => (a.toMul : G))
    (congrArg Prod.fst (e.injective he))
  change x = (y : G) at hxy
  rw [hxy]
  exact hy

omit [Finite G] in
/-- The two source seed conventions generate the same H-span. -/
theorem plane_span_eq_seed_span (H J Z F : Subgroup G)
    (hJ : J ≤ H) (hZF : Z ≤ F) (hF : F = ThompsonExtension.conjugateSpan J Z) :
    conjugateSpanBy F H = conjugateSpanBy Z H := by
  apply le_antisymm _ (conjugateSpanBy_mono hZF le_rfl)
  apply conjugateSpanBy_le _ (le_normalizer_conjugateSpanBy Z H)
  rw [hF]
  apply iSup_le
  intro j
  rintro x ⟨z,hz,rfl⟩
  exact le_normalizer_iff.mp (le_normalizer_conjugateSpanBy Z H) _
    (H.inv_mem (hJ j.property)) _ (le_conjugateSpanBy Z H hz)


/-- The actual elementary module and faithful fixed-space quotient action in
source 15.3.68's bad-character branch. All action and span conclusions are
constructed from the preceding source geometry and the kernel calculation. -/
theorem terminal_bad_character_action
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
      ∃ ρ : Representation (ZMod 2) (H ⧸ pCore 2 H) (Additive W),
        Function.Injective ρ ∧
        (∀ (h : H) (w : Additive W),
          ((ρ (QuotientGroup.mk' _ h) w).toMul : G) = (h : G) * (w.toMul : G) * (h : G)⁻¹) ∧
        ∃ b : B, b ∉ localTwoCore B ∧
          U = W ⊔ W.map (MulAut.conj (b : G)).toMonoidHom ∧
          Nonempty ((Additive W × Additive W) ≃ₗ[ZMod 2] Additive U) := by
  let H := amalgamGroup Y T E F
  let B := lineY Y E
  let U := conjugateSpanBy V H
  have hHB := c.normalizes_lineY
  have hBV : B ≤ normalizer (V : Set G) :=
    (lineY_le Y E).trans (inf_le_left.trans (hYM.trans d.normalizes))
  have hVc : V = ⁅V,B⁆ := Orthogonal.lineY_commutator d Y E hYM hEV hEcard hE himage
  have hVB : V ≤ B := hVc.le.trans
    (le_normalizer_iff_commutator_le_right.mp
      ((c.module_le_core.trans (pCoreIn_le 2 H)).trans hHB))
  have hV0 : V ≤ ambientTwoCore B :=
    le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 V) hVB hBV
  have h0V : ambientTwoCore B ≤ centralizer (V : Set G) :=
    (Orthogonal.lineY_twoCore d Y E hYM hEV himage hYcore).le.trans inf_le_right
  have hUelem := external_span_elementary H B V hHB hV0 h0V
  let := hUelem
  refine ⟨hUelem,?_⟩
  obtain ⟨h0Q,h0U,hlocal,hN⟩ := terminal_kernel_reduction T M Y V E F d c
    hYM hEV hEcard hE hZE hZ himage hYcore hCT h66F
  have hBU := external_normalizes_span H B V hHB hBV
  have hHU := le_normalizer_conjugateSpanBy V H
  have hgen := external_span_eq_commutator H B V hHB hBV hVc
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
  have hQQ : ambientTwoCore H ≤ twoCoreAmbient (firstAmalgamGroup Y T E F) := by
    apply le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 H)
      ((core_le_lineT Y T E F c.sylow).trans le_sup_right)
    exact le_sup_left.trans (H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
  have hFQ : F ≤ centralizer (ambientTwoCore H : Set G) :=
    le_centralizer_iff.mp (hQQ.trans (h66F.le.trans inf_le_right))
  have hW := coreFixed_eq_plane_span H B V F U hHB hBU h0U hN hc hgen rfl
    qH q.2 hqχ ⟨b,hb⟩ hb0 hV hFQ
  have hWZ : coreFixed H U = conjugateSpanBy (centralInvolutions T) H :=
    hW.trans (plane_span_eq_seed_span H (lineY Y F) (centralInvolutions T) F
      (le_sup_left.trans le_sup_left) c.seed_le c.seed_span)
  have hC := coreFixed_centralizer H B U hHB hHU hBU h0U hN hc hgen qH q.2 hqχ ⟨b,hb⟩ hb0
  let hn := coreFixed_normalized H U hHU
  refine ⟨hWZ,coreQuotientAction H (coreFixed H U) hn hC,
    coreQuotientAction_injective H (coreFixed H U) hn hC,
    coreQuotientAction_apply H (coreFixed H U) hn hC,⟨b,hb⟩,hb0,?_,?_⟩
  · rw [hW]
    exact span_eq_cubicPair H B V F U hHB hBU h0U hc hgen rfl ⟨b,hb⟩ hb0 hV
  · exact ⟨coreFixedPairEquiv H B U hHB hHU hBU h0U hN hc hgen qH q.2 hqχ ⟨b,hb⟩ hb0⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear
