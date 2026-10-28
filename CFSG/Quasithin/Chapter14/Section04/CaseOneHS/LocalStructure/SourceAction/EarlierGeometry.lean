module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Terminal
public import CFSG.Quasithin.ChapterG.Section10.NumericalGeometry
public import CFSG.Quasithin.ChapterG.Section11.LowRank
public import CFSG.Quasithin.Chapter12.Section08.Symplectic.LowRank
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.SourceAction.Geometry

/-!
# Earlier marked action geometry for the original rank-three flag

The source parabolic module supplies the full G.10 hypothesis. Its actual
Sylow image normalizes the actor, and the fixed space is either the marked
line or supplies the required rank-two displacement. Thus every G.11 input
is obtained on the original quotient, without centerlessness.

In dimension four, isotropy and the seed plane force E-hat = V-hat and
rank(X-dot / Z(U)-dot) = 1. The conjugate center fixes V-hat pointwise.
Orbit generation shows that H cannot preserve this plane, proving the
strict inequality H > (H intersect M) C_H(U-hat).

These are the geometric clauses of 14.3.23 and the genuine classification
inputs for 14.3.24, not the exhaustive action alternatives. Nontriviality
of the dotted conjugate center before centerlessness, the action catalogue,
and its marked exclusions remain with qt-d-hs-action-source. The numerical
bound at the end retains precisely that nontriviality premise.

This extension imports the existing rank-three terminal action above
Section04, so consumers import it directly; the lower SourceAction umbrella
does not re-export it. None of its statements assumes centerlessness or the
later natural action.

Source: Aschbacher--Smith, 12.8.11--13 and 14.3.12--14,23--24,
printed pp.854--856,993--994,999--1000.
-/

public section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
private theorem hatSpace_mono (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    {A B : Subgroup G} (h : A ≤ B) : hatSpace F A ≤ hatSpace F B :=
  fun _ hx => (show hatImage F A ≤ hatImage F B from map_mono (comap_mono h)) hx

/-- The isotropic intersection and actor quotient in dimension four, without centerlessness. -/
theorem source_four_marked_geometry (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ hx : IsElementaryAbelian 2 (F.terminalDot (F.X g)), letI := hx
      hatSpace F (F.E g) = hatSpace F V ∧
      finrank (ZMod 2) (hatSpace F (F.E g)) = 2 ∧
      Group.rank ((F.terminalDot (F.X g)) ⧸
        (F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) = 1 := by
  obtain ⟨_, hx, B, v, hyp⟩ := CaseOneLarge.source_terminal_hypothesis F d earlier hq chosen
    structural alternatives hne g hgP hgH
  let := hx
  let := chosen.elementary
  have hVE : hatSpace F V ≤ hatSpace F (F.E g) :=
    hatSpace_mono F (F.seed_le_E_of_normalizes g (F.P_le_seed_normalizer L chosen.normalizes hgP))
  have hv := seed_hat_dimension F (source_closure d earlier hq chosen structural alternatives F hne).2.2
  have he := Submodule.finrank_mono hVE
  have hi := B.twice_finrank_le_of_isotropic hyp.nondegenerate _ hyp.isotropic
  rw [hd] at hi
  have heq : finrank (ZMod 2) (hatSpace F (F.E g)) = 2 := by omega
  have hb := hyp.dimension
  rw [hd, heq] at hb
  exact ⟨hx, (Submodule.eq_of_le_of_finrank_eq hVE (hv.trans heq.symm)).symm, heq, by omega⟩

omit [Finite G] in
/-- The conjugate center fixes the original seed pointwise under the literal dotted action. -/
theorem source_conjugate_center_fixes_seed
    (chosen : ChosenModule T L V) (F : InvariantFlag T V 3)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) :
    ∀ z ∈ F.terminalDot (conjugate F.ZU g), ∀ v ∈ hatSpace F V,
      F.terminalRepresentation z v = v := by
  let := chosen.elementary
  intro z hz v hv
  obtain ⟨a, ha, rfl⟩ := hz
  obtain ⟨w, hw, he⟩ := (show v.toMul ∈ hatImage F V from hv)
  apply Additive.toMul.injective
  rw [F.terminalRepresentation_apply_mk, ← he, F.terminalHatAction_apply_mk]
  congr 1
  apply Subtype.ext
  change (a:G) * (w:G) * (a:G)⁻¹ = (w:G)
  have hc := F.conjugate_center_centralizes_seed g
    (F.P_le_seed_normalizer L chosen.normalizes hgP) ha
  have hc' := (mem_centralizer_iff.mp hc) (w:G) hw
  change (w:G) * (a:G) = (a:G) * (w:G) at hc'
  rw [← hc', mul_assoc, mul_inv_cancel, mul_one]

/-- The whole dotted group cannot preserve the original seed plane. -/
theorem source_seed_hat_not_invariant (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) :
    ¬ ∀ a : F.TerminalHdot, ∀ w ∈ hatSpace F V,
      F.terminalRepresentation a w ∈ hatSpace F V := by
  obtain ⟨g, _, hgP, hgH⟩ := CaseOneLarge.exists_source_conjugator d earlier hq chosen structural F
  obtain ⟨_, hx, B, v, hyp, hline, _⟩ := CaseOneLarge.source_terminal_marked_hypothesis F d earlier hq
    chosen structural alternatives hne g hgP hgH
  let := chosen.elementary
  let := hx
  obtain ⟨htwo, hphi, hvc⟩ := source_closure d earlier hq chosen structural alternatives F hne
  have hdim := (quotient_dimension F htwo hphi hvc).1
  have hv := seed_hat_dimension F hvc
  intro hstable
  let S : Subrepresentation F.terminalRepresentation := ⟨hatSpace F V, fun a _ hw => hstable a _ hw⟩
  have hproper : S.toSubmodule ≠ ⊤ := by
    intro he
    have hh : finrank (ZMod 2) (hatSpace F V) = finrank (ZMod 2) (Additive F.Uhat) := by
      rw [show hatSpace F V = ⊤ from he, finrank_top]
    omega
  apply hyp.point_not_mem S hproper
  exact hatSpace_mono F (F.le_seed 2) (hline ▸ Submodule.mem_span_singleton_self v)

/-- The actual intersection with M has proper image in the dotted group (14.3.23(4)). -/
theorem source_dotted_intersection_ne_top (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) :
    F.terminalDot (F.H ⊓ normalizer (L : Set G)) ≠ ⊤ := by
  let := chosen.elementary
  have unique : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro X _ _ hX S A hA
    exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hX S hA
  have hpoint : F.Vi 1 ≠ ⊥ := by
    intro he
    have hc := F.card 1 (by decide)
    rw [he, card_bot] at hc
    norm_num at hc
  have hm := intersection_normalizer d earlier hq chosen ⟨structural, unique, alternatives⟩
    (F.Vi 1) F.H hpoint (F.le_seed 1) le_rfl
  intro htop
  apply source_seed_hat_not_invariant d earlier hq chosen structural alternatives F hne
  intro a w hw
  obtain ⟨b, hb, rfl⟩ := (show a ∈ F.terminalDot (F.H ⊓ normalizer (L : Set G)) by rw [htop]; trivial)
  have hn : (b:G) ∈ normalizer (V : Set G) := (hm ▸ hb).2
  obtain ⟨c, hc, he⟩ := (show w.toMul ∈ hatImage F V from hw)
  refine ⟨F.uAction b c, (mem_normalizer_iff.mp hn (c:G)).mp hc, ?_⟩
  change QuotientGroup.mk' (center F.U) (F.uAction b c) = F.terminalHatAction b w.toMul
  change QuotientGroup.mk' (center F.U) (F.uAction b c) = F.uhatAction b w.toMul
  rw [← F.uhatAction_apply_mk, he]


/-- The earlier rank-three actor is normal in the image of the original Sylow,
without any assertion that the action kernel equals the two-core. -/
theorem source_earlier_actor_normal_in_sylow (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
      (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
    F.terminalDot (F.X g) ≤ (P : Subgroup F.TerminalHdot) ∧
      ((F.terminalDot (F.X g)).subgroupOf (P : Subgroup F.TerminalHdot)).Normal := by
  let := chosen.elementary
  let : IsElementaryAbelian 2 (F.Vi 2) := IsElementaryAbelian.of_injective
    (inclusion (F.le_seed 2)) (inclusion_injective _)
  let h := higherRankHypothesis d earlier hq chosen
  obtain ⟨hcomm, hsquare⟩ := CaseOneLarge.source_commutator_squares d earlier hq chosen structural alternatives F
  have hspan := (source_seed_geometry d earlier hq chosen F).2.1
  obtain ⟨e, _, hgen, _, hIG, hIN, _, _, hfactor, hPH, hcore, hindex, _⟩ :=
    F.binary_generation (by decide) L chosen.normalizes (h.binarySeedAction_surjective F)
      (h.centralizer_LT structural) hcomm hsquare hspan hne g hgP hgH
  have hcore' := F.binary_core_factorization L g hgP hfactor hPH hgen.symm e hcore hindex
  obtain ⟨z, hz, hzp⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  exact Xdot_normal_in_Tdot F (by decide) z hzp hz
    (F.binary_point_commutator (by decide) hcomm hindex) L g
    (F.P_le_G₂ (by decide) L chosen.normalizes hgP) hIG
    ((normal_subgroupOf_iff_le_normalizer hIG).mp hIN) hcore'
    F.terminalHatAction F.terminalHatAction_apply_mk

omit [Finite G] in
private theorem marked_form_zero (F : InvariantFlag T V 3)
    [IsElementaryAbelian 2 F.Uhat]
    (hcomm : ⁅F.U,F.U⁆ ≤ F.Vi 1) (B : F.UhatCommutatorForm hcomm) (a b : F.U) :
    B.form (hatElement F a) (hatElement F b) = 0 ↔ Commute a b := by
  rw [show B.form (hatElement F a) (hatElement F b) =
    (B.valueEquiv ⟨⁅(a:G),(b:G)⁆,hcomm (commutator_mem_commutator a.property b.property)⟩).toAdd
      from B.evaluation a b]
  change B.valueEquiv _ = 1 ↔ _
  rw [map_eq_one_iff B.valueEquiv B.valueEquiv.injective,Subtype.ext_iff]
  exact commutatorElement_eq_one_iff_mul_comm.trans (by
    change (a:G)*(b:G)=(b:G)*(a:G) ↔ a*b=b*a
    constructor
    · intro h
      exact Subtype.ext h
    · intro h
      exact congrArg (fun t : F.U => (t:G)) h)

private theorem source_parabolic_displacement (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∀ u ∈ F.U, u ∉ F.W → ∀ w ∈ F.W,
      ∃ x ∈ F.X g, ∃ e ∈ F.E g, ⁅x,u⁆ * e = w := by
  let := chosen.elementary
  let h := higherRankHypothesis d earlier hq chosen
  obtain ⟨hcomm, hsquare⟩ := CaseOneLarge.source_commutator_squares d earlier hq chosen structural alternatives F
  have hspan := (source_seed_geometry d earlier hq chosen F).2.1
  obtain ⟨ι, ⟨N⟩⟩ := F.binary_source_parabolic_natural_module (by decide) L chosen.normalizes
    (h.binarySeedAction_surjective F) (h.centralizer_LT structural) hcomm hsquare hspan hne g hgP hgH
  obtain ⟨_, _, hgen, _⟩ := F.binary_generation (by decide) L chosen.normalizes
    (h.binarySeedAction_surjective F) (h.centralizer_LT structural) hcomm hsquare hspan hne g hgP hgH
  have hnE := F.binary_source_E_normalized L chosen.normalizes g hgP hgen.symm hcomm
  let : ((F.E g).subgroupOf F.W).Normal := normal_subgroupOf_of_le_normalizer
    ((show F.W ≤ F.I₂ L from inf_le_left.trans (le_conjugateSpanBy _ _)).trans hnE)
  intro u hu huw w hw
  let uU : F.U := ⟨u, hu⟩
  have hcm : ∀ x ∈ F.X g, ⁅x,u⁆ ∈ F.W := fun x hx =>
    N.commutator_mem_W uU huw x ((le_sup_right : F.X g ≤ F.W ⊔ F.X g) hx)
  obtain ⟨x, hx⟩ := F.parabolicCommutator_natural_surjective L g N uU huw hcm
    N.commutator_core_le (QuotientGroup.mk' ((F.E g).subgroupOf F.W) ⟨w, hw⟩)
  have he : ⁅(x:G),u⁆⁻¹ * w ∈ F.E g := by
    change (⟨⁅(x:G),u⁆, hcm x x.property⟩ : F.W)⁻¹ * ⟨w,hw⟩ ∈ (F.E g).subgroupOf F.W
    rw [← QuotientGroup.ker_mk' ((F.E g).subgroupOf F.W)]
    exact (MonoidHom.eq_iff (QuotientGroup.mk' ((F.E g).subgroupOf F.W))).mp hx.symm
  exact ⟨x, x.property, _, he, mul_inv_cancel_left _ _⟩

private theorem source_fixed_point_alternative (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (v : Additive F.Uhat) (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2)) :
    Representation.BinaryOffender.fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) =
        Submodule.span (ZMod 2) {v} ∨
      ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)) := by
  let := chosen.elementary
  let h := higherRankHypothesis d earlier hq chosen
  let c := CaseOneLarge.source_closure_geometry F d earlier hq chosen structural alternatives hne
  let : IsElementaryAbelian 2 (F.Vi 2) := IsElementaryAbelian.of_injective
    (inclusion (F.le_seed 2)) (inclusion_injective _)
  obtain ⟨hcomm, hsquare⟩ := CaseOneLarge.source_commutator_squares d earlier hq chosen structural alternatives F
  have hspan := (source_seed_geometry d earlier hq chosen F).2.1
  have hg := F.P_le_G₂ (by decide) L chosen.normalizes hgP
  obtain ⟨e, _, _, _, hIG, _, _, _, _, _, _, hindex, heval⟩ :=
    F.binary_generation (by decide) L chosen.normalizes (h.binarySeedAction_surjective F)
      (h.centralizer_LT structural) hcomm hsquare hspan hne g hgP hgH
  let C := F.localKernel_markedForm (by decide) c.two c.frattini_point hcomm
  have hC := marked_form_zero F hcomm C
  have hdis := disjoint_iff.mpr (F.parabolic_displaced_centers (by decide) L chosen.normalizes
    c.seed_center g hgP hgH).1
  have hcuts := source_center_intersections d earlier hq chosen structural alternatives F hne g hgP hgH
  have hc : F.ZU ⊓ conjugate F.U g = (F.ZU ⊓ conjugate F.ZU g) ⊔ F.Vi 1 := by
    rw [hcuts.1]; exact hcuts.2.1
  have hcg : conjugate F.ZU g ⊓ F.U = (F.ZU ⊓ conjugate F.ZU g) ⊔ conjugate (F.Vi 1) g := by
    rw [hcuts.1]; exact hcuts.2.2
  have hfour : hatSpace F (F.E g) ⊓ XfixedSpace F F.terminalHatAction g = hatSpace F (F.Vi 2) :=
    EhatFixed_eq_plane F g hg hcomm hdis hc hcg C.form hC C.nondegenerate C.alternating.isRefl
  have hfix : Representation.BinaryOffender.fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) =
      XfixedSpace F F.terminalHatAction g := by
    ext w
    simp only [XfixedSpace, Submodule.mem_iInf, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    rfl
  by_cases heq : Representation.BinaryOffender.fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) =
      Submodule.span (ZMod 2) {v}
  · exact Or.inl heq
  right
  have hstrict : hatSpace F (F.Vi 2) < XfixedSpace F F.terminalHatAction g := by
    apply lt_of_le_of_ne (hfour ▸ inf_le_right)
    intro he
    exact heq (hfix.trans (he.symm.trans hline.symm))
  have hPhi : (frattini F.U).map F.U.subtype = F.Vi 1 := by
    rw [c.frattini_point]
    exact map_subgroupOf_eq_of_le ((F.le_seed 1).trans (le_conjugateSpanBy _ _))
  have hfull : Function.Surjective ((F.Vi 2).normalizerMonoidHom.comp (inclusion hIG)) := by
    intro α
    obtain ⟨i, hi⟩ := QuotientGroup.mk'_surjective (pCore 2 (F.I₂ L))
      (e.symm (F.binaryPlaneLabel (by decide) α))
    refine ⟨i, ?_⟩
    ext w
    change (i:G)*(w:G)*(i:G)⁻¹ = (α w:G)
    rw [← heval i w]
    change ((F.binaryPlaneLabel (by decide)).symm (e (QuotientGroup.mk' _ i)) w : G) = _
    rw [hi, e.apply_symm_apply, MulEquiv.symm_apply_apply]
  obtain ⟨z, hz, hzp⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  have hi : ∀ (b : F.H) (u w : F.Uhat),
      C.form (Additive.ofMul (F.terminalHatAction b u)) (Additive.ofMul (F.terminalHatAction b w)) =
        C.form (Additive.ofMul u) (Additive.ofMul w) := by
    change ∀ b u w, F.uhatBilinearForm (by decide) c.two c.frattini_point
      (Additive.ofMul (F.uhatAction b u)) (Additive.ofMul (F.uhatAction b w)) = _
    intro b u w
    rw [F.uhatBilinearForm_apply, F.uhatCommutator_invariant (by decide) c.two c.frattini_point]
    rfl
  obtain ⟨x, hx, _, hr, hm⟩ := exists_lowRank_of_fixedSpace_lt F (by decide) hne
    c.two hPhi c.seed_center L g hg hdis z hzp hz hIG hfull F.terminalHatAction
    F.terminalHatAction_apply_mk
    (F.binary_source_action_kernel_intersections (by decide) L chosen.normalizes
      (h.binarySeedAction_surjective F) (h.centralizer_LT structural) hcomm hsquare hspan hne
      c.seed_center g hgP hgH).1 hindex
    (source_parabolic_displacement d earlier hq chosen structural alternatives F hne g hgP hgH)
    hc C.form C.nondegenerate C.alternating hC hi hfour hstrict
  exact ⟨x, hx, hr, hm (hline ▸ Submodule.mem_span_singleton_self v)⟩


/-- Every G.11 input on the original rank-three flag is supplied by the earlier
source geometry. In particular both fixed-space alternatives and the literal
Sylow normality are retained, independently of centerlessness. -/
theorem source_earlier_classification_input (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ heU : IsElementaryAbelian 2 F.Uhat, letI := heU
    ∃ heX : IsElementaryAbelian 2 (F.terminalDot (F.X g)), letI := heX
    ∃ (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat),
      ChapterG.Section10.Hypothesis F.terminalRepresentation B v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g))
        ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) ∧
      Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2) ∧
      Nonempty (ChapterG.Section09.SQTKCover KnownSimple.IsKnownSimple F.TerminalHdot) ∧
      ChapterG.Section11.NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      (Representation.BinaryOffender.fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) =
          Submodule.span (ZMod 2) {v} ∨
        ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g))) := by
  obtain ⟨heU, heX, B, v, hyp, hline, hfix⟩ :=
    CaseOneLarge.source_terminal_marked_hypothesis F d earlier hq chosen structural alternatives hne g hgP hgH
  let := heU
  let := heX
  have hn := source_earlier_actor_normal_in_sylow d earlier hq chosen structural alternatives F hne g hgP hgH
  refine ⟨heU, heX, B, v, hyp, hline, CaseOneLarge.source_terminal_cover F d chosen,
    ⟨_, ?_, hn⟩, source_fixed_point_alternative d earlier hq chosen structural alternatives F hne g hgP hgH v hline⟩
  exact hfix

/-- A nontrivial smaller actor gives the earlier half-degree bound. This uses
its actual image, without identifying it with the tilded center. -/
theorem source_dimension_le_twice_actor_of_dot_center_ne_bot (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (g : G) [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hne : ¬ IsMulCommutative F.U) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (hZ : F.terminalDot (conjugate F.ZU g) ≠ ⊥) :
    finrank (ZMod 2) (Additive F.Uhat) ≤
      2 * finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) := by
  obtain ⟨_, hx, B, v, hyp⟩ := CaseOneLarge.source_terminal_hypothesis F d earlier hq chosen
    structural alternatives hne g hgP hgH
  apply hyp.dimension_le_twice_actor_of_smaller_ne_bot
  intro hb
  have hh := congrArg (fun A : Subgroup (F.terminalDot (F.X g)) =>
    A.map (F.terminalDot (F.X g)).subtype) hb
  have hle : F.terminalDot (conjugate F.ZU g) ≤ F.terminalDot (F.X g) :=
    map_mono (comap_mono (F.conjugate_ZU_le_X g))
  exact hZ (by simpa only [map_subgroupOf_eq_of_le hle, Subgroup.map_bot] using hh)


/-- The strict subgroup inequality in 14.3.23(4), using the original
centralizer kernel inside H. -/
theorem source_intersection_kernel_lt (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) :
    (F.H ⊓ normalizer (L : Set G)) ⊔ F.uhatAction.ker.map F.H.subtype < F.H := by
  have hle : (F.H ⊓ normalizer (L : Set G)) ⊔ F.uhatAction.ker.map F.H.subtype ≤ F.H :=
    sup_le inf_le_left (map_subtype_le _)
  apply lt_of_le_of_ne hle
  intro heq
  apply source_dotted_intersection_ne_top d earlier hq chosen structural alternatives F hne
  have he := congrArg (F.terminalDot) heq
  have hk : ((F.uhatAction.ker.map F.H.subtype).subgroupOf F.H).map
      (QuotientGroup.mk' F.terminalHatAction.ker) = ⊥ := by
    rw [subgroupOf, comap_map_eq_self_of_injective F.H.subtype_injective]
    apply le_bot_iff.mp
    rw [map_le_iff_le_comap, MonoidHom.comap_bot, QuotientGroup.ker_mk']
    rfl
  unfold terminalDot at he
  rw [subgroupOf_sup inf_le_left (map_subtype_le _), Subgroup.map_sup, hk, sup_bot_eq,
    subgroupOf_self, map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at he
  exact he

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS
