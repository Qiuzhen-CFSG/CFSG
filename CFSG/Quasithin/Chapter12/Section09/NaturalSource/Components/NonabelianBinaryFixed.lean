module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianFixed
public import Theory.GroupAction.TwoGroupFourFactors

/-!
# The binary-fixed plane and the original Sylow action

Put D = C_I(Z(U)^g) and E = V₂D, using the same natural constituent
constructed in NonabelianFixed. The returning-center calculation puts D
inside Z(I₂)V₁. Thus E splits as the direct product of V₂ and its actual
I₂-fixed subgroup A = E intersect Z(I₂), of order four. The plane is fully
moved by I₂. Consequently the action on E has exactly the original
O₂(I₂) kernel and the marked S₃ quotient; the action on A is trivial.
The subgroup A lies in Z(U), and D lies in AV₁.

The original T preserves V₂ and D separately. The general four-factor
action bound makes its image have order at most four and exponent two.
Since T lies in Y = ⟨P,I₂⟩ and Y preserves E, Sylow conjugacy proves that
an element of Y whose fourth power centralizes E already has its square
centralizing E. The last theorem constructs all these data on the same
flag, with the restricted P = P₀ intersect K₁T and original quotient maps.

The comparison of the two actions in common four-space coordinates, the
ambient contradiction, catalogue exhaustion and LocalControlInput remain
with source assembly. No equality D = A or D = [I,Z(U)^g] is assumed or
asserted. The genuine guarded module theorem and NaturalReduction 4 are
retained as their original explicit inputs.

Source: Aschbacher--Smith, proof of 12.9.4, printed p.860 of
refs/quasithin.pdf, with the restricted component lift of P₀.
-/

public noncomputable section
open Subgroup Module Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag Section08.InvariantFlag.Symplectic
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

omit [Finite G] in
private theorem subgroup_centralizer_eq_center (A : Subgroup G) :
    A ⊓ centralizer (A : Set G) = Section08.centerIn A := by
  ext x
  constructor
  · rintro ⟨hx,hc⟩
    exact ⟨⟨x,hx⟩,mem_center_iff.mpr (fun a => Subtype.ext (hc a a.property)),rfl⟩
  · rintro ⟨x,hx,rfl⟩
    exact ⟨x.property,fun a ha => congrArg Subtype.val (mem_center_iff.mp hx ⟨a,ha⟩)⟩

/-- The original binary span moves the entire plane. -/
theorem nonabelian_plane_commutator_binary
    {K : GroupClass.{u}} (h : HigherRankHypothesis K T L V n)
    (earlier : EarlierSetupResults.{u} K) (F : InvariantFlag T V n)
    (hne : ¬ IsMulCommutative F.U) (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ⁅F.Vi 2,F.I₂ L⁆ = F.Vi 2 := by
  let := h.chosen.elementary
  let := F.localKernel_tilde_seed_elementary
  have hn : 2 ≤ n := by have := h.rank; omega
  have hVU : F.Vi 2 ≤ F.U := (F.le_seed 2).trans (le_conjugateSpanBy V F.H)
  have hUI : F.U ≤ F.I₂ L := le_conjugateSpanBy _ _
  have hc := (F.localKernel_commutator_squares h.source.simpleQTKE L _ hn
    h.chosen.le_sylow h.chosen.normalizes (h.sylow_normalizes earlier.structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩) (h.flag_escape F earlier.alternatives)).1
  have hcenter := F.seed_inf_center_eq_point_of_ambient_natural h.naturalMarking h.rank.1 hne
  have hJpoint : ⁅F.Vi 2,F.U⁆ ≤ F.Vi 1 := (commutator_mono hVU le_rfl).trans hc
  have hJne : ⁅F.Vi 2,F.U⁆ ≠ ⊥ := by
    intro hz
    have hVZ : F.Vi 2 ≤ F.ZU := by
      change F.Vi 2 ≤ Section08.centerIn F.U
      rw [←subgroup_centralizer_eq_center]
      exact le_inf hVU (commutator_eq_bot_iff_le_centralizer.mp hz)
    have hle : F.Vi 2 ≤ F.Vi 1 := hcenter ▸ le_inf (F.le_seed 2) hVZ
    have hh := card_le_of_le hle
    rw [F.card 2 hn,F.card 1 (by omega)] at hh
    norm_num at hh
  have hJ : ⁅F.Vi 2,F.U⁆ = F.Vi 1 := by
    apply eq_of_le_of_card_ge hJpoint
    have hh := (one_lt_card_iff_ne_bot _).mpr hJne
    rw [F.card 1 (by omega)]
    norm_num at ⊢
    omega
  have hUG : F.U ≤ F.Gi 2 := F.U_le_G₂_of_commutator hc
  have hIG : F.I₂ L ≤ F.Gi 2 := conjugateSpanBy_le hUG
    ((F.P_le_G₂ hn L h.chosen.normalizes).trans (F.Gi 2).le_normalizer)
  have hPJ : F.P L ≤ normalizer ((⁅F.Vi 2,F.I₂ L⁆ : Subgroup G) : Set G) := by
    intro a ha
    have hNI : a ∈ normalizer (F.I₂ L : Set G) := le_normalizer_conjugateSpanBy F.U (F.P L) ha
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (F.P_le_G₂ hn L h.chosen.normalizes ha),
      mem_normalizer_iff_map_conj_eq.mp hNI]
  have hpoint : F.Vi 1 ≤ ⁅F.Vi 2,F.I₂ L⁆ := hJ ▸ commutator_mono le_rfl hUI
  apply le_antisymm (le_normalizer_iff_commutator_le_left.mp hIG)
  calc
    F.Vi 2 = F.Vi 1 ⊔ conjugate (F.Vi 1) g :=
      F.plane_eq_point_join_conjugate hn L h.chosen.normalizes g hgP hgH
    _ ≤ ⁅F.Vi 2,F.I₂ L⁆ := sup_le hpoint (conjugate_le_of_normalizes hpoint g (hPJ hgP))

/-- The binary center is disjoint from the same original plane. -/
theorem nonabelian_plane_disjoint_binary_center
    {K : GroupClass.{u}} (h : HigherRankHypothesis K T L V n)
    (earlier : EarlierSetupResults.{u} K) (F : InvariantFlag T V n)
    (hne : ¬ IsMulCommutative F.U) [IsElementaryAbelian 2 F.Uhat]
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    Disjoint (F.Vi 2) (Section08.centerIn (F.I₂ L)) := by
  let := h.chosen.elementary
  let := F.localKernel_tilde_seed_elementary
  have he := (nonabelian_center_intersection_and_kernel h earlier F hne g hgP hgH).1
  have hcenter := F.seed_inf_center_eq_point_of_ambient_natural h.naturalMarking h.rank.1 hne
  have hd := F.point_inf_conjugate_ZU (by have := h.rank; omega) hcenter g
    (F.P_le_seed_normalizer L h.chosen.normalizes hgP) hgH
  apply disjoint_iff.mpr
  apply bot_unique
  rintro x ⟨hx,hz⟩
  rw [←he] at hz
  exact hd.le ⟨hcenter ▸ (show x ∈ V ⊓ F.ZU from ⟨F.le_seed 2 hx,hz.1⟩),hz.2⟩

/-- The same sixteen-group has a canonical binary-fixed complement. -/
theorem nonabelian_caseFive_binary_fixed_complement
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B)
    (C : ComponentGeometry F L) {I : Subgroup G} (c : ChosenModule T C.K1 I)
    (hnatural : NaturalModule c 4) (hiZ : I ≤ F.ZU)
    (hD : Nat.card (I ⊓ centralizer (conjugate F.ZU g : Set G) : Subgroup G) = 4) :
    let E := F.Vi 2 ⊔ (I ⊓ centralizer (conjugate F.ZU g : Set G))
    let A := E ⊓ Section08.centerIn (F.I₂ L)
    E = F.Vi 2 ⊔ A ∧ Disjoint (F.Vi 2) A ∧ Nat.card A = 4 ∧
      E ⊓ centralizer (F.I₂ L : Set G) = A ∧ ⁅E,F.I₂ L⁆ = F.Vi 2 := by
  let E := F.Vi 2 ⊔ (I ⊓ centralizer (conjugate F.ZU g : Set G))
  let Z := Section08.centerIn (F.I₂ L)
  let A := E ⊓ Z
  have hVE : F.Vi 2 ≤ E := le_sup_left
  have hVZ : Disjoint (F.Vi 2) Z := nonabelian_plane_disjoint_binary_center h earlier F hne g hgP hgH
  have hEC : E ≤ F.Vi 2 ⊔ Z := by
    refine sup_le le_sup_left ?_
    have hh : I ⊓ centralizer (conjugate F.ZU g : Set G) ≤ Z ⊔ F.Vi 1 := by
      dsimp only [Z]
      rw [←(nonabelian_center_intersection_and_kernel h earlier F hne g hgP hgH).1,
        ←nonabelian_caseFive_center_centralizer h (.inl rfl) earlier F hne g hgP hgH B h5]
      exact inf_le_inf_right _ hiZ
    exact hh.trans (sup_le le_sup_right ((F.monotone (by decide : 1 ≤ 2)).trans le_sup_left))
  have hVZcomm : F.Vi 2 ≤ centralizer (Z : Set G) := by
    exact le_centralizer_iff.mp ((centerIn_le_centralizer _).trans
      (centralizer_le (((F.le_seed 2).trans (le_conjugateSpanBy V F.H)).trans
        (le_conjugateSpanBy F.U (F.P L)))))
  have hsplit : E = F.Vi 2 ⊔ A := by
    apply le_antisymm ?_ (sup_le hVE inf_le_left)
    intro x hx
    have hm : x ∈ (F.Vi 2 : Set G) * (Z : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left _ _
        ((le_centralizer_iff.mp hVZcomm).trans (Subgroup.centralizer_le_normalizer _))]
      exact hEC hx
    obtain ⟨v,hv,z,hz,rfl⟩ := hm
    have hzE : z ∈ E := by
      have hh := E.mul_mem (E.inv_mem (hVE hv)) hx
      simpa only [inv_mul_cancel_left] using hh
    exact mul_mem (mem_sup_left hv) (mem_sup_right ⟨hzE,hz⟩)
  have hd : Disjoint (F.Vi 2) A := hVZ.mono_right inf_le_right
  have hAc : Nat.card A = 4 := by
    have hprod := card_sup_eq_mul_of_normalizes_of_disjoint (F.Vi 2) A
      ((inf_le_right.trans (le_centralizer_iff.mp hVZcomm)).trans
        (Subgroup.centralizer_le_normalizer _)) hd
    rw [←hsplit,F.card 2 (by decide)] at hprod
    have hEc := (nonabelian_caseFive_plane_extension_card h F hne C c hnatural hiZ
      (show I ⊓ centralizer (conjugate F.ZU g : Set G) ≤ I from inf_le_left)).2
    rw [hD] at hEc
    change Nat.card E = 4 * 4 at hEc
    omega
  have hEI : E ≤ F.I₂ L := (sup_le
    ((F.le_seed 2).trans (le_conjugateSpanBy V F.H))
    ((inf_le_left.trans hiZ).trans (map_subtype_le _))).trans
      (le_conjugateSpanBy F.U (F.P L))
  have hefix : E ⊓ centralizer (F.I₂ L : Set G) = A := by
    rw [show A = E ⊓ Z from rfl,show Z = F.I₂ L ⊓ centralizer (F.I₂ L : Set G)
      from (subgroup_centralizer_eq_center _).symm,←inf_assoc,inf_eq_left.mpr hEI]
  refine ⟨hsplit,hd,hAc,hefix,le_antisymm ?_ ?_⟩
  · exact (nonabelian_caseFive_returning_fixed_extension h (.inl rfl) earlier F hne g hgP hgH B h5 hiZ).1
  · exact (nonabelian_plane_commutator_binary h earlier F hne g hgP hgH).ge.trans
      (commutator_mono hVE le_rfl)


/-- Adjoining a binary-fixed factor does not enlarge the original action
kernel: it remains precisely O₂(I₂), with the same S₃ quotient marking. -/
theorem nonabelian_binary_extension_kernel
    {K : GroupClass.{u}} (h : HigherRankHypothesis K T L V n)
    (earlier : EarlierSetupResults.{u} K) (F : InvariantFlag T V n)
    (hne : ¬ IsMulCommutative F.U) (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    {E : Subgroup G} (hsplit : E = F.Vi 2 ⊔ (E ⊓ Section08.centerIn (F.I₂ L))) :
    let := h.chosen.elementary
    F.I₂ L ⊓ centralizer (E : Set G) = (F.I₂ L).pCoreIn 2 ∧
      ∃ e : ((F.I₂ L) ⧸ pCore 2 (F.I₂ L)) ≃* Equiv.Perm (Fin 3),
        ∀ (x : F.I₂ L) (v : F.Vi 2) (a : (E ⊓ Section08.centerIn (F.I₂ L) : Subgroup G)),
          (x:G) * ((v:G) * (a:G)) * (x:G)⁻¹ =
            ((F.binaryPlaneLabel (by have := h.rank; omega)).symm
              (e (QuotientGroup.mk x)) v : G) * (a:G) := by
  let := h.chosen.elementary
  let := F.localKernel_tilde_seed_elementary
  have hn : 2 ≤ n := by have := h.rank; omega
  obtain ⟨hc,hs⟩ := F.localKernel_commutator_squares h.source.simpleQTKE L _ hn
    h.chosen.le_sylow h.chosen.normalizes (h.sylow_normalizes earlier.structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩) (h.flag_escape F earlier.alternatives)
  have hspan := F.U_eq_plane_span L hn h.chosen.normalizes
    (F.localKernel_irreducible L hn h.chosen.normalizes (fun _ => ⟨h.naturalMarking⟩))
  obtain ⟨e,_,_,_,_,_,_,_,_,_,hcore,_,he⟩ := F.binary_generation hn L
    h.chosen.normalizes (h.binarySeedAction_surjective F) (h.centralizer_LT earlier.structural)
    hc hs hspan hne g hgP hgH
  have hVE : F.Vi 2 ≤ E := by rw [hsplit]; exact le_sup_left
  have hfix : F.I₂ L ⊓ centralizer (F.Vi 2 : Set G) ≤ centralizer (E : Set G) := by
    apply le_centralizer_iff.mpr
    rw [hsplit]
    exact sup_le (le_centralizer_iff.mp inf_le_right)
      ((inf_le_right.trans (centerIn_le_centralizer _)).trans (centralizer_le inf_le_left))
  refine ⟨(le_antisymm (inf_le_inf_left _ (centralizer_le hVE))
    (le_inf inf_le_left hfix)).trans hcore,e,?_⟩
  intro x v a
  rw [he]
  have hax : (x:G) * (a:G) * (x:G)⁻¹ = (a:G) :=
    mul_inv_eq_iff_eq_mul.mpr ((centerIn_le_centralizer _ a.property.2) x x.property)
  calc
    _ = ((x:G) * (v:G) * (x:G)⁻¹) * ((x:G) * (a:G) * (x:G)⁻¹) := by group
    _ = _ := by rw [hax]

/-- The binary-fixed complement lies in the original center, and the
returning fixed four-group is contained in it times the original point. -/
theorem nonabelian_caseFive_binary_fixed_placement
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B)
    {I : Subgroup G} (hiZ : I ≤ F.ZU) :
    let D := I ⊓ centralizer (conjugate F.ZU g : Set G)
    let E := F.Vi 2 ⊔ D
    let A := E ⊓ Section08.centerIn (F.I₂ L)
    A ≤ F.ZU ∧ D ≤ A ⊔ F.Vi 1 := by
  let D := I ⊓ centralizer (conjugate F.ZU g : Set G)
  let E := F.Vi 2 ⊔ D
  let Z := Section08.centerIn (F.I₂ L)
  let A := E ⊓ Z
  have hZZ : Z ≤ F.ZU := by
    dsimp only [Z]
    rw [←(nonabelian_center_intersection_and_kernel h earlier F hne g hgP hgH).1]
    exact inf_le_left
  have hDZ : D ≤ Z ⊔ F.Vi 1 := by
    dsimp only [Z]
    rw [←(nonabelian_center_intersection_and_kernel h earlier F hne g hgP hgH).1,
      ←nonabelian_caseFive_center_centralizer h (.inl rfl) earlier F hne g hgP hgH B h5]
    exact inf_le_inf_right _ hiZ
  have hpointE : F.Vi 1 ≤ E := (F.monotone (by decide : 1 ≤ 2)).trans le_sup_left
  have hn : F.Vi 1 ≤ normalizer (Z : Set G) := by
    exact (((F.le_seed 1).trans (le_conjugateSpanBy V F.H)).trans
      (le_conjugateSpanBy F.U (F.P L))).trans
        ((le_centralizer_iff.mp (centerIn_le_centralizer _)).trans (Subgroup.centralizer_le_normalizer _))
  refine ⟨inf_le_right.trans hZZ,?_⟩
  intro d hd
  have hm : d ∈ (Z : Set G) * (F.Vi 1 : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left _ _ hn]
    exact hDZ hd
  obtain ⟨z,hz,v,hv,rfl⟩ := hm
  have hzE : z ∈ E := by
    have hh := E.mul_mem (show z*v ∈ E from mem_sup_right hd) (E.inv_mem (hpointE hv))
    simpa only [mul_inv_cancel_right] using hh
  exact mul_mem (mem_sup_left ⟨hzE,hz⟩) (mem_sup_right hv)

/-- Both fixed planes are now constructed on the same source flag. The
joined actor preserves E, and its original Sylow preserves V₂ and D
separately. The binary action on E has exactly the original two-core kernel.
Equality of D with the binary-fixed plane A remains an ambient obligation. -/
theorem nonabelian_caseFive_natural_binary_geometry
    (modules : Theorem1222ModulesOfMany.{u} KnownSimple.IsKnownSimple)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (preferred : PreferredDimension KnownSimple.IsKnownSimple T 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (four : NaturalReduction KnownSimple.IsKnownSimple.{u} 4)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B) :
    ∃ (v : Additive F.Uhat) (C : ComponentGeometry F L) (I : Subgroup G)
      (c : ChosenModule T C.K1 I),
      v ≠ 0 ∧ hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v} ∧
      NaturalModule c 4 ∧ I ≤ F.ZU ∧ I = ⁅F.ZU,C.K1⁆ ∧
      let D := I ⊓ centralizer (conjugate F.ZU g : Set G)
      let E := F.Vi 2 ⊔ D
      let A := E ⊓ Section08.centerIn (F.I₂ L)
      let P := componentPlanePreimage F C v
      Nat.card D = 4 ∧ IsElementaryAbelian 2 E ∧ Nat.card E = 16 ∧
      Disjoint (F.Vi 2) D ∧ P ≤ normalizer (D : Set G) ∧
      ⁅E,componentPlaneResidual F C v⁆ = D ∧
      (∀ J : Subgroup G, J ≤ D → componentPlaneResidual F C v ≤ normalizer (J : Set G) →
        J = ⊥ ∨ J = D) ∧
      E = F.Vi 2 ⊔ A ∧ Disjoint (F.Vi 2) A ∧ Nat.card A = 4 ∧
      E ⊓ centralizer (F.I₂ L : Set G) = A ∧ A ≤ F.ZU ∧ D ≤ A ⊔ F.Vi 1 ∧
      ⁅E,F.I₂ L⁆ = F.Vi 2 ∧
      F.I₂ L ⊓ centralizer (E : Set G) = (F.I₂ L).pCoreIn 2 ∧
      P ⊔ F.I₂ L ≤ normalizer (E : Set G) ∧
      (T : Subgroup G) ≤ P ⊔ F.I₂ L ∧
      (T : Subgroup G) ≤ normalizer (F.Vi 2 : Set G) ⊓ normalizer (D : Set G) ∧
      (centralizer (E : Set G)).relIndex (T : Subgroup G) ≤ 4 ∧
      (∀ t ∈ (T : Subgroup G), t ^ 2 ∈ centralizer (E : Set G)) ∧
      (∀ y ∈ P ⊔ F.I₂ L, y ^ 4 ∈ centralizer (E : Set G) →
        y ^ 2 ∈ centralizer (E : Set G)) ∧
      ¬ P ≤ F.Gi 2 := by
  obtain ⟨v,C,I,c,hv,hline,hnat,hiZ,hi,_,_,hcD,hE,hcE,hd,hPD,hPE,hRD,hirr,_,hIE,hnot⟩ :=
    nonabelian_caseFive_natural_fixed_geometry modules h preferred earlier four
      F hne g hgP hgH B h5
  obtain ⟨hsplit,hdis,hcA,hfix,hmove⟩ := nonabelian_caseFive_binary_fixed_complement
    h earlier F hne g hgP hgH B h5 C c hnat hiZ hcD
  obtain ⟨hAZ,hDA⟩ := nonabelian_caseFive_binary_fixed_placement
    h earlier F hne g hgP hgH B h5 hiZ
  have hTP : (T : Subgroup G) ≤ componentPlanePreimage F C v :=
    le_sup_right.trans (componentPlanePreimage_contains F C v hv hline)
  have hsmall := two_group_four_factors_action (T : Subgroup G) (F.Vi 2)
    (I ⊓ centralizer (conjugate F.ZU g : Set G)) T.isPGroup'
    (by simpa using F.card 2 (by decide)) hcD (F.invariant 2) (hTP.trans hPD)
  refine ⟨v,C,I,c,hv,hline,hnat,hiZ,hi,hcD,hE,hcE,hd,hPD,hRD,hirr,
    hsplit,hdis,hcA,hfix,hAZ,hDA,hmove,?_,sup_le hPE hIE,hTP.trans le_sup_left,
    le_inf (F.invariant 2) (hTP.trans hPD),hsmall.1,hsmall.2,?_,hnot⟩
  · exact (nonabelian_binary_extension_kernel h earlier F hne g hgP hgH hsplit).1
  · exact fourth_power_centralizes_implies_square T _ _
      (hTP.trans le_sup_left) (sup_le hPE hIE) hsmall.2

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
