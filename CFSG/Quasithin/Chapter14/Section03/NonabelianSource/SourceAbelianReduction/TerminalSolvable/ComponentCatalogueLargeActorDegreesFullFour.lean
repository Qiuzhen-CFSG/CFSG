module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueLargeActorDegreesSymplectic
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationStrictExceptionalGeometry
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.CenterAbovePoint.Seed
public import Theory.Representation.BinaryNaturalDual.NormalFirstCohomology
public import Theory.Representation.BinaryNaturalDual.InvolutionDisplacement
public import Theory.Representation.FirstCohomologyDuality.Indecomposable

/-!
# The original larger-actor degree alternatives

The exceptional whole S₈ action has a nontrivial smaller actor, so Z(U) is
larger than the flag point V₁. Put N = O²(⟨Z(U)ᵍᴴ⟩). The original rank-two
center geometry makes its dotted image nontrivial and normal and makes N
centralize Z(U). In natural-plus-dual coordinates a nonidentity involution
cannot fix a hyperplane. Thus [W,Z(U)ᵍ] is the displaced point. Irreducibility
and the H-orbit of the original seed then give U = [U,N]V₁.

The literal action of N on U/V₁ descends to its dotted image. The map
U/V₁ → U/Z(U) is consequently a commutator-generated central cover.
Vanishing dual first cohomology on every nontrivial normal subgroup of the
full four-space action forces this map to be injective, contradicting
Z(U) > V₁. This removes the exceptional row and completes the numerical
alternative, including the full dotted-group equivalence to G₂(2).

The Chapter 6 smaller-actor lemma used here has only the generic G.10,
whole-action and relative Sylow-normality hypotheses, all supplied by the
original E action. The final theorem discharges `hdegrees` in the actual
component consumer; its independent component premises remain explicit.

Source: Aschbacher--Smith 12.8.12--13 and 14.3.13--14, printed pp.854--855,
993--994, with the central-cover argument of I.1.5--6, p.408. The ambient
argument handles the exceptional G.10.15 correction recorded in
`docs/quasithin-proof-basis.md`.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ChapterG.Section11 ChapterG.Section09
namespace LargeActorSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  (s : LargeActorSource T M Mc F g B v)
include s
open ChapterG.Section11.FullLinearFour
open Representation.OneCohomology

variable {D : Subgroup F.TerminalHdot}
  {I J : Submodule (ZMod 2) (Additive F.Uhat)}
  (m : WholeActionModel F.terminalRepresentation D I J)
include m

/-- The exceptional whole action forces the center above the flag point. -/
theorem full_four_center_ne_point : F.ZU ≠ F.Vi 1 := by
  intro he
  exact Chapter6.Source.RankOneRecognition.full_four_smaller_actor_ne_bot m
    s.hypothesis s.normal_sylow (s.smaller_actor_eq_bot_of_center_point he)

/-- The displaced center has the full displaced point as its commutator with W. -/
theorem full_four_center_commutator :
    ⁅F.W,conjugate F.ZU g⁆ = conjugate (F.Vi 1) g := by
  classical
  let h := source_lemma_14_2_4 s.simple T s.empty s.maximal s.unique_overgroup
    s.many_overgroups s.seed_card (Classical.choice s.centralizer_quotient)
  let d := Recognition.rankTwo_closure_geometry h F s.nonabelian
  have hg := F.conjugate_center_le_H g
    (F.P_le_seed_normalizer (sourceResidual M Mc) h.L_normalizes_seed s.parabolic_mem)
  have hz := F.terminalDot_center_ne_bot g hg
    (Recognition.rankTwo_terminal_center_kernel h F d s.nonabelian
      g s.parabolic_mem s.normalizer_not_mem)
    (lt_of_le_of_ne (F.point_le_ZU (by decide)) (Ne.symm (s.full_four_center_ne_point m)))
  obtain ⟨a,ha,ha1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hz
  have haX : a ∈ F.terminalDot (F.X g) :=
    (map_mono (comap_mono (F.conjugate_ZU_le_X g))) ha
  have ha2 : a^2=1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) a haX
  let C := BinaryNaturalDual.ModelOrbits.AutomorphismModel.coordinateAction (Or.inl (rfl : 4=4))
  let δ := C.representation (m.groupEquiv a) - 1
  have hne : C.representation (m.groupEquiv a) ≠ 1 := by
    intro he
    apply ha1
    apply s.hypothesis.faithful
    rw [map_one]
    apply LinearMap.ext
    intro w
    apply m.spaceEquiv.injective
    rw [m.equivariant]
    exact LinearMap.congr_fun he (m.spaceEquiv w)
  have hr := C.involution_displacement_ge_two (Or.inl rfl) (m.groupEquiv a)
    (by rw [←map_pow,ha2,map_one]) hne
  have hnat : 3 ≤ 2 → Nonempty (AmbientNaturalMarking (sourceResidual M Mc) h.L_normalizes_seed 2) := by omega
  obtain ⟨hcomm,_⟩ := F.localKernel_commutator_squares h.simpleQTKE (sourceResidual M Mc) M (by decide)
    h.seed_le_sylow h.L_normalizes_seed h.sylow_normalizes_L h.L_residual hnat (h.flag_escape F)
  let form := F.localKernel_markedForm (by decide) d.two d.frattini_point hcomm
  have hq := F.finrank_quotient_hat_centralizer (by decide) d.seed_center form
  have hdim := (hatSpace F F.W).finrank_quotient_add_finrank
  have hd : finrank (ZMod 2) (Additive F.Uhat) = 8 := by
    simpa only [BinaryNaturalDual.CoordinateSpace,BinaryNaturalDual.Space,Module.finrank_prod,
      Subspace.dual_finrank_eq,BinaryLinear.OuterCyclic.Space,Module.finrank_pi,
      Fintype.card_fin,Nat.reduceAdd] using m.spaceEquiv.finrank_eq
  have hnon : ⁅F.W,conjugate F.ZU g⁆ ≠ ⊥ := by
    intro he
    have hcent : conjugate F.ZU g ≤ centralizer (F.W : Set G) := by
      rw [commutator_comm] at he
      exact commutator_eq_bot_iff_le_centralizer.mp he
    have hfix (w : Additive F.Uhat) (hw : w ∈ hatSpace F F.W) :
        F.terminalRepresentation a w = w := by
      obtain ⟨b,hb,rfl⟩ := ha
      obtain ⟨u,hu,heu⟩ := (show w.toMul ∈ hatImage F F.W from hw)
      apply Additive.toMul.injective
      rw [F.terminalRepresentation_apply_mk,←heu,F.terminalHatAction_apply_mk]
      apply congrArg (QuotientGroup.mk' (center F.U))
      apply Subtype.ext
      change (b:G)*(u:G)*(b:G)⁻¹ = (u:G)
      have hbu : (u : G) * (b : G) = (b : G) * (u : G) :=
        mem_centralizer_iff.mp (hcent hb) u hu
      rw [←hbu,mul_assoc,mul_inv_cancel,mul_one]
    have hk : (hatSpace F F.W).map m.spaceEquiv.toLinearMap ≤ δ.ker := by
      rintro _ ⟨w,hw,rfl⟩
      change C.representation (m.groupEquiv a) (m.spaceEquiv w) - m.spaceEquiv w = 0
      rw [←m.equivariant,hfix w hw,sub_self]
    have hl := Submodule.finrank_mono hk
    rw [←(Submodule.equivMapOfInjective _ m.spaceEquiv.injective (hatSpace F F.W)).finrank_eq] at hl
    have hh := δ.finrank_range_add_finrank_ker
    have hcd : finrank (ZMod 2) (BinaryNaturalDual.CoordinateSpace 4) = 8 := by
      simp [BinaryNaturalDual.CoordinateSpace,BinaryNaturalDual.Space,BinaryLinear.OuterCyclic.Space]
    rw [hcd] at hh
    change finrank (ZMod 2) (Additive F.Uhat ⧸ hatSpace F F.W) = 1 at hq
    change 2 ≤ finrank (ZMod 2) δ.range at hr
    omega
  have hc : Nat.card (conjugate (F.Vi 1) g) = 2 := by
    rw [conjugate,card_map_of_injective (MulAut.conj g⁻¹).injective]
    simpa using F.card 1 (by decide)
  apply eq_of_le_of_card_ge (Recognition.rankTwo_center_commutator_le_conjugate_point
    h F d s.nonabelian g s.parabolic_mem s.normalizer_not_mem)
  rw [hc]
  have hh := (one_lt_card_iff_ne_bot _).mpr hnon
  omega

omit s [Finite G] [IsElementaryAbelian 2 (rankTwoSeed T M)] in
private theorem full_four_normal_dual_H1_zero (A : Subgroup F.TerminalHdot)
    [A.Normal] (hA : A ≠ ⊥) :
    finrank (ZMod 2) (H1 (Representation.dual (F.terminalRepresentation.comp A.subtype))) = 0 := by
  let N := A.map m.groupEquiv.toMonoidHom
  let : N.Normal := Normal.map inferInstance _ m.groupEquiv.surjective
  have hN : N ≠ ⊥ := by
    intro he
    apply hA
    apply le_bot_iff.mp
    intro a ha
    exact mem_bot.mpr (m.groupEquiv.map_eq_one_iff.mp
      (mem_bot.mp (he ▸ mem_map_of_mem _ ha)))
  let e := m.groupEquiv.subgroupMap A
  let d := BinaryNaturalDual.ModelOrbits.AutomorphismModel.coordinateAction (Or.inl (rfl : 4=4))
  let σ : Representation (ZMod 2) N (BinaryNaturalDual.CoordinateSpace 4) :=
    d.representation.comp N.subtype
  let ρ : Representation (ZMod 2) A (Additive F.Uhat) :=
    F.terminalRepresentation.comp A.subtype
  have hedual (a : A) (f : Module.Dual (ZMod 2) (Additive F.Uhat)) :
      m.spaceEquiv.symm.dualMap (ρ.dual a f) =
        σ.dual (e a) (m.spaceEquiv.symm.dualMap f) := by
    apply LinearMap.ext
    intro w
    change f (ρ a⁻¹ (m.spaceEquiv.symm w)) = f (m.spaceEquiv.symm (σ (e a)⁻¹ w))
    congr 1
    apply m.spaceEquiv.injective
    rw [m.spaceEquiv.apply_symm_apply]
    change m.spaceEquiv (F.terminalRepresentation (a⁻¹:A) (m.spaceEquiv.symm w)) = _
    rw [m.equivariant,m.spaceEquiv.apply_symm_apply]
    change d.representation (m.groupEquiv (a.val⁻¹)) w = d.representation ((m.groupEquiv a.val)⁻¹) w
    rw [map_inv]
  let eH := H1Congr ρ.dual σ.dual e m.spaceEquiv.symm.dualMap hedual
  let := BinaryNaturalDual.coordinateAction_normal_dual_H1_subsingleton d N hN
  rw [eH.finrank_eq]
  exact Module.finrank_zero_of_subsingleton

omit m in
private theorem normal_coinvariants_top (A : Subgroup F.TerminalHdot)
    [A.Normal] (hA : A ≠ ⊥) :
    Coinvariants.ker (F.terminalRepresentation.comp A.subtype) = ⊤ := by
  let : IsIrreducible F.terminalRepresentation := s.hypothesis.irreducible_of_not_solvable s.nonsolvable
  let C : Subrepresentation F.terminalRepresentation := {
    toSubmodule := Coinvariants.ker (F.terminalRepresentation.comp A.subtype)
    apply_mem_toSubmodule a w hw := Coinvariants.le_comap_ker _ A a hw }
  rcases (inferInstance : IsIrreducible F.terminalRepresentation).eq_bot_or_eq_top C with he | he
  · exfalso
    apply hA
    apply le_bot_iff.mp
    intro a ha
    apply mem_bot.mpr
    apply s.hypothesis.faithful
    rw [map_one]
    apply LinearMap.ext
    intro w
    have hw := Coinvariants.sub_mem_ker (ρ := F.terminalRepresentation.comp A.subtype) ⟨a,ha⟩ w
    rw [show Coinvariants.ker (F.terminalRepresentation.comp A.subtype) = ⊥ from
      congrArg Subrepresentation.toSubmodule he,Submodule.mem_bot] at hw
    exact sub_eq_zero.mp hw
  · exact congrArg Subrepresentation.toSubmodule he

private theorem full_four_source_generation :
    F.U = ⁅F.U,Recognition.centerConjugateResidual F g⁆ ⊔ F.Vi 1 := by
  classical
  let h := source_lemma_14_2_4 s.simple T s.empty s.maximal s.unique_overgroup
    s.many_overgroups s.seed_card (Classical.choice s.centralizer_quotient)
  let d := Recognition.rankTwo_closure_geometry h F s.nonabelian
  obtain ⟨hNH,hHN,hNC,hN⟩ := Recognition.rankTwo_center_residual_geometry
    h F d s.nonabelian g s.parabolic_mem s.normalizer_not_mem s.hypothesis (s.full_four_center_ne_point m)
  let N := Recognition.centerConjugateResidual F g
  let A := F.terminalDot N
  let C := ⁅F.U,N⁆
  have hUH : F.H ≤ normalizer (F.U : Set G) := le_normalizer_conjugateSpanBy _ _
  have hCU : C ≤ F.U := le_normalizer_iff_commutator_le_left.mp (hNH.trans hUH)
  have hHC : F.H ≤ normalizer (C : Set G) := by
    intro a ha
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hUH ha),mem_normalizer_iff_map_conj_eq.mp (hHN ha)]
  let : (N.subgroupOf F.H).Normal := (normal_subgroupOf_iff_le_normalizer hNH).mpr hHN
  let : A.Normal := Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  -- A nontrivial normal image has full commutator space on the irreducible quotient.
  have hCfull : hatSpace F C = ⊤ := by
    apply top_unique
    rw [←s.normal_coinvariants_top A hN]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a,w⟩,rfl⟩
    obtain ⟨b,hb,he⟩ := a.property
    obtain ⟨u,hu⟩ := QuotientGroup.mk'_surjective (center F.U) w.toMul
    have hw : w = Additive.ofMul (QuotientGroup.mk' (center F.U) u) := congrArg Additive.ofMul hu.symm
    rw [hw]
    let u' := F.U.normalizerMonoidHom ⟨b,hUH b.property⟩ u
    change (F.terminalRepresentation a.val _ - _).toMul ∈ hatImage F C
    refine ⟨u' * u⁻¹,?_,?_⟩
    · change ⁅(b:G),(u:G)⁆ ∈ ⁅F.U,N⁆
      rw [commutator_comm F.U N]
      exact commutator_mem_commutator hb u.property
    · rw [toMul_sub,←he,F.terminalRepresentation_apply_mk]
      change QuotientGroup.mk' (center F.U) (u' * u⁻¹) =
        F.terminalHatAction b (QuotientGroup.mk' (center F.U) u) /
          QuotientGroup.mk' (center F.U) u
      rw [F.terminalHatAction_apply_mk]
      simp only [map_mul,map_inv,div_eq_mul_inv]
      rfl

  have hs : F.U = C ⊔ F.ZU := by
    apply le_antisymm ?_ (sup_le hCU (map_subtype_le (center F.U)))
    intro u hu
    let q := QuotientGroup.mk' (center F.U)
    have hm : Additive.ofMul (q ⟨u,hu⟩) ∈ hatSpace F C := hCfull ▸ Submodule.mem_top
    obtain ⟨c,hc,he⟩ := hm
    change q c = q ⟨u,hu⟩ at he
    have hk : c⁻¹ * ⟨u,hu⟩ ∈ center F.U := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q (_ * _) = 1
      rw [map_mul,map_inv,he,inv_mul_cancel]
    have hh := (C ⊔ F.ZU).mul_mem (mem_sup_left hc)
      (mem_sup_right (mem_map_of_mem F.U.subtype hk))
    change (c:G) * ((c:G)⁻¹ * u) ∈ C ⊔ F.ZU at hh
    change u ∈ C ⊔ F.ZU
    simpa only [mul_inv_cancel_left] using hh
  have hg := F.conjugate_center_le_H g
    (F.P_le_seed_normalizer (sourceResidual M Mc) h.L_normalizes_seed s.parabolic_mem)
  have hc := Recognition.rankTwo_centers_commute h F d s.nonabelian g s.parabolic_mem s.normalizer_not_mem
  have huc : ⁅F.U,conjugate F.ZU g⁆ ≤ C := by
    rw [hs]
    exact commutator_sup_le_of_relative_normal F.U C F.ZU (conjugate F.ZU g) C
      (normalizer_commutator_ge_left _ _) hCU (map_subtype_le (center F.U))
      (le_normalizer_iff_commutator_le_left.mp (hg.trans hHC)) (hc.le.trans bot_le)
  have hpoint : conjugate (F.Vi 1) g ≤ C := by
    rw [←s.full_four_center_commutator m]
    exact (commutator_mono (show F.W ≤ F.U from inf_le_left) le_rfl).trans huc
  -- The displaced point and the H-orbit of the seed generate U modulo V₁.
  have hseed : rankTwoSeed T M ≤ C ⊔ F.Vi 1 := by
    calc
      rankTwoSeed T M = F.Vi 1 ⊔ conjugate (F.Vi 1) g :=
        F.last.symm.trans (F.plane_eq_point_join_conjugate (by decide)
          (sourceResidual M Mc) h.L_normalizes_seed g s.parabolic_mem s.normalizer_not_mem)
      _ ≤ C ⊔ F.Vi 1 := sup_le le_sup_right (hpoint.trans le_sup_left)
  apply le_antisymm ?_ (sup_le hCU ((F.le_seed 1).trans (le_conjugateSpanBy _ _)))
  apply conjugateSpanBy_le hseed
  intro a ha
  rw [mem_normalizer_iff_map_conj_eq,Subgroup.map_sup,
    mem_normalizer_iff_map_conj_eq.mp (hHC ha),
    mem_normalizer_iff_map_conj_eq.mp ha]

/-- The original E central cover excludes the whole exceptional four-space action. -/
theorem not_full_four_model : False := by
  classical
  let h := source_lemma_14_2_4 s.simple T s.empty s.maximal s.unique_overgroup
    s.many_overgroups s.seed_card (Classical.choice s.centralizer_quotient)
  let d := Recognition.rankTwo_closure_geometry h F s.nonabelian
  obtain ⟨hNH,hHN,hNC,hN⟩ := Recognition.rankTwo_center_residual_geometry
    h F d s.nonabelian g s.parabolic_mem s.normalizer_not_mem s.hypothesis (s.full_four_center_ne_point m)
  let N := Recognition.centerConjugateResidual F g
  let NH := N.subgroupOf F.H
  let A := F.terminalDot N
  let : NH.Normal := (normal_subgroupOf_iff_le_normalizer hNH).mpr hHN
  let : A.Normal := Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  let : IsElementaryAbelian 2 (F.tilde F.U) := F.tilde_elementary_of_point d.two d.frattini_point
  -- Descend the action on the point quotient through the actual dotted map.
  let q₀ := QuotientGroup.mk' F.terminalHatAction.ker
  let q : NH →* A := q₀.subgroupMap NH
  have hq : Function.Surjective q := q₀.subgroupMap_surjective NH
  let α := (F.localTildeAction F.H le_rfl).comp NH.subtype
  have hk : q.ker ≤ α.ker := by
    intro a ha
    have he : (a:F.H) ∈ F.terminalHatAction.ker :=
      (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val ha)
    have hc : (a:F.H) ∈ pCore 2 F.H :=
      ((Recognition.terminal_restricted_kernel_eq_core F d N hNC) ▸
        (show (a:F.H) ∈ NH ⊓ F.terminalHatAction.ker from ⟨a.property,he⟩)).2
    change (a:F.H) ∈ (F.localTildeAction F.H le_rfl).ker
    rw [d.tilde_kernel]
    exact hc
  let β : A →* MulAut (F.tilde F.U) := q.liftOfSurjective hq ⟨α,hk⟩
  have hβ (a : NH) : β (q a) = α a := q.liftOfRightInverse_comp_apply _ _ _ a
  let σ : Representation (ZMod 2) A (Additive (F.tilde F.U)) :=
    Representation.elementaryRepresentation (p := 2) β
  have hσ (a : NH) (w : Additive (F.tilde F.U)) :
      σ (q a) w = Additive.ofMul (F.localTildeAction F.H le_rfl a.val w.toMul) := by
    change Additive.ofMul (β (q a) w.toMul) = _
    rw [hβ]
    rfl
  let ρ : Representation (ZMod 2) A (Additive F.Uhat) :=
    F.terminalRepresentation.comp A.subtype
  let π := F.tildeToUhat (by decide : 1 ≤ 2)
  let p : σ.IntertwiningMap ρ :=
    π.toAdditive.toZModLinearMap 2 |>.intertwiningMap_of_isIntertwiningMap σ ρ (by
      intro a w
      obtain ⟨b,rfl⟩ := hq a
      rw [hσ]
      exact congrArg Additive.ofMul (F.tildeToUhat_equivariant (by decide) b.val w.toMul))
  -- Verify the central-cover conditions for the literal map U/V₁ → U/Z(U).
  have hp : Function.Surjective p := by
    intro w
    obtain ⟨u,hu⟩ := F.tildeToUhat_surjective (by decide : 1 ≤ 2) w.toMul
    exact ⟨Additive.ofMul u,congrArg Additive.ofMul hu⟩
  have hpfix : p.toLinearMap.ker ≤ fixed σ := by
    intro w hw a
    obtain ⟨b,rfl⟩ := hq a
    have hwZ : w.toMul ∈ (F.tilde F.ZU).subgroupOf (F.tilde F.U) := by
      rw [←F.tildeToUhat_ker (by decide)]
      exact congrArg Additive.toMul hw
    obtain ⟨z,hz,he⟩ := hwZ
    change F.tildeProjection z = (w.toMul : F.G₁tilde) at he
    rw [hσ]
    apply Additive.toMul.injective
    apply Subtype.ext
    change F.tildeProjection b.val * (w.toMul:F.G₁tilde) *
      (F.tildeProjection b.val)⁻¹ = (w.toMul:F.G₁tilde)
    rw [←he,←map_mul,←map_inv,←map_mul]
    apply congrArg F.tildeProjection
    apply Subtype.ext
    change (b.val:G)*(z:G)*(b.val:G)⁻¹ = (z:G)
    have hbz : (z:G) * (b.val:G) = (b.val:G) * (z:G) :=
      mem_centralizer_iff.mp (hNC b.property) z hz
    rw [←hbz,mul_assoc,mul_inv_cancel,mul_one]
  have hpgen : Coinvariants.ker σ = ⊤ := by
    let Q := F.tildeMap F.U F.U_le_H
    let E : Subgroup (F.tilde F.U) := (Coinvariants.ker σ).toAddSubgroup.toSubgroup'
    let C := (E.comap Q).map F.U.subtype
    have hcomm : ⁅F.U,N⁆ ≤ C := by
      rw [commutator_comm]
      apply commutator_le.mpr
      intro a ha u hu
      let b : NH := ⟨⟨a,hNH ha⟩,ha⟩
      let uU : F.U := ⟨u,hu⟩
      let u' := F.uAction b.val uU
      refine ⟨u' * uU⁻¹,?_,rfl⟩
      change Additive.ofMul (Q (u' * uU⁻¹)) ∈ Coinvariants.ker σ
      have hm := Coinvariants.sub_mem_ker (ρ := σ) (q b) (Additive.ofMul (Q uU))
      have he : σ (q b) (Additive.ofMul (Q uU)) = Additive.ofMul (Q u') := by
        rw [hσ]
        apply congrArg Additive.ofMul
        apply Subtype.ext
        change F.tildeProjection b.val * F.tildeProjection ⟨u,F.U_le_H hu⟩ *
          (F.tildeProjection b.val)⁻¹ = F.tildeProjection _
        rw [←map_inv,←map_mul,←map_mul]
        rfl
      rw [he] at hm
      simpa only [map_mul,map_inv,ofMul_mul,ofMul_inv,sub_eq_add_neg] using hm
    have hpoint : F.Vi 1 ≤ C := by
      intro z hz
      have hzU : z ∈ F.U := ((F.le_seed 1).trans (le_conjugateSpanBy _ _)) hz
      refine ⟨⟨z,hzU⟩,?_,rfl⟩
      change Q ⟨z,hzU⟩ ∈ E
      have he : Q ⟨z,hzU⟩ = 1 := by
        apply Subtype.ext
        exact (QuotientGroup.eq_one_iff _).mpr hz
      rw [he]
      exact E.one_mem
    have hUC : F.U ≤ C := by
      rw [s.full_four_source_generation m]
      exact sup_le hcomm hpoint
    apply top_unique
    intro w _
    obtain ⟨u,hu⟩ := F.tildeMap_surjective F.U F.U_le_H w.toMul
    obtain ⟨b,hb,he⟩ := hUC u.property
    have hx : Q u ∈ E := (Subtype.ext he : b=u) ▸ hb
    rw [hu] at hx
    exact hx
  -- Vanishing dual cohomology kills the central kernel of this cover.
  have hbound := finrank_ker_le_H1_of_cover p ⟨hp,hpfix,hpgen⟩
  have hzero := full_four_normal_dual_H1_zero m A hN
  have hinj : Function.Injective p.toLinearMap := LinearMap.ker_eq_bot.mp
    (Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_le_zero (hzero ▸ hbound)))
  apply s.full_four_center_ne_point m
  apply le_antisymm ?_ (F.point_le_ZU (by decide))
  intro z hz
  have hzU := (map_subtype_le (center F.U)) hz
  let u : F.U := ⟨z,hzU⟩
  let w := F.tildeMap F.U F.U_le_H u
  have hpw : p (Additive.ofMul w) = 0 := by
    change Additive.ofMul (π w) = 0
    rw [F.tildeToUhat_apply_map]
    apply congrArg Additive.ofMul
    apply (QuotientGroup.eq_one_iff _).mpr
    obtain ⟨c,hc,he⟩ := hz
    exact (Subtype.ext he : c=u) ▸ hc
  have hw : w = 1 := congrArg Additive.toMul
    (hinj (hpw.trans (map_zero p.toLinearMap).symm))
  have hqz : F.tildeProjection ⟨z,F.U_le_H hzU⟩ = 1 := congrArg Subtype.val hw
  have hmem : (⟨z,F.U_le_H hzU⟩ : F.H) ∈ (F.Vi 1).subgroupOf F.H :=
    (QuotientGroup.eq_one_iff _).mp hqz
  exact hmem

omit m in
/-- The marked exceptional row is impossible under the original E hypotheses. -/
theorem not_full_four_alternative :
    ¬ MarkedAlternative F.terminalRepresentation B v (hatSpace F (F.E g))
      (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) := by
  rintro ⟨D,I,J,m,_⟩
  exact s.not_full_four_model m

omit m in
/-- The original larger-actor degree alternatives, with the full dotted group in degree six. -/
theorem degree_cases :
    (finrank (ZMod 2) (Additive F.Uhat) = 4 ∧
      2 ≤ finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) ∨
    (finrank (ZMod 2) (Additive F.Uhat) = 6 ∧
      finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 3 ∧
      Nonempty (F.TerminalHdot ≃* Atlas.G2.Model (ZMod 2))) := by
  rcases s.degree_cases_or_full_four with good | ⟨_,_,_,hm⟩
  · exact good
  · exact (s.not_full_four_alternative hm).elim

omit m in
/-- Discharge hdegrees in the original component consumer. -/
theorem component_of_source_degrees
    (hfour : finrank (ZMod 2) (Additive F.Uhat) = 4 →
      ∀ D : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot D →
        ⁅D,F.terminalDot (F.X g)⁆ ≠ ⊥ → SmallComponentImage D)
    (hsix : ∀ K : Subgroup G, ComponentLift F g K →
      Nonempty (F.terminalDot K ≃* alternatingGroup (Fin 6)) → False) :
    (∃ D : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot D ∧
      ⁅D,F.terminalDot (F.X g)⁆ ≠ ⊥ ∧ Nonempty (D ≃* alternatingGroup (Fin 5))) ∨
    (∃ K : Subgroup G, ComponentLift F g K ∧ (F.terminalDot K).Normal ∧
      Nonempty (F.terminalDot K ≃* Atlas.G2.BinaryParabolicPair.DerivedModel) ∧
      F.terminalHatAction.ker.comap (K.subgroupOf F.H).subtype =
        pCore 2 (K.subgroupOf F.H)) :=
  source_component_large_actor_of_degree_cases s.simple T s.empty s.maximal
    s.unique_overgroup s.many_overgroups s.seed_card
    (Classical.choice s.centralizer_quotient) F s.nonabelian g s.parabolic_mem
    s.normalizer_not_mem s.nonsolvable s.hypothesis s.degree_cases hfour hsix

end LargeActorSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
