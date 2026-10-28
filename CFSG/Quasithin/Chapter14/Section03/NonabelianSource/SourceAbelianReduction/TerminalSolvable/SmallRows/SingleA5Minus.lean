module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.SingleA5Center
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.ParabolicOrthogonal
public import Theory.GroupTheory.PGroup.FiveSquareRecognition
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The exact minus closure and opposite local in the normalized A₅ branch

The full five-point coordinates identify the original square map with the
minus quadratic form. Thus the same U is Q₈ * D₈. Its elementary
intersection E with the prescribed conjugate has order four and equals
the original seed V; the action-kernel calculation also gives
O₂(H) ∩ Uᵍ = V. The original factorization O₂(I₂)=WWᵍ then gives
|W|=16, |O₂(I₂)|=64 and |I₂|=384, with its actual S₃ quotient.

These results discharge local inputs to the terminal-solvability owner's
remaining core and ambient recognition argument. They do not identify
U with O₂(H) or assert an ambient Janko isomorphism.

Source: Aschbacher–Smith 12.8.9–11, 14.2.16 and 14.3.6,14–15,
printed pp.852–854,985–986,991,994.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
section Source
variable {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)

variable (hnot : ¬ ClassificationModels.IsTheoremEModel G) (g : G)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    {K : Subgroup G} (hK : ComponentLift F g K)
include hnot hgP hgH hyp hK


include hG hempty hM hu hmany hcard e hne

/-- The original square map is the minus form in the same full action coordinates. -/
theorem source_single_a5_square_coordinates_of_four
    (e5 : F.terminalDot K ≃* alternatingGroup (Fin 5))
    (hspan : K = conjugateSpanBy K (T : Subgroup G))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4) :
    ∃ c : Additive F.Uhat ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 5),
      ∀ u : F.U, u ^ 2 = 1 ↔ BinaryPermutation.FiveGeometry.form
        (c (Additive.ofMul (QuotientGroup.mk' (center F.U) u))) = 0 := by
  obtain ⟨c,p,w,hp,hm,he,hw,hline,hfw,hfix⟩ := source_single_a5_whole_action_seed_of_four
    hG T hempty hM hu hmany hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  have hZ := source_single_a5_center_eq_point_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  let d := Recognition.rankTwo_closure_geometry h F hne
  let hphi := Recognition.center_frattini_bot_of_center_point F d hZ
  let q := Recognition.centerPointQuadraticForm F d (by decide) hZ
  have hdis : Disjoint (conjugate (F.Vi 1) g) F.ZU :=
    disjoint_iff.mpr (F.parabolic_displaced_centers (by decide) (sourceResidual M Mc)
      h.L_normalizes_seed d.seed_center g hgP hgH).1
  obtain ⟨hs,hqi,hnd⟩ := Recognition.quadratic_intersection_of_center_point F d (by decide) hZ g hdis
  change (∀ x ∈ hatSpace F (F.E g), q x = 0) at hs
  change q.polarBilin.Nondegenerate at hnd
  have hqin (a : F.TerminalHdot) (x : Additive F.Uhat) : q (F.terminalRepresentation a x) = q x := by
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective F.terminalHatAction.ker a
    exact hqi a x.toMul
  let q' := q.comp c.symm.toLinearMap
  have hqne : q' ≠ 0 := by
    intro hh
    have hzero (x : Additive F.Uhat) : q x = 0 := by
      have hv := congrArg (fun z : QuadraticForm (ZMod 2) (BinaryPermutation.core (Fin 5)) => z (c x)) hh
      simpa only [q',QuadraticMap.comp_apply,LinearEquiv.coe_coe,c.symm_apply_apply,
        zero_apply] using hv
    exact hw (hnd.1 w (fun y => by
      rw [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,hzero,hzero,hzero]
      simp))
  have hwin : w ∈ hatSpace F (F.E g) := by
    have hwseed : w ∈ hatSpace F (rankTwoSeed T M) := by
      rw [hline]
      exact Submodule.subset_span (Set.mem_singleton w)
    obtain ⟨u,hu,heu⟩ := hwseed
    exact ⟨u,F.seed_le_E_of_normalizes g
      (F.P_le_seed_normalizer (sourceResidual M Mc) h.L_normalizes_seed hgP) hu,heu⟩
  have heq : q' = BinaryPermutation.FiveGeometry.form := by
    apply BinaryPermutation.FiveGeometry.eq_form_of_invariant_seed q' hqne ?_
      (c w) (fun hh => hw (c.injective (hh.trans (map_zero c).symm))) ?_ hfw
    · intro a x
      have ha := he ((e5.symm a : F.terminalDot K) : F.TerminalHdot) (c.symm x)
      rw [hm,e5.apply_symm_apply,c.apply_symm_apply] at ha
      change q (c.symm (BinaryPermutation.coreRepresentation (Fin 5) a.val x)) = q (c.symm x)
      rw [←ha,c.symm_apply_apply]
      exact hqin _ _
    · simpa only [q',QuadraticMap.comp_apply,LinearEquiv.coe_coe,c.symm_apply_apply] using hs w hwin
  have hqeq (x : Additive F.Uhat) : q x = BinaryPermutation.FiveGeometry.form (c x) := by
    have hh := congrArg (fun z : QuadraticForm (ZMod 2) (BinaryPermutation.core (Fin 5)) => z (c x)) heq
    simpa only [q',QuadraticMap.comp_apply,LinearEquiv.coe_coe,c.symm_apply_apply] using hh
  refine ⟨c,fun u => ?_⟩
  rw [←hqeq]
  change u ^ 2 = 1 ↔ (SmallFrattini.binaryMark (F.frattini_card_two_of_point (by decide) d.frattini_point)
    (F.uhatSquare d.two hphi (QuotientGroup.mk' (center F.U) u))).toAdd = 0
  constructor
  · intro hu
    have hz : F.uhatSquare d.two hphi (QuotientGroup.mk' (center F.U) u) = 1 := by
      apply Subtype.ext
      rw [F.uhatSquare_apply_mk,hu]
      rfl
    rw [hz,map_one]
    rfl
  · intro hh
    have hz := (SmallFrattini.binaryMark (F.frattini_card_two_of_point (by decide) d.frattini_point)).injective
      (show SmallFrattini.binaryMark (F.frattini_card_two_of_point (by decide) d.frattini_point)
        (F.uhatSquare d.two hphi (QuotientGroup.mk' (center F.U) u)) =
        SmallFrattini.binaryMark (F.frattini_card_two_of_point (by decide) d.frattini_point) 1 from
        (show SmallFrattini.binaryMark (F.frattini_card_two_of_point (by decide) d.frattini_point)
          (F.uhatSquare d.two hphi (QuotientGroup.mk' (center F.U) u)) = 1 from hh).trans (map_one _).symm)
    have hh' := congrArg (fun a : frattini F.U => (a : F.U)) hz
    simpa only [F.uhatSquare_apply_mk,Subgroup.coe_one] using hh'

/-- Recognition of the same actual closure, without a core identification premise. -/
theorem source_single_a5_minus_model_of_four
    (e5 : F.terminalDot K ≃* alternatingGroup (Fin 5))
    (hspan : K = conjugateSpanBy K (T : Subgroup G))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4) :
    Nonempty (F.U ≃* MinusExtraspecial.Model) := by
  obtain ⟨hZ,hE,hU,hker⟩ := source_single_a5_extraspecial_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  let := hE
  obtain ⟨c,hc⟩ := source_single_a5_square_coordinates_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  exact IsExtraspecial.minus_model_of_five_square_coordinates hU c (fun u hu => (hc u).mp hu)

/-- The elementary source intersection is exactly the original seed plane. -/
theorem source_single_a5_intersection_eq_seed_of_four
    (e5 : F.terminalDot K ≃* alternatingGroup (Fin 5))
    (hspan : K = conjugateSpanBy K (T : Subgroup G))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4) :
    F.E g = rankTwoSeed T M := by
  obtain ⟨hZ,hE,hU,hker⟩ := source_single_a5_extraspecial_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  let := hE
  obtain ⟨c,hc⟩ := source_single_a5_square_coordinates_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  let d := Recognition.rankTwo_closure_geometry h F hne
  have hdis : Disjoint (conjugate (F.Vi 1) g) F.ZU :=
    disjoint_iff.mpr (F.parabolic_displaced_centers (by decide) (sourceResidual M Mc)
      h.L_normalizes_seed d.seed_center g hgP hgH).1
  have hPhi : (frattini F.U).map F.U.subtype = F.Vi 1 := by
    rw [d.frattini_point]
    exact map_subgroupOf_eq_of_le
      (show F.Vi 1 ≤ F.U from (F.le_seed 1).trans (le_conjugateSpanBy _ F.H))
  let : IsElementaryAbelian 2 (F.E g) := F.E_elementary (by decide) g d.two hPhi hdis
  have hEU : F.E g ≤ F.U := inf_le_left.trans inf_le_left
  let A := (F.E g).subgroupOf F.U
  let j : A ≃* F.E g := subgroupOfEquivOfLe hEU
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_injective j.toMonoidHom j.injective
  have hbound := IsExtraspecial.elementary_card_le_four_of_five_square_coordinates c
    (fun u hu => (hc u).mp hu) A
  have hVE := F.seed_le_E_of_normalizes g
    (F.P_le_seed_normalizer (sourceResidual M Mc) h.L_normalizes_seed hgP)
  apply (eq_of_le_of_card_ge hVE ?_).symm
  have hV : Nat.card (rankTwoSeed T M) = 4 := by simpa only [←F.last,show 2^2=4 by decide] using F.card 2 (by decide)
  rw [Nat.card_congr j.toEquiv] at hbound
  omega

/-- The literal local two-core intersects the conjugate closure in the seed. -/
theorem source_single_a5_core_intersection_of_four
    (e5 : F.terminalDot K ≃* alternatingGroup (Fin 5))
    (hspan : K = conjugateSpanBy K (T : Subgroup G))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4) :
    F.H.pCoreIn 2 ⊓ conjugate F.U g = rankTwoSeed T M := by
  have hZ := source_single_a5_center_eq_point_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  have hE := source_single_a5_intersection_eq_seed_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  let d := Recognition.rankTwo_closure_geometry h F hne
  have hnat : 3≤2→Nonempty (AmbientNaturalMarking (sourceResidual M Mc) h.L_normalizes_seed 2) := by omega
  obtain ⟨hcomm,hsquare⟩ := F.localKernel_commutator_squares h.simpleQTKE (sourceResidual M Mc) M (by decide)
    h.seed_le_sylow h.L_normalizes_seed h.sylow_normalizes_L h.L_residual hnat (h.flag_escape F)
  have hUspan : F.U=conjugateSpanBy (F.Vi 2) F.H := by rw [F.last]; rfl
  have hk := (F.binary_source_action_kernel_intersections (by decide) (sourceResidual M Mc)
    h.L_normalizes_seed (h.binarySeedAction_surjective F) h.centralizer hcomm hsquare hUspan hne
    d.seed_center g hgP hgH).1
  change F.X g ⊓ F.terminalHatAction.ker.map F.H.subtype=F.E g at hk
  rw [Recognition.terminal_kernel_of_center_point F d hZ] at hk
  have hX := Recognition.conjugate_U_inf_H_eq_X F h.L_normalizes_seed g hgP hgH
  apply Eq.trans ?_ (hk.trans hE)
  rw [←hX]
  change F.H.pCoreIn 2 ⊓ conjugate F.U g=
    (conjugate F.U g ⊓ F.H) ⊓ F.H.pCoreIn 2
  have hcore : F.H.pCoreIn 2≤F.H := map_subtype_le _
  exact le_antisymm (fun x hx => ⟨⟨hx.2,hcore hx.1⟩,hx.1⟩)
    (fun x hx => ⟨hx.2,hx.1.1⟩)

/-- The actual opposite local group has order 384 and two-core order 64.
These are the original carriers generated by U and its prescribed conjugate. -/
theorem source_single_a5_opposite_orders_of_four
    (e5 : F.terminalDot K ≃* alternatingGroup (Fin 5))
    (hspan : K = conjugateSpanBy K (T : Subgroup G))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4) :
    Nat.card F.W = 16 ∧ Nat.card ((F.I₂ (sourceResidual M Mc)).pCoreIn 2) = 64 ∧
      Nat.card (F.I₂ (sourceResidual M Mc)) = 384 := by
  have hE := source_single_a5_intersection_eq_seed_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  obtain ⟨_,_,hU,_⟩ := source_single_a5_extraspecial_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  have hnat : 3≤2→Nonempty (AmbientNaturalMarking (sourceResidual M Mc) h.L_normalizes_seed 2) := by omega
  obtain ⟨hcomm,hsquare⟩ := F.localKernel_commutator_squares h.simpleQTKE (sourceResidual M Mc) M (by decide)
    h.seed_le_sylow h.L_normalizes_seed h.sylow_normalizes_L h.L_residual hnat (h.flag_escape F)
  have hUspan : F.U=conjugateSpanBy (F.Vi 2) F.H := by rw [F.last]; rfl
  obtain ⟨eqI,_,hgen,_,hIG,hIN,_,_,hfactor,hPH,hcore,hindex,_⟩ := F.binary_generation
    (by decide) (sourceResidual M Mc) h.L_normalizes_seed (h.binarySeedAction_surjective F)
    h.centralizer hcomm hsquare hUspan hne g hgP hgH
  have hsplit := (F.binary_source_core_and_intersection (by decide) (sourceResidual M Mc)
    h.L_normalizes_seed (h.binarySeedAction_surjective F) h.centralizer
    hcomm hsquare hUspan hne g hgP hgH).1
  have hW : Nat.card F.W = 16 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) F.W F.U bot_le inf_le_left
    simp only [relIndex_bot_left,hindex,hU] at hh
    omega
  have hX : Nat.card (F.X g) = 16 := by
    change Nat.card (conjugate F.W g) = 16
    rw [conjugate,card_map_of_injective (MulAut.conj g⁻¹).injective,hW]
  have hXN : F.X g ≤ normalizer (F.W : Set G) := by
    apply (le_inf (F.X_normalizes_U g (F.P_le_G₂ (by decide) _ h.L_normalizes_seed hgP))
      ?_).trans inf_normalizer_le_normalizer_inf
    exact (F.X_le_plane_centralizer g
      (F.P_le_G₂ (by decide) _ h.L_normalizes_seed hgP)).trans
      (centralizer (F.Vi 2 : Set G)).le_normalizer
  have hS : Nat.card ((F.I₂ (sourceResidual M Mc)).pCoreIn 2) = 64 := by
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes F.W (F.X g) hXN
    change Nat.card F.W * Nat.card (F.X g) = Nat.card (F.E g) * Nat.card (F.W ⊔ F.X g : Subgroup G) at hh
    rw [hW,hX,←hsplit,hE,show Nat.card (rankTwoSeed T M) = 4 by simpa only [←F.last,show 2^2=4 by decide] using F.card 2 (by decide)] at hh
    omega
  refine ⟨hW,hS,?_⟩
  have hh := (pCore 2 (F.I₂ (sourceResidual M Mc))).card_eq_card_quotient_mul_card_subgroup
  rw [Nat.card_congr eqI.toEquiv] at hh
  have hS' : Nat.card (pCore 2 (F.I₂ (sourceResidual M Mc))) = 64 := by
    change Nat.card ((pCore 2 (F.I₂ (sourceResidual M Mc))).map (F.I₂ (sourceResidual M Mc)).subtype) = 64 at hS
    rwa [card_map_of_injective (F.I₂ (sourceResidual M Mc)).subtype_injective] at hS
  rw [hS'] at hh
  norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial] at hh
  exact hh

end Source
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
