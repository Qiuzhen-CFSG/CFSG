module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.SingleA5Minus
public import Theory.GroupTheory.ConjugatePairSeed.Supplement

public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.ParabolicSeedResidual
public import Theory.Representation.BinaryPermutation.FiveCoinvariants
public import Theory.Representation.FrattiniCoinvariantCommutator
public import CFSG.Quasithin.Chapter14.Section02.ProperOutsideSylow

/-!
# Opposite cores in the original normalized degree-four A₅ branch

The literal opposite core R meets Q=O₂(H) in W, with [R,Q] contained
in U. Its dotted image has order four and is normal in the dotted Sylow.
Five-point coordinates and Frattini lifting give U=[U,K], placing U in
the selected component's own two-core. The original opposite residual Y
has order 192, core R of order 64, and a fixed-point-free element of order
three.

The extraspecial centralizer theorem isolates the remaining full-core
question in D=C_Q(U): Q=UD, U∩D=V₁ and [D,R]≤V₁. Eliminating D/V₁ and
recognizing the ambient field-four case remain obligations of the terminal
solvability owner. No equality U=Q is inferred from the action kernel.

Source: Aschbacher–Smith 14.2.16 and 14.3.6,15, pp.986,991,994.
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

/-- The opposite core has the original hyperplane as its intersection with
O₂(H); its image is the same rank-two actor, normal in the dotted Sylow. -/
theorem source_single_a5_core_pair_of_four
    (e5 : F.terminalDot K ≃* alternatingGroup (Fin 5))
    (hspan : K = conjugateSpanBy K (T : Subgroup G))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4) :
    let R := (F.I₂ (sourceResidual M Mc)).pCoreIn 2
    let Q := F.H.pCoreIn 2
    let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
      (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
    R ≤ (T : Subgroup G) ∧ R = F.W ⊔ F.X g ∧ R ⊓ Q = F.W ∧
      ⁅R,Q⁆ ≤ F.U ∧ F.terminalDot R = F.terminalDot (F.X g) ∧
      F.terminalDot R ≤ (P : Subgroup F.TerminalHdot) ∧
      (P : Subgroup F.TerminalHdot) ≤ normalizer (F.terminalDot R : Set F.TerminalHdot) ∧
      Nat.card (F.terminalDot R) = 4 := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  let dg := Recognition.rankTwo_closure_geometry h F hne
  have hZ := source_single_a5_center_eq_point_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  obtain ⟨hWc,hRc,hIc⟩ := source_single_a5_opposite_orders_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  let L := sourceResidual M Mc
  let R := (F.I₂ L).pCoreIn 2
  let Q := F.H.pCoreIn 2
  let : Fact (IsPGroup 2 F.U) := ⟨dg.two⟩
  have hPhi : (frattini F.U).map F.U.subtype=F.Vi 1 := by
    rw [dg.frattini_point]
    exact map_subgroupOf_eq_of_le ((F.le_seed 1).trans (le_conjugateSpanBy _ _))
  have hcomm : ⁅F.U,F.U⁆≤F.Vi 1 := by
    rw [←F.U.map_subtype_commutator]
    exact (map_mono (f:=F.U.subtype) (commutator_le_frattini_of_isPGroup (p:=2))).trans hPhi.le
  have hsquare : ∀u∈F.U,u^2∈F.Vi 1 := fun u hu=>
    hPhi ▸ mem_map_of_mem F.U.subtype (pth_power_mem_frattini_of_isPGroup (p:=2) (⟨u,hu⟩:F.U))
  have hUspan : F.U=conjugateSpanBy (F.Vi 2) F.H := by rw [F.last]; rfl
  obtain ⟨e₀,_,hgen,_,hIG,hIN,_,_,hfactor,hPH,hcore,hindex,_⟩ :=
    F.binary_generation (by decide) L h.L_normalizes_seed (h.binarySeedAction_surjective F)
      h.centralizer hcomm hsquare hUspan hne g hgP hgH
  have hsplit : R=F.W⊔F.X g :=
    F.binary_core_factorization L g hgP hfactor hPH hgen.symm e₀ hcore hindex
  have hRN : F.Gi 2≤normalizer (R:Set G) :=
    ((normal_subgroupOf_iff_le_normalizer hIG).mp hIN).trans
      (normalizer_le_normalizer_characteristic_image (F.I₂ L) (pCore 2 (F.I₂ L)))
  have hRT : R≤(T:Subgroup G) := normalized_pSubgroup_le_sylow T (F.Gi 2) R
    (F.invariant 2) ((pCoreIn_le 2 (F.I₂ L)).trans hIG) hRN (isPGroup_pCoreIn 2 (F.I₂ L))
  have hTH : (T:Subgroup G)≤F.H := F.invariant 1
  have hQT : Q≤(T:Subgroup G) := by
    have hh := pCoreIn_le_sylow F.H (T.subtype hTH)
    change Q≤((T:Subgroup G).subgroupOf F.H).map F.H.subtype at hh
    rwa [map_subgroupOf_eq_of_le hTH] at hh
  have hRH : R≤F.H := hRT.trans hTH
  have hQH : Q≤F.H := pCoreIn_le 2 F.H
  have hUQ : F.U≤Q := le_pCoreIn_of_normalizes dg.two F.U_le_H
    (le_normalizer_conjugateSpanBy _ _)
  have hWH : F.W≤F.H := inf_le_left.trans F.U_le_H
  have hXH : F.X g≤F.H := F.X_le_H g (F.P_le_G₂ (by decide) L h.L_normalizes_seed hgP)
  have hXc : Nat.card (F.X g)=16 := by
    change Nat.card (F.W.map (MulAut.conj g⁻¹).toMonoidHom)=16
    rw [card_map_of_injective (MulAut.conj g⁻¹).injective,hWc]
  have hVx : rankTwoSeed T M≤F.X g :=
    (F.seed_le_E_of_normalizes g (F.P_le_seed_normalizer L h.L_normalizes_seed hgP)).trans inf_le_right
  have hVc : Nat.card (rankTwoSeed T M)=4 := by
    simpa only [F.last,show (2:ℕ)^2=4 from rfl] using F.card 2 le_rfl
  have hQX : Q⊓F.X g=rankTwoSeed T M := by
    have hh := source_single_a5_core_intersection_of_four hG T hempty hM hu hmany
      hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
    rw [←Recognition.conjugate_U_inf_H_eq_X F h.L_normalizes_seed g hgP hgH]
    rw [←inf_assoc,inf_comm Q,inf_assoc,inf_eq_left.mpr hQH,inf_comm]
    exact hh
  let q := QuotientGroup.mk' F.terminalHatAction.ker
  have hqker : q.ker=pCore 2 F.H := by
    rw [QuotientGroup.ker_mk',Recognition.terminal_kernel_of_center_point F dg hZ]
  have hXdotc : Nat.card (F.terminalDot (F.X g))=4 := by
    change Nat.card ((F.X g).subgroupOf F.H |>.map q)=4
    rw [←relIndex_ker _ q,hqker]
    have he := relIndex_map_map_of_injective (pCore 2 F.H) ((F.X g).subgroupOf F.H) F.H.subtype_injective
    rw [map_subgroupOf_eq_of_le hXH] at he
    change Q.relIndex (F.X g)=(pCore 2 F.H).relIndex ((F.X g).subgroupOf F.H) at he
    rw [←he,←inf_relIndex_right,hQX]
    have hh := relIndex_mul_card_of_le hVx
    rw [hVc,hXc] at hh
    omega
  have hWdot : F.terminalDot F.W=⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    rw [hqker]
    intro w hw
    obtain ⟨a,ha,he⟩ := (hUQ ((show F.W≤F.U from inf_le_left) hw))
    exact (show a=w from Subtype.ext he) ▸ ha
  have hRdot : F.terminalDot R=F.terminalDot (F.X g) := by
    change (R.subgroupOf F.H).map q=((F.X g).subgroupOf F.H).map q
    rw [hsplit,subgroupOf_sup hWH hXH,Subgroup.map_sup]
    change F.terminalDot F.W⊔F.terminalDot (F.X g)=F.terminalDot (F.X g)
    rw [hWdot,bot_sup_eq]
  let P : Sylow 2 F.TerminalHdot := (T.subtype hTH).mapSurjective
    (f:=q) (QuotientGroup.mk'_surjective _)
  have hRP : F.terminalDot R≤(P:Subgroup F.TerminalHdot) :=
    map_mono (show R.subgroupOf F.H≤(T:Subgroup G).subgroupOf F.H from fun _ hx=>hRT hx)
  have hRI : Q.relIndex R=4 := by
    have he := relIndex_map_map_of_injective (pCore 2 F.H) (R.subgroupOf F.H)
      F.H.subtype_injective
    rw [map_subgroupOf_eq_of_le hRH] at he
    change Q.relIndex R=(pCore 2 F.H).relIndex (R.subgroupOf F.H) at he
    rw [he,←hqker,relIndex_ker]
    change Nat.card (F.terminalDot R)=4
    rw [hRdot,hXdotc]
  have hRQc : Nat.card (R⊓Q:Subgroup G)=16 := by
    rw [inf_comm R Q]
    have hh := relIndex_mul_card_of_le (show R⊓Q≤R from inf_le_left)
    rw [inf_comm R Q,inf_relIndex_right,hRI,hRc] at hh
    omega
  have hWQ : F.W≤Q := (show F.W≤F.U from inf_le_left).trans hUQ
  have hWR : F.W≤R := le_sup_left.trans hsplit.ge
  have hRQ : R⊓Q=F.W := (eq_of_le_of_card_ge (le_inf hWR hWQ)
    (by rw [hWc,hRQc])).symm
  have hQR : Q≤normalizer (R:Set G) := (hQT.trans (F.invariant 2)).trans hRN
  have hRHnorm : R≤normalizer (Q:Set G) := hRH.trans
    (F.H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image F.H (pCore 2 F.H)))
  have hRQcomm : ⁅R,Q⁆≤F.U := by
    have hi : ⁅R,Q⁆≤R⊓Q := le_inf
      (le_normalizer_iff_commutator_le_left.mp hQR)
      (by rw [commutator_comm];exact le_normalizer_iff_commutator_le_left.mp hRHnorm)
    rw [hRQ] at hi
    exact hi.trans inf_le_left
  have hTR : (T:Subgroup G)≤normalizer (R:Set G) := (F.invariant 2).trans hRN
  have hnH : (T:Subgroup G).subgroupOf F.H≤normalizer (R.subgroupOf F.H:Set F.H) := by
    intro t ht
    apply mem_normalizer_iff.mpr
    intro r
    change (r:G)∈R ↔ (t:G)*(r:G)*(t:G)⁻¹∈R
    exact (mem_normalizer_iff.mp (hTR ht)) (r:G)
  have hnP : (P:Subgroup F.TerminalHdot)≤normalizer (F.terminalDot R:Set F.TerminalHdot) :=
    (map_mono hnH).trans (le_normalizer_map _)
  exact ⟨hRT,hsplit,hRQ,hRQcomm,hRdot,hRP,hnP,by rw [hRdot,hXdotc]⟩

/-- The remaining full-core question is concentrated in its literal
centralizing supplement, whose commutator with the opposite core lies in V₁. -/
theorem source_single_a5_core_supplement_of_four
    (e5 : F.terminalDot K ≃* alternatingGroup (Fin 5))
    (hspan : K = conjugateSpanBy K (T : Subgroup G))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4) :
    let Q := F.H.pCoreIn 2
    let D := Q ⊓ centralizer (F.U : Set G)
    F.U ⊔ D = Q ∧ F.U ⊓ D = F.Vi 1 ∧
      F.H ≤ normalizer (D : Set G) ∧
      ⁅D,(F.I₂ (sourceResidual M Mc)).pCoreIn 2⁆ ≤ F.Vi 1 ∧
      (F.U = Q ↔ D = F.Vi 1) := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  let dg := Recognition.rankTwo_closure_geometry h F hne
  obtain ⟨hZ,hex,hUc,hker⟩ := source_single_a5_extraspecial_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  let := hex
  let Q := F.H.pCoreIn 2
  let D := Q ⊓ centralizer (F.U : Set G)
  let R := (F.I₂ (sourceResidual M Mc)).pCoreIn 2
  have hUQ : F.U ≤ Q := le_pCoreIn_of_normalizes dg.two F.U_le_H
    (le_normalizer_conjugateSpanBy _ _)
  have hc : ⁅Q,F.U⁆ ≤ F.Vi 1 := by
    rw [←hZ]
    apply commutator_le.mpr
    intro q hq u hu
    let qh : F.H := ⟨q,pCoreIn_le 2 F.H hq⟩
    have hqker : qh ∈ F.terminalHatAction.ker := by
      rw [hker]
      obtain ⟨a,ha,he⟩ := hq
      exact (show a=qh from Subtype.ext he) ▸ ha
    have he := DFunLike.congr_fun hqker (QuotientGroup.mk' (center F.U) ⟨u,hu⟩)
    rw [F.terminalHatAction_apply_mk] at he
    change QuotientGroup.mk' (center F.U) (F.uAction qh ⟨u,hu⟩) =
      QuotientGroup.mk' (center F.U) ⟨u,hu⟩ at he
    have hm : F.uAction qh ⟨u,hu⟩ * (⟨u,hu⟩ : F.U)⁻¹ ∈ center F.U := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' (center F.U) _ = 1
      rw [map_mul,map_inv,he]
      exact mul_inv_cancel _
    exact mem_map_of_mem F.U.subtype hm
  have hs : F.U ⊔ D = Q := extraspecial_sup_centralizer_eq F.U Q (F.Vi 1) hUQ hZ hc
  have hi : F.U ⊓ D = F.Vi 1 := by
    change F.U ⊓ (Q ⊓ centralizer (F.U : Set G)) = _
    rw [←inf_assoc,inf_eq_left.mpr hUQ,←map_center_subtype_eq_inf_centralizer]
    exact hZ
  have hQD : F.H ≤ normalizer (Q : Set G) := F.H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image F.H (pCore 2 F.H))
  have hHD : F.H ≤ normalizer (D : Set G) :=
    (le_inf hQD ((le_normalizer_conjugateSpanBy _ _).trans
      (normalizer_le_normalizer_centralizer F.U))).trans inf_normalizer_le_normalizer_inf
  obtain ⟨hRT,_,_,hRQ,_⟩ := source_single_a5_core_pair_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  have hDR : ⁅D,R⁆ ≤ F.Vi 1 := by
    rw [←hi]
    refine le_inf ?_ (le_normalizer_iff_commutator_le_left.mp
      ((hRT.trans (F.invariant 1)).trans hHD))
    rw [commutator_comm]
    exact (commutator_mono le_rfl (show D≤Q from inf_le_left)).trans hRQ
  refine ⟨hs,hi,hHD,hDR,?_⟩
  constructor
  · intro he
    have hh : F.U ⊓ D = D := inf_eq_right.mpr (show D≤F.U from he ▸ inf_le_left)
    exact hh.symm.trans hi
  · intro he
    change D = F.Vi 1 at he
    have hp : F.Vi 1 ≤ F.U := (F.le_seed 1).trans (le_conjugateSpanBy _ _)
    rw [he,sup_eq_left.mpr hp] at hs
    exact hs


/-- The same selected component generates the whole closure by commutators,
so the closure lies in its literal two-core. -/
theorem source_single_a5_closure_component_of_four
    (e5 : F.terminalDot K ≃* alternatingGroup (Fin 5))
    (hspan : K = conjugateSpanBy K (T : Subgroup G))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4) :
    F.U = ⁅F.U,K⁆ ∧ F.U ≤ K.pCoreIn 2 := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  let dg := Recognition.rankTwo_closure_geometry h F hne
  obtain ⟨hZ,hex,_,_⟩ := source_single_a5_extraspecial_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  let := hex
  obtain ⟨c,p,hp,hm,he⟩ := source_single_a5_whole_action_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  let q := QuotientGroup.mk' F.terminalHatAction.ker
  let a := (subgroupOfEquivOfLe hK.le_pointNormalizer).symm
  let j := q.subgroupMap (K.subgroupOf F.H)
  let π : K →* F.terminalDot K := j.comp a.toMonoidHom
  let f5 : K →* alternatingGroup (Fin 5) := e5.toMonoidHom.comp π
  have hf5 : Function.Surjective f5 := e5.surjective.comp
    ((q.subgroupMap_surjective (K.subgroupOf F.H)).comp a.surjective)
  let σ := F.terminalRepresentation.comp ((F.terminalDot K).subtype.comp π)
  have hcoords (k : K) (w : Additive F.Uhat) :
      c (σ k w) = BinaryPermutation.coreRepresentation (Fin 5) (f5 k).val (c w) := by
    have hh := he ((π k : F.terminalDot K) : F.TerminalHdot) w
    rw [hm] at hh
    exact hh
  have hcoin := BinaryPermutation.five_coinvariants_of_coordinates σ f5 hf5 c hcoords
  let qU := QuotientGroup.mk' (center F.U)
  let f : F.U →* Multiplicative (Additive F.Uhat) := {
    toFun u := Multiplicative.ofAdd (Additive.ofMul (qU u))
    map_one' := congrArg (fun x => Multiplicative.ofAdd (Additive.ofMul x)) (map_one qU)
    map_mul' := fun x y => congrArg (fun x => Multiplicative.ofAdd (Additive.ofMul x)) (map_mul qU x y) }
  have hf : Function.Surjective f := by
    intro w
    obtain ⟨u,hu⟩ := QuotientGroup.mk'_surjective (center F.U) w.toAdd.toMul
    exact ⟨u,congrArg (fun x => Multiplicative.ofAdd (Additive.ofMul x)) hu⟩
  have hfk : f.ker ≤ frattini F.U := by
    rw [IsExtraspecial.frattini_eq_center_two]
    intro u hu
    exact (QuotientGroup.eq_one_iff u).mp hu
  have hact (k : K) (u u' : F.U) (hu' : (u' : G) = (k : G) * (u : G) * (k : G)⁻¹) :
      (f u').toAdd = σ k (f u).toAdd := by
    change Additive.ofMul (qU u') = F.terminalRepresentation
      (QuotientGroup.mk' F.terminalHatAction.ker ⟨k,hK.le_pointNormalizer k.property⟩)
      (Additive.ofMul (qU u))
    apply Additive.toMul.injective
    rw [F.terminalRepresentation_apply_mk]
    change qU u' = F.terminalHatAction ⟨k,hK.le_pointNormalizer k.property⟩
      ((QuotientGroup.mk' (center F.U)) u)
    rw [F.terminalHatAction_apply_mk]
    apply congrArg qU
    exact Subtype.ext hu'
  have hnorm : K ≤ normalizer (F.U : Set G) := hK.le_pointNormalizer.trans
    (le_normalizer_conjugateSpanBy _ _)
  have hcomm := Representation.subgroup_eq_commutator_of_frattini_coinvariants
    F.U K.subtype (by rw [range_subtype]; exact hnorm) σ f hf hfk hact hcoin
  rw [range_subtype] at hcomm
  have hnK : (K.subgroupOf F.H).Normal := by
    have hh := hK.normal_span
    rwa [←hspan] at hh
  have hUK : F.U ≤ K := by
    rw [hcomm]
    exact le_normalizer_iff_commutator_le_right.mp (F.U_le_H.trans
      ((normal_subgroupOf_iff_le_normalizer hK.le_pointNormalizer).mp hnK))
  exact ⟨hcomm,le_pCoreIn_of_normalizes dg.two hUK hnorm⟩


/-- The actual opposite residual has order 192; its two-core is the original
order-64 opposite core and admits a fixed-point-free cubic in that residual. -/
theorem source_single_a5_opposite_residual_of_four
    (e5 : F.terminalDot K ≃* alternatingGroup (Fin 5))
    (hspan : K = conjugateSpanBy K (T : Subgroup G))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4) :
    let Y := sourceResidual M Mc
    let R := (F.I₂ Y).pCoreIn 2
    (pResidual 2 (F.I₂ Y)).map (F.I₂ Y).subtype = Y ∧
      R = ⁅R,Y⁆ ∧ Y.pCoreIn 2 = R ∧ Nat.card Y = 192 ∧
      ∃ c : G, c ∈ Y ∧ orderOf c = 3 ∧ R ⊓ centralizer ({c} : Set G) = ⊥ := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  let dg := Recognition.rankTwo_closure_geometry h F hne
  have hE := source_single_a5_intersection_eq_seed_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  obtain ⟨hD,hR,hQ,hc⟩ := Recognition.parabolic_residual_core_structure_of_seed_intersection
    hG T hempty hM hu hmany hcard e F dg hne g hgP hgH hE
  obtain ⟨_,hRc,_⟩ := source_single_a5_opposite_orders_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  let Y := sourceResidual M Mc
  have hQc : Nat.card (pCore 2 Y) = 64 := by
    rw [←card_map_of_injective Y.subtype_injective]
    change Nat.card (Y.pCoreIn 2) = 64
    rw [hQ]
    exact hRc
  have hY := (pCore 2 Y).card_eq_card_quotient_mul_card_subgroup
  rw [source_residual_twoCore_quotient_card hG T hempty hM hu hmany hcard e,hQc] at hY
  exact ⟨hD,hR,hQ,hY,hc⟩

end Source
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
