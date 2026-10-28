module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.FactorSelfCentralizing.ModelExclusion.WreathSquare
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.ParabolicNormalizerIntersection
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorFullAutomorphism

/-!
# The terminal four-group in the marked centralizer

For the marked point `d`, put `R = O₂(I₂)` and
`D = O₂(H) ∩ C_G(U)`.  The parabolic intersection calculation identifies the
terminal image of `R` with the elementary image of the translated factor
`X g`, of order four.  The actual dihedral supplement `D` is normalized by
`R`; its commutator with `R` lies in `U ∩ D = Z(U)`.  The elementary dihedral
calculation then conjugates `d` inside `D` without changing its terminal
image, putting every element of the terminal image in the image of the
literal marked centralizer `H ∩ C_G(d)`.

Source: Aschbacher--Smith, 14.3.20, printed pp.997--998.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Recognition
variable {G : Type*} [Group G] [Finite G]

private theorem dihedral_conjugate_of_central_difference : ∀ z d x : DihedralGroup 4,
    z ∈ center (DihedralGroup 4) → z ≠ 1 → d ^ 2 = 1 → d ≠ 1 → d ≠ z →
    x ^ 2 = 1 → x * d⁻¹ ∈ center (DihedralGroup 4) →
    ∃ c : DihedralGroup 4, c * d * c⁻¹ = x := by
  decide +kernel

theorem terminalFourSource_of_source_hypotheses
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot) :
    TerminalFourSource F (sourceResidual M Mc) := by
  intro A hA hlt P z hz hgeom hSylow hcore
  let := hA.elementary
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨dg, heU, hx, _, _, _, _⟩ := rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := heU
  let := hx
  let : Fact (IsPGroup 2 F.U) := ⟨dg.two⟩
  have hZ := source_center_eq_point_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hr := source_full_orthogonal_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  let L := sourceResidual M Mc
  let R := (F.I₂ L).pCoreIn 2
  let Q := F.H.pCoreIn 2
  let D := Q ⊓ centralizer (F.U : Set G)
  obtain ⟨hRQ, hcomm, hRP, _, hRc⟩ := parabolic_core_intersection_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg (hZ) hne g hgP hgH hr
  have hPhi : (frattini F.U).map F.U.subtype = F.Vi 1 := by
    rw [dg.frattini_point]
    exact map_subgroupOf_eq_of_le ((F.le_seed 1).trans (le_conjugateSpanBy _ _))
  have hcommU : ⁅F.U, F.U⁆ ≤ F.Vi 1 := by
    rw [← F.U.map_subtype_commutator]
    exact (map_mono (f := F.U.subtype)
      (commutator_le_frattini_of_isPGroup (p := 2))).trans hPhi.le
  have hsquare : ∀ u ∈ F.U, u ^ 2 ∈ F.Vi 1 := fun u hu =>
    hPhi ▸ mem_map_of_mem F.U.subtype
      (pth_power_mem_frattini_of_isPGroup (p := 2) (⟨u, hu⟩ : F.U))
  have hspan : F.U = conjugateSpanBy (F.Vi 2) F.H := by rw [F.last]; rfl
  obtain ⟨e₀, _, hgen, _, hIG, hIN, _, _, hfactor, hPH, hcore', hindex, _⟩ :=
    F.binary_generation (by decide) L h.L_normalizes_seed
      (h.binarySeedAction_surjective F) h.centralizer hcommU hsquare hspan hne g hgP hgH
  have hsplit : R = F.W ⊔ F.X g :=
    F.binary_core_factorization L g hgP hfactor hPH hgen.symm e₀ hcore' hindex
  have hRN : F.Gi 2 ≤ normalizer (R : Set G) :=
    ((normal_subgroupOf_iff_le_normalizer hIG).mp hIN).trans
      (normalizer_le_normalizer_characteristic_image (F.I₂ L) (pCore 2 (F.I₂ L)))
  have hRT : R ≤ (T : Subgroup G) := normalized_pSubgroup_le_sylow T (F.Gi 2) R
    (F.invariant 2) ((pCoreIn_le 2 (F.I₂ L)).trans hIG) hRN
      (isPGroup_pCoreIn 2 (F.I₂ L))
  have hTH : (T : Subgroup G) ≤ F.H := F.invariant 1
  have hQT : Q ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow F.H (T.subtype hTH)
    change Q ≤ ((T : Subgroup G).subgroupOf F.H).map F.H.subtype at hh
    rwa [map_subgroupOf_eq_of_le hTH] at hh
  have hRH : R ≤ F.H := hRT.trans hTH
  have hQH : Q ≤ F.H := pCoreIn_le 2 F.H
  have hUQ : F.U ≤ Q := le_pCoreIn_of_normalizes dg.two F.U_le_H
    (le_normalizer_conjugateSpanBy _ _)
  have hWH : F.W ≤ F.H := inf_le_left.trans F.U_le_H
  have hXH : F.X g ≤ F.H := F.X_le_H g
    (F.P_le_G₂ (by decide) L h.L_normalizes_seed hgP)
  let q := QuotientGroup.mk' F.terminalHatAction.ker
  have hqker : q.ker = pCore 2 F.H := by
    rw [QuotientGroup.ker_mk', terminal_kernel_of_center_point F dg hZ]
  have hWdot : F.terminalDot F.W = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    rw [hqker]
    intro w hw
    obtain ⟨a, ha, he⟩ := hUQ ((show F.W ≤ F.U from inf_le_left) hw)
    exact (show a = w from Subtype.ext he) ▸ ha
  have hRdot : F.terminalDot R = F.terminalDot (F.X g) := by
    change (R.subgroupOf F.H).map q = ((F.X g).subgroupOf F.H).map q
    rw [hsplit, subgroupOf_sup hWH hXH, Subgroup.map_sup]
    change F.terminalDot F.W ⊔ F.terminalDot (F.X g) = F.terminalDot (F.X g)
    rw [hWdot, bot_sup_eq]
  have hE : IsElementaryAbelian 2 (F.terminalDot R) := by
    rw [hRdot]
    infer_instance
  have hHQ : F.H ≤ normalizer (Q : Set G) := F.H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image F.H (pCore 2 F.H))
  have hHU : F.H ≤ normalizer (F.U : Set G) := le_normalizer_conjugateSpanBy _ _
  have hHD : F.H ≤ normalizer (D : Set G) :=
    (le_inf hHQ (hHU.trans (normalizer_le_normalizer_centralizer F.U))).trans
      inf_normalizer_le_normalizer_inf
  have hRD : R ≤ normalizer (D : Set G) := hRH.trans hHD
  have hQR : Q ≤ normalizer (R : Set G) := hQT.trans ((F.invariant 2).trans hRN)
  have hDR : D ≤ normalizer (R : Set G) := inf_le_left.trans hQR
  have hcommD : ⁅R, D⁆ ≤ D := by
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_left.mp hRD
  have hcommRD : ⁅R, D⁆ ≤ F.U ⊓ D := by
    refine le_inf ?_ hcommD
    intro x hx
    exact hcomm ((commutator_mono le_rfl inf_le_left) hx)
  have hzmem : z ∈ F.Vi 1 := hz.symm ▸ mem_zpowers z
  have hzU : z ∈ F.ZU := hZ.symm ▸ hzmem
  have hzD : z ∈ D :=
    ⟨hUQ (map_subtype_le (center F.U) hzU), centerIn_le_centralizer F.U hzU⟩
  have hz2 : orderOf z = 2 := by
    rw [← Nat.card_zpowers, ← hz]
    simpa using F.card 1 (by decide)
  have hz1 : z ≠ 1 := by
    intro he
    simp [he] at hz2
  have hd1 : P.element ≠ 1 := by
    intro he
    apply P.outside_factor
    change P.element ∈ A
    rw [he]
    exact A.one_mem
  have hdz : P.element ≠ z := by
    intro he
    apply P.outside_factor
    change P.element ∈ A
    rw [he]
    exact hA.seed_le (F.le_seed 1 hzmem)
  have hd2 : P.element ^ 2 = 1 := by
    rw [← P.point_order]
    exact pow_orderOf_eq_one _
  have hdD : P.element ∈ D := P.mem_supplement
  obtain ⟨eD⟩ := source_factor_supplement_dihedral_of_strict_centralizer
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A
      hA.le_core hA.seed_le hA.card hA.intersection_card hA.normalized hlt
  have hDcentral : D ≤ centralizer (F.U : Set G) := inf_le_right
  have hzC : eD (⟨z, hzD⟩ : D) ∈ center (DihedralGroup 4) := by
    rw [mem_center_iff]
    intro x
    obtain ⟨y, rfl⟩ := eD.surjective x
    rw [← map_mul, ← map_mul]
    exact congrArg eD (Subtype.ext (hDcentral y.property z (map_subtype_le (center F.U) hzU)).symm)
  have hterminal : F.terminalDot R ≤ F.terminalDot P.localCentralizer := by
    change (R.subgroupOf F.H).map q ≤
      (P.localCentralizer.subgroupOf F.H).map q
    intro x hx
    rcases hx with ⟨r, hr, rfl⟩
    have hrR : (r : G) ∈ R := hr
    have hrD : ((r : G)⁻¹ * P.element * (r : G)) ∈ D := by
      simpa using ((mem_normalizer_iff.mp (hRD (R.inv_mem hrR))) P.element).mp hdD
    let xG := (r : G)⁻¹ * P.element * (r : G)
    let xD : D := ⟨xG, hrD⟩
    let dD : D := ⟨P.element, hdD⟩
    have hx2 : xG ^ 2 = 1 := by
      dsimp [xG]
      rw [show ((r : G)⁻¹ * P.element * (r : G)) ^ 2 =
        (r : G)⁻¹ * P.element ^ 2 * (r : G) by simp only [pow_two]; group, hd2]
      simp
    have hk := hcommRD (commutator_mem_commutator (R.inv_mem hrR) hdD)
    have hkcenter : (⟨⁅(r : G)⁻¹, P.element⁆, hk.2⟩ : D) ∈ center D := by
      rw [mem_center_iff]
      intro y
      exact Subtype.ext (hDcentral y.property _ hk.1).symm
    have hxdiff : eD xD * (eD dD)⁻¹ ∈ center (DihedralGroup 4) := by
      rw [← map_inv, ← map_mul]
      have heq : xD * dD⁻¹ = ⟨⁅(r : G)⁻¹, P.element⁆, hk.2⟩ := by
        apply Subtype.ext
        dsimp [xD, dD, xG]
        simp only [commutatorElement_def, inv_inv]
      rw [heq]
      apply mem_center_iff.mpr
      intro a
      obtain ⟨b, rfl⟩ := eD.surjective a
      rw [← map_mul, ← map_mul]
      exact congrArg eD (mem_center_iff.mp hkcenter b)
    have hd2' : (eD dD) ^ 2 = 1 := by
      rw [← map_pow]
      change eD (dD ^ 2) = 1
      rw [show dD ^ 2 = 1 from Subtype.ext hd2, map_one]
    have hx2' : (eD xD) ^ 2 = 1 := by
      rw [← map_pow]
      change eD (xD ^ 2) = 1
      rw [show xD ^ 2 = 1 from Subtype.ext hx2, map_one]
    obtain ⟨c, hc⟩ := dihedral_conjugate_of_central_difference
      (eD ⟨z, hzD⟩) (eD dD) (eD xD) hzC
      (by intro hh; exact hz1 (congrArg Subtype.val
        (eD.injective (hh.trans eD.map_one.symm))))
      hd2'
      (by intro hh; exact hd1 (congrArg Subtype.val
        (eD.injective (hh.trans eD.map_one.symm))))
      (by intro hh; exact hdz (congrArg Subtype.val (eD.injective hh)))
      hx2' hxdiff
    let cD : D := eD.symm c
    have hcD : (cD : G) ∈ D := cD.property
    have hcconj : (cD : G) * P.element * (cD : G)⁻¹ = xG := by
      have hh : cD * dD * cD⁻¹ = xD := eD.injective (by
        simpa only [map_mul, map_inv, cD, eD.apply_symm_apply] using hc)
      exact congrArg Subtype.val hh
    let y := (r : G) * (cD : G)
    have hyH : y ∈ F.H := by
      exact F.H.mul_mem (hRH hrR) (hQH hcD.1)
    have hyconj : y * P.element * y⁻¹ = P.element := by
      have hh := congrArg (fun t : G => (r : G) * t * (r : G)⁻¹) hcconj
      simpa [y, xG, mul_assoc] using hh
    have hycomm : y * P.element = P.element * y := by
      calc
        y * P.element = (y * P.element * y⁻¹) * y := by simp [mul_assoc]
        _ = P.element * y := by rw [hyconj]
    have hyC : y ∈ P.localCentralizer :=
      ⟨hyH, mem_centralizer_singleton_iff.mpr hycomm⟩
    let rH : F.H := ⟨r, hRH hrR⟩
    let cH : F.H := ⟨cD, hQH hcD.1⟩
    have hcq : q cH = 1 := by
      rw [← MonoidHom.mem_ker, hqker]
      exact (mem_map_iff_mem F.H.subtype_injective).mp cD.property.1
    have hqeq : q ⟨y, hyH⟩ = q rH := by
      have heq : (⟨y, hyH⟩ : F.H) = rH * cH := by
        apply Subtype.ext
        rfl
      rw [heq, map_mul, hcq, mul_one]
    exact ⟨⟨y, hyH⟩, hyC, hqeq⟩
  exact ⟨F.terminalDot R, hterminal, hE, by simpa using hRc⟩

theorem quotientCentralizerSource_of_source_terminal_four
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (hrecognize : ∀ J E : Subgroup BinaryFourPlus.Wreath,
      pResidual 2 BinaryFourPlus.Wreath ≤ J → E ≤ J →
      IsElementaryAbelian 2 E → Nat.card E = 4 →
      ∃ S : Subgroup BinaryFourPlus.Wreath, S ≤ J ∧ S.relIndex J ≤ 2 ∧
        Nonempty (S ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))) :
    QuotientCentralizerSource F (sourceResidual M Mc) := by
  exact quotientCentralizerSource_of_terminal_four_and_wreath_recognition
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
    (terminalFourSource_of_source_hypotheses hG T hempty hM hu hmany hcard e hnot F
      hne g hgP hgH hs) hrecognize

/-- The actual quaternion extension, with the finite wreath recognition discharged. -/
theorem quotientCentralizerSource_of_source_hypotheses
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot) : QuotientCentralizerSource F (sourceResidual M Mc) := by
  exact quotientCentralizerSource_of_terminal_four
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
    (terminalFourSource_of_source_hypotheses hG T hempty hM hu hmany hcard e hnot F
      hne g hgP hgH hs)

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing
