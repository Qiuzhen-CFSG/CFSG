module
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction.Extraction.Preparation
public import CFSG.Quasithin.ChapterB.Section01.QuasisimpleSections.Group
public import Theory.GroupTheory.GeneralizedFitting.ComponentCenterPrimeCore
public import Theory.GroupTheory.SylowSubnormalIntersection
public import Theory.GroupAction.NormalComplement
public import Theory.GroupAction.TwoGroupFixedImage
public import Theory.GroupAction.SubgroupConjugation
/-!
# Quotient component extraction for E.6.19

Failure of odd-core containment produces a component D of the actual quotient
C_G(A)/(O(C_G(A)) A) with [D,Ū] = [D,O(C(Ū))] = D and V̄ ≤ N(D).
No component, balance, exceptional-model, or lifting conclusion is assumed.

The intrinsic argument uses the source Sylow geometry. If O(G) = 1, then
C_G(S ∩ E(G)) fixes every component: otherwise a Sylow subgroup of a component
would be central, contradicting Burnside transfer and its trivial odd core.
An odd subgroup R normalized by S also fixes every component. Indeed, the
two-group S ∩ E(G) acts trivially on the image of R modulo E(G), and odd-kernel
fixed-point lifting gives R ≤ E(G) C_G(S ∩ E(G)).

Generalized-Fitting self-centralization now detects a component on which the
nontrivial R = O(C(B)) acts nontrivially, since R centralizes O₂(G). Both R
and the Sylow-central B normalize this component. If B centralized it, the
normal-subgroup component dichotomy inside C(B) would force R to centralize
it as well. The component commutator dichotomy yields both full equalities.
The quotient adapter discharges every intrinsic premise using Preparation
and the genuine E.6.1 hypotheses. This step does not need the source's further
corank-two or relative-index-two restrictions.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.19,
printed p.252 (PDF p.263); Aschbacher, Finite Group Theory, second edition,
31.13–18, printed pp.159–161 (PDF pp.169–171). The central-Sylow specialization
replaces the general component-permutation and diagonal arguments of 31.17–18
by two-group fixed-point lifting. Generalized-Fitting self-centralization is
reused through the proved Chapter B bridge to Gorenstein–Walter.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction.Extraction.QuotientComponent
variable {G : Type*} [Group G] [Finite G]

private theorem quasisimple_sylow_not_central
    [IsQuasisimple G] (ho : pPrimeCore 2 G = ⊥) (P : Sylow 2 G) :
    ¬ (P : Subgroup G) ≤ center G := by
  intro hc
  obtain ⟨N, hn, hcop, hp⟩ :=
    exists_normal_coprime_subgroup_and_pgroup_quotient_of_sylow_le_center_normalizer 2 P
      (fun x hx => ⟨P.le_normalizer hx, fun y _ => mem_center_iff.mp (hc hx) y⟩)
  let _ := hn
  have hN : N = ⊥ := le_bot_iff.mp (ho ▸ (show N ≤ pPrimeCore 2 G from le_sSup ⟨hn, hcop⟩))
  have hker : (QuotientGroup.mk' N).ker = ⊥ := by rw [QuotientGroup.ker_mk', hN]
  have hg : IsPGroup 2 G := hp.of_injective (QuotientGroup.mk' N) ((MonoidHom.ker_eq_bot_iff _).mp hker)
  let _ := hg.isNilpotent
  let _ := IsQuasisimple.simple (G := G)
  let _ : Nontrivial G := (QuotientGroup.mk'_surjective (center G)).nontrivial
  exact Group.IsPerfect.not_isNilpotent G inferInstance

/-- The centralizer of a Sylow two-subgroup fixes every component when the odd core vanishes. -/
private theorem centralizer_sylow_layer_le_normalizer (ho : pPrimeCore 2 G = ⊥)
    (S : Sylow 2 G) {D : Subgroup G} (hD : IsComponent G D) :
    centralizer ((S : Subgroup G) ⊓ componentLayer G : Set G) ≤ normalizer (D : Set G) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq]
  by_contra hne
  have hc := hD.commutator_eq_bot_of_ne (hD.map_conj g) (Ne.symm hne)
  obtain ⟨P, hP⟩ := S.exists_subgroupOf_eq_of_subnormal D hD.1
  let _ := hD.2
  apply quasisimple_sylow_not_central (hD.1.pPrimeCore_eq_bot ho D) P
  intro x hx
  have hxS : (x : G) ∈ S := by
    change x ∈ (P : Subgroup D) at hx
    rw [hP] at hx
    exact hx
  have hxg : (x : G) ∈ D.map (MulAut.conj g).toMonoidHom := by
    refine ⟨x, x.property, ?_⟩
    change g * (x : G) * g⁻¹ = x
    rw [← hg x ⟨hxS, (show D ≤ componentLayer G from le_sSup hD) x.property⟩, mul_inv_cancel_right]
  rw [mem_center_iff]
  intro y
  exact Subtype.ext ((commutator_eq_bot_iff_le_centralizer.mp hc y.property) x hxg).symm

omit [Finite G] in
private theorem layer_normal : (componentLayer G).Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [le_normalizer_iff]
  intro g _ x hx
  have hmap : (componentLayer G).map (MulAut.conj g).toMonoidHom ≤ componentLayer G := by
    apply map_le_iff_le_comap.mpr
    apply sSup_le
    intro L hL
    exact map_le_iff_le_comap.mp (show L.map (MulAut.conj g).toMonoidHom ≤ componentLayer G
      from le_sSup (hL.map_conj g))
  exact hmap (mem_map_of_mem _ hx)

omit [Finite G] in
private theorem layer_le_normalizer {D : Subgroup G} (hD : IsComponent G D) :
    componentLayer G ≤ normalizer (D : Set G) := by
  apply sSup_le
  intro L hL
  by_cases he : L = D
  · exact he ▸ D.le_normalizer
  · exact (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (hD.commutator_eq_bot_of_ne hL (Ne.symm he)))).trans
      (Subgroup.centralizer_le_normalizer _)

/-- Sylow-central elements normalize every component. -/
private theorem centralizer_sylow_le_normalizer (ho : pPrimeCore 2 G = ⊥)
    (S : Sylow 2 G) {D : Subgroup G} (hD : IsComponent G D) :
    centralizer (S : Set G) ≤ normalizer (D : Set G) :=
  (Subgroup.centralizer_le inf_le_left).trans
    (centralizer_sylow_layer_le_normalizer ho S hD)

/-- An odd subgroup normalized by a full Sylow two-subgroup fixes every component. -/
private theorem odd_normalized_le_component_normalizer (ho : pPrimeCore 2 G = ⊥)
    (S : Sylow 2 G) (R : Subgroup G) (hodd : Odd (Nat.card R))
    (hn : (S : Subgroup G) ≤ normalizer (R : Set G))
    {D : Subgroup G} (hD : IsComponent G D) : R ≤ normalizer (D : Set G) := by
  let E := componentLayer G
  let _ : E.Normal := layer_normal
  let P := (S : Subgroup G) ⊓ E
  let _ : MulDistribMulAction P R :=
    conjMulDistribMulActionOfLeNormalizer P R (inf_le_left.trans hn)
  let actQ : MulDistribMulAction P (G ⧸ E) :=
    { smul := fun _ x => x
      one_smul := fun _ => rfl
      mul_smul := fun _ _ _ => rfl
      smul_one := fun _ => rfl
      smul_mul := fun _ _ _ => rfl }
  let _ : MulDistribMulAction P (G ⧸ E) := actQ
  let _ : MulAction P (G ⧸ E) := actQ.toMulAction
  let q := QuotientGroup.mk' E
  let f := q.comp R.subtype
  have hequiv : ∀ a : P, ∀ r : R, f (a • r) = a • f r := by
    intro a r
    change q ((a : G) * (r : G) * (a : G)⁻¹) = q r
    have ha : q a = 1 := (QuotientGroup.eq_one_iff _).mpr a.property.2
    simp only [map_mul, map_inv, ha, one_mul, inv_one, mul_one]
  have hf := f.map_fixedPoints_eq_of_odd_kernel (A := P)
    (S.isPGroup'.to_le (show P ≤ (S : Subgroup G) from inf_le_left)) (hodd.of_dvd_nat (card_subgroup_dvd_card f.ker)) hequiv
  intro r hr
  have hfr : f ⟨r, hr⟩ ∈ (FixedPoints.subgroup P R).map f := by
    rw [hf]
    exact ⟨⟨⟨r, hr⟩, rfl⟩, fun _ => rfl⟩
  obtain ⟨c, hc, he⟩ := hfr
  have hcP : (c : G) ∈ centralizer (P : Set G) := by
    intro a ha
    have hh := congrArg Subtype.val (hc (⟨a, ha⟩ : P))
    change a * (c : G) * a⁻¹ = c at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  have hrc : r * (c : G)⁻¹ ∈ E := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (r * (c : G)⁻¹) = 1
    change q c = q r at he
    simp only [map_mul, map_inv, he, mul_inv_cancel]
  have hcN := centralizer_sylow_layer_le_normalizer ho S hD hcP
  have hrcN := layer_le_normalizer hD hrc
  simpa only [inv_mul_cancel_right] using (normalizer (D : Set G)).mul_mem hrcN hcN

/-- A nontrivial odd subgroup centralizing O₂ moves some component. -/
private theorem exists_component_commutator_ne_bot (ho : pPrimeCore 2 G = ⊥)
    (R : Subgroup G) (hodd : Odd (Nat.card R)) (hne : R ≠ ⊥)
    (hc : R ≤ centralizer (pCore 2 G : Set G)) :
    ∃ D : Subgroup G, IsComponent G D ∧ ⁅D, R⁆ ≠ ⊥ := by
  classical
  by_contra! hn
  have hER : componentLayer G ≤ centralizer (R : Set G) := by
    exact sSup_le fun D hD => commutator_eq_bot_iff_le_centralizer.mp (hn D hD)
  have hFR : generalizedFitting G ≤ centralizer (R : Set G) := by
    rw [generalizedFitting, Fitting_eq_pcore G 2 ho]
    exact sup_le (le_centralizer_iff.mp hc) hER
  let C := centralizer (generalizedFitting G : Set G)
  let _ : (generalizedFitting G).Normal := generalizedFitting_normal
  let _ : C.Normal := inferInstance
  have hCF : C ≤ generalizedFitting G :=
    ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le
  let _ : IsMulCommutative C := ⟨⟨fun x y =>
    Subtype.ext (x.property y (hCF y.property)).symm⟩⟩
  have hp : IsPGroup 2 C := isPGroup_of_nilpotent_normal C inferInstance inferInstance ho
  obtain ⟨n, hncard⟩ := hp.exists_card_eq
  have hd : Disjoint R C := disjoint_of_coprime_natCard (by
    rw [hncard]
    exact hodd.coprime_two_right.pow_right n)
  apply hne
  apply le_bot_iff.mp
  intro r hr
  exact Subgroup.disjoint_def.mp hd hr (le_centralizer_iff.mp hFR hr)

omit [Finite G] in
private theorem component_commutator_eq_of_normalized
    {D R : Subgroup G} (hD : IsComponent G D)
    (hn : R ≤ normalizer (D : Set G)) (hne : ⁅D, R⁆ ≠ ⊥) : ⁅D, R⁆ = D := by
  rcases hD.commutator_dichotomy R with he | he
  · exact (hne he).elim
  · rw [he]
    exact le_antisymm (iSup_conjugates_le_of_le_normalizer D R D le_rfl hn)
      (le_iSup_conjugates D R)

private theorem oddCentralizer_coprime (B : Subgroup G) :
    Nat.Coprime 2 (Nat.card (oddCentralizer B)) :=
  (pPrimeCore_coprime_card (p := 2) (G := centralizer (B : Set G))).of_dvd_right
    (card_map_dvd _ _)

private theorem component_commutes_oddCentralizer_of_commutes
    (ho : pPrimeCore 2 G = ⊥) {D B : Subgroup G}
    (hD : IsComponent G D) (hc : ⁅D, B⁆ = ⊥) : ⁅D, oddCentralizer B⁆ = ⊥ := by
  let C := centralizer (B : Set G)
  have hDC : D ≤ C := commutator_eq_bot_iff_le_centralizer.mp hc
  rcases (hD.subgroupOf hDC).normal_dichotomy (pPrimeCore 2 C) with hle | he
  · have hDR : D ≤ oddCentralizer B := by
      simpa only [map_subgroupOf_eq_of_le hDC, oddCentralizer, C] using map_mono (f := C.subtype) hle
    have hcopD : Nat.Coprime 2 (Nat.card D) :=
      (oddCentralizer_coprime B).of_dvd_right (card_dvd_of_le hDR)
    have htop : (⊤ : Subgroup D) ≤ pPrimeCore 2 D :=
      le_sSup ⟨inferInstance, by simpa only [card_top] using hcopD⟩
    rw [hD.1.pPrimeCore_eq_bot ho D] at htop
    have hbot : D = ⊥ := by
      apply le_bot_iff.mp
      intro d hd
      exact congrArg Subtype.val (mem_bot.mp (htop (mem_top (⟨d, hd⟩ : D))))
    simp only [hbot, commutator_bot_left]
  · have he' := congrArg (Subgroup.map C.subtype) he
    simpa only [map_commutator, map_subgroupOf_eq_of_le hDC, Subgroup.map_bot, oddCentralizer, C] using he'

/-- The Sylow-central specialization of the component extraction in Aschbacher 31.18. -/
theorem exists_component_of_oddCentralizer
    (ho : pPrimeCore 2 G = ⊥) (S : Sylow 2 G) (B W : Subgroup G)
    (hBW : B ≤ W) (hWS : W ≤ centralizer (S : Set G))
    (hne : oddCentralizer B ≠ ⊥)
    (hcore : oddCentralizer B ≤ centralizer (pCore 2 G : Set G)) :
    ∃ D : Subgroup G, IsComponent G D ∧ ⁅D, B⁆ = D ∧
      ⁅D, oddCentralizer B⁆ = D ∧ W ≤ normalizer (D : Set G) := by
  let R := oddCentralizer B
  have hodd : Odd (Nat.card R) := (oddCentralizer_coprime B).odd_of_left
  obtain ⟨D, hD, hDR⟩ := exists_component_commutator_ne_bot ho R hodd hne hcore
  have hWN : W ≤ normalizer (D : Set G) :=
    hWS.trans (centralizer_sylow_le_normalizer ho S hD)
  have hSC : (S : Subgroup G) ≤ centralizer (B : Set G) :=
    le_centralizer_iff.mp (hBW.trans hWS)
  have hSN : (S : Subgroup G) ≤ normalizer (R : Set G) :=
    (hSC.trans (centralizer (B : Set G)).le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image _ (pPrimeCore 2 (centralizer (B : Set G))))
  have hRN : R ≤ normalizer (D : Set G) :=
    odd_normalized_le_component_normalizer ho S R hodd hSN hD
  have hDB : ⁅D, B⁆ ≠ ⊥ := fun hc =>
    hDR (component_commutes_oddCentralizer_of_commutes ho hD hc)
  exact ⟨D, hD, component_commutator_eq_of_normalized hD (hBW.trans hWN) hDB,
    component_commutator_eq_of_normalized hD hRN hDR, hWN⟩

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction.Extraction.QuotientComponent

namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction.Extraction
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V A U : Subgroup G}

/-- The quotient component required in E.6.19, with both full commutators and
normalization by the actual quotient image of V. The proof only needs the
subspace inclusions and failed odd-core containment; the source corank-two
and relative-index-two conditions are unnecessary for this step. -/
theorem exists_quotient_component
    (h : HypothesisE61 K T M V) (hA : A ∈ obstructionFamily M V)
    (hAU : A ≤ U) (hUV : U ≤ V)
    (hfail : ¬ oddCentralizer U ≤ oddCentralizer A) :
    ∃ D : Subgroup (CentralizerQuotient A), IsComponent (CentralizerQuotient A) D ∧
      ⁅D, quotientImage A U⁆ = D ∧
      ⁅D, oddCentralizer (quotientImage A U)⁆ = D ∧
      quotientImage A V ≤ normalizer (D : Set (CentralizerQuotient A)) := by
  let _ := h.elementary
  obtain ⟨S, _, _, hVS⟩ := quotient_sylow_geometry h hA
  apply QuotientComponent.exists_component_of_oddCentralizer
    (quotient_oddCore_eq_bot hA.1) S (quotientImage A U) (quotientImage A V)
    (map_mono (comap_mono hUV)) hVS
  · intro hb
    exact quotient_centralizer_oddCore_ne_bot hAU hUV hfail
      ((oddCentralizer_eq_bot_iff _).mp hb)
  · exact quotient_oddCentralizer_centralizes_twoCore h hA hUV

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction.Extraction
