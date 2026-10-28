module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureOddCore
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryPureCore
public import Theory.GroupTheory.GeneralizedFitting.ComponentExclusion
public import Theory.GroupTheory.GeneralizedFitting.NoComponentInverter

/-!
# The original pure-line odd core and minimal component obstruction

For either marked factor, the literal residual L₁ = O²(C_L(Z₁)) moves a
subgroup of corank at most two in W. The original r ≥ 3 theorem puts its
centralizer in M. A.1.26 and characteristic two of H ∩ M then prove O(H)=1
for every L₁T₁ ≤ H ≤ C_G(Z₁).

The actual offender's pure-line centralizer is already known to fail
characteristic two under w ≤ 1. Minimal descent selects the source (H1)
overgroup H with O(H)=1 and an ordinary component K outside M. Minimality
proves H = ⟨K,L₁T₁⟩. The residual moved subgroup normalizes K and acts
nontrivially. The selected central line lies in O₂(H), and C_T(Z₁) is
realized as a Sylow subgroup of H by the original centralizer placement.

This does not assert faithful action on the full residual moved subgroup;
the source faithful rank-four action, ordinary-component exclusion,
Proposition 7.7.2, w ≤ 1 and the remaining doubled rows are still required.
The full residual movement must not be identified with the source's
rank-four paired-plane movement without a separate proof.

Source: Aschbacher–Smith A.1.26 and §7.7.3, printed pp.705–706,
refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource Chapter7 ChapterE
open DoubledBinaryLocalCore DoubledBinaryPureFactors DoubledBinaryPureOddCore
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Both original marked factors have the same pure-line residual index
bound, with the graph action retaining the given seed conjugator. -/
theorem sourceOrbit_binary_pureLine_residual_index
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    (t : G) (ht : t ∈ (T : Subgroup G)) (hnt : t ∉ normalizer (V : Set G))
    (Z : Subgroup G) (hZ : Nat.card Z = 2)
    (hpure : Z ≤ V ∨ Z ≤ V.map (MulAut.conj t).toMonoidHom) :
    (⁅D.sourceOrbit,localResidual L Z⁆).relIndex D.sourceOrbit ≤ 4 := by
  let W := D.sourceOrbit
  let Vt := V.map (MulAut.conj t).toMonoidHom
  have hVW : V ≤ W := by
    change V ≤ D.sourceOrbit
    rw [D.sourceOrbit_eq]
    exact le_componentOrbit V (T : Subgroup G)
  have hVtW : Vt ≤ W := (map_mono hVW).trans_eq
    (mem_normalizer_iff_map_conj_eq.mp (D.sourceOrbit_weakClosure_setup.normalizes ht))
  obtain ⟨t₀,_,_,q,hq,E,a,hE,_,hinner,hcov,hV,hVt₀⟩ :=
    D.sourceOrbit_binary_automizer_model h hd F hF hmodel
  let tN : normalizer (W : Set G) := ⟨t,D.sourceOrbit_weakClosure_setup.normalizes ht⟩
  have hother : Vt = V.map (MulAut.conj t₀).toMonoidHom :=
    outer_conjugate_eq W V _ hVW
      (card_map_of_injective (MulAut.conj t₀).injective).symm E a hcov hV hVt₀ tN
      (fun hi => hnt ((hinner tN).mp hi))
  have hVt : ∀ w, (E w).1 = 0 ↔ (w.toMul : G) ∈ Vt := by
    intro w
    rw [hother]
    exact hVt₀ w
  rcases hpure with hZV | hZVt
  · exact naturalLine_residual_relIndex_le_four W L V Z
      D.sourceOrbit_component_normalizes hVW q hq E hE hV hZ hZV
  · let E' := E.trans BinaryLinearThree.NaturalDual.graphSwap
    let q' := BinaryLinearThree.AutomorphismAction.graph.toMonoidHom.comp q
    have hE' (l : L) (w : Additive W) :
        E' (automizerRepresentation W (W.normalizerMonoidHom.rangeRestrict
          (inclusion D.sourceOrbit_component_normalizes l)) w) =
            BinaryLinearThree.NaturalDual.action (q' l) (E' w) := by
      change BinaryLinearThree.NaturalDual.graphSwap (E _) =
        BinaryLinearThree.NaturalDual.action (BinaryLinearThree.AutomorphismAction.graph (q l))
          (BinaryLinearThree.NaturalDual.graphSwap (E w))
      have he : E (automizerRepresentation W (W.normalizerMonoidHom.rangeRestrict
          (inclusion D.sourceOrbit_component_normalizes l)) w) =
            BinaryLinearThree.NaturalDual.action (q l) (E w) := hE l w
      rw [he,BinaryLinearThree.NaturalDual.graphSwap_covariance]
    have hA' (w : Additive W) : (E' w).2 = 0 ↔ (w.toMul : G) ∈ Vt := by
      change BinaryLinearThree.AutomorphismAction.graphNaturalDual.toLinearEquiv (E w).1 = 0 ↔ _
      rw [LinearEquiv.map_eq_zero_iff]
      exact hVt w
    exact naturalLine_residual_relIndex_le_four W L Vt Z
      D.sourceOrbit_component_normalizes hVtW q'
      (BinaryLinearThree.AutomorphismAction.graph.surjective.comp hq) E' hE' hA' hZ hZVt

/-- The original r ≥ 3 theorem controls the centralizer of the actual
pure-line residual's moved subgroup, in both marked orientations. -/
theorem sourceOrbit_binary_pureLine_moved_centralizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    (hnon : D.SourceOrbitNonFF)
    (t : G) (ht : t ∈ (T : Subgroup G)) (hnt : t ∉ normalizer (V : Set G))
    (Z : Subgroup G) (hZ : Nat.card Z = 2)
    (hpure : Z ≤ V ∨ Z ≤ V.map (MulAut.conj t).toMonoidHom) :
    subgroupCorank D.sourceOrbit ⁅D.sourceOrbit,localResidual L Z⁆ ≤ 2 ∧
      centralizer ((⁅D.sourceOrbit,localResidual L Z⁆ : Subgroup G) : Set G) ≤
        normalizer (L : Set G) := by
  have hi := D.sourceOrbit_binary_pureLine_residual_index h hd F hF hmodel t ht hnt Z hZ hpure
  have hc : subgroupCorank D.sourceOrbit ⁅D.sourceOrbit,localResidual L Z⁆ ≤ 2 := by
    change Nat.log 2 _ ≤ 2
    exact (Nat.log_mono_right hi).trans (by decide : Nat.log 2 4 ≤ 2)
  have hAW : ⁅D.sourceOrbit,localResidual L Z⁆ ≤ D.sourceOrbit :=
    le_normalizer_iff_commutator_le_left.mp
      ((map_subtype_le _).trans (inf_le_left.trans D.sourceOrbit_component_normalizes))
  refine ⟨hc,?_⟩
  rw [← D.sourceOrbit_normalizer_eq_of_markedDoubled h hd]
  apply centralizer_le_normalizer_of_corank_lt_globalR hAW
  have hr := D.sourceOrbit_binary_three_le_globalR h hd hnon F hF hmodel
  exact lt_of_lt_of_le (lt_of_le_of_lt (by exact_mod_cast hc) (by decide : (2 : ℕ∞) < 3)) hr

/-- Every original pure-line local-base overgroup has trivial odd core.
Its SQTK inheritance and characteristic-two intersection with M are retained
for the subsequent ordinary-component argument. -/
theorem sourceOrbit_binary_pureLine_overgroup_structure
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    (hnon : D.SourceOrbitNonFF)
    (t : G) (ht : t ∈ (T : Subgroup G)) (hnt : t ∉ normalizer (V : Set G))
    (Z : Subgroup G) (hZ : Nat.card Z = 2)
    (hpure : Z ≤ V ∨ Z ≤ V.map (MulAut.conj t).toMonoidHom)
    (H : Subgroup G) (hBH : localBase L (T : Subgroup G) Z ≤ H)
    (hHC : H ≤ centralizer (Z : Set G)) :
    IsSQTK KnownSimple.IsKnownSimple H ∧
      HasCharacteristicTwo (H ⊓ normalizer (L : Set G) : Subgroup G) ∧
      pPrimeCore 2 H = ⊥ := by
  let W := D.sourceOrbit
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let M := normalizer (L : Set G)
  have hTM : (T : Subgroup G) ≤ M := D.sylow_normalizes_component
  have hVW : V ≤ W := by
    change V ≤ D.sourceOrbit
    rw [D.sourceOrbit_eq]
    exact le_componentOrbit V (T : Subgroup G)
  have hZW : Z ≤ W := hpure.elim (fun hh => hh.trans hVW) (fun hh =>
    (hh.trans (map_mono hVW)).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (D.sourceOrbit_weakClosure_setup.normalizes ht)))
  have hQT : Q ≤ (T : Subgroup G) ⊓ centralizer (W : Set G) := by
    have he : (T : Subgroup G) ⊓ centralizer (W : Set G) = Q := by
      dsimp only [W,Q]
      simpa only [D.sourceOrbit_eq] using D.doubledOrbit_sylow_centralizer h
    exact he.symm.le
  have hQH : Q ≤ H :=
    hQT.trans ((inf_le_inf_left (T : Subgroup G) (centralizer_le hZW)).trans
      (le_sup_right.trans hBH))
  have hWH : W ≤ H := (D.sourceOrbit_core_normalizer h).1.trans hQH
  have hZne : Z ≠ ⊥ := by
    intro he
    rw [he,card_bot] at hZ
    omega
  have hMQ : M.pCoreIn 2 ≤ Q := DoubledBinarySylow.core_le_of_sylow_base (T.subtype hTM)
    (by rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTM]; exact le_sup_right)
    (sup_le L.le_normalizer hTM)
  have hMHne : H ⊓ M ≠ ⊥ := by
    intro he
    have hWM : W ≤ M := D.sourceOrbit_weakClosure_setup.le_sylow.trans hTM
    exact hZne (le_bot_iff.mp (he ▸ le_inf (hZW.trans hWH) (hZW.trans hWM)))
  have h61 := D.sourceOrbit_hypothesisE61_of_markedDoubled h hd
  have hMH : HasCharacteristicTwo (H ⊓ M : Subgroup G) := Chapter1.mem_He_iff.mp
    (Chapter1.lemma_1_1_4_5 T (h.simpleQTKE.evenCharacteristic T) h61.maximalTwoLocal hTM
      hMHne inf_le_right
      (inf_le_left.trans (le_inf (hMQ.trans hQH) (pCoreIn_le 2 M))))
  have hHN : H ≤ normalizer (Z : Set G) := hHC.trans (Subgroup.centralizer_le_normalizer _)
  have hs := (h.simpleQTKE.twoLocal_sqtk (show IsTwoLocal (normalizer (Z : Set G)) from
    ⟨Z,hZne,(IsElementaryAbelian.isPGroup 2 W).to_le hZW,rfl⟩)).subgroup
      (H.subgroupOf (normalizer (Z : Set G)))
  have hSQ : IsSQTK KnownSimple.IsKnownSimple H :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hHN)).mp hs
  refine ⟨hSQ,hMH,?_⟩
  exact oddCore_eq_bot_of_moved_centralizer W (localResidual L Z) H M
    (isPPerfect_embedded_pResidual 2 (L ⊓ centralizer (Z : Set G)))
    ((map_subtype_le _).trans (inf_le_left.trans D.sourceOrbit_component_normalizes))
    hWH (le_sup_left.trans hBH)
    (D.sourceOrbit_binary_pureLine_moved_centralizer h hd F hF hmodel hnon t ht hnt Z hZ hpure).2
    hSQ.stronglyQuasithin hMH

/-- Minimal non-characteristic-two descent, with the original local base.
Every resulting component escapes M and generates H together with that base.
The literal residual movement normalizes and moves the selected component. -/
theorem sourceOrbit_binary_pureLine_minimal_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    (hnon : D.SourceOrbitNonFF)
    (t : G) (ht : t ∈ (T : Subgroup G)) (hnt : t ∉ normalizer (V : Set G))
    (Z : Subgroup G) (hZ : Nat.card Z = 2)
    (hpure : Z ≤ V ∨ Z ≤ V.map (MulAut.conj t).toMonoidHom)
    (hnc : ¬ HasCharacteristicTwo (centralizer (Z : Set G))) :
    let B := localBase L (T : Subgroup G) Z
    ∃ H : Subgroup G, B ≤ H ∧ H ≤ centralizer (Z : Set G) ∧
      ¬ HasCharacteristicTwo H ∧
      (∀ J : Subgroup G, B ≤ J → J < H → HasCharacteristicTwo J) ∧
      IsSQTK KnownSimple.IsKnownSimple H ∧
      HasCharacteristicTwo (H ⊓ normalizer (L : Set G) : Subgroup G) ∧
      pPrimeCore 2 H = ⊥ ∧
      ∃ K : Subgroup G, IsComponentIn K H ∧ ¬ K ≤ normalizer (L : Set G) ∧
        H = K ⊔ B ∧
        ⁅D.sourceOrbit,localResidual L Z⁆ ≤ normalizer (K : Set G) ∧
        ¬ ⁅D.sourceOrbit,localResidual L Z⁆ ≤ centralizer (K : Set G) := by
  classical
  dsimp only
  let B := localBase L (T : Subgroup G) Z
  let C := centralizer (Z : Set G)
  have hBC : B ≤ C := sup_le ((map_subtype_le _).trans inf_le_right) inf_le_right
  let S : Set (Subgroup G) := {H | B ≤ H ∧ H ≤ C ∧ ¬ HasCharacteristicTwo H}
  obtain ⟨H,hH⟩ := (Set.toFinite S).exists_minimalFor id S ⟨C,hBC,le_rfl,hnc⟩
  have hBH : B ≤ H := hH.1.1
  have hHC : H ≤ C := hH.1.2.1
  have hNH : ¬ HasCharacteristicTwo H := hH.1.2.2
  have hmin (J : Subgroup G) (hBJ : B ≤ J) (hJH : J < H) :
      HasCharacteristicTwo J := by
    by_contra hn
    exact hJH.not_ge (hH.2 ⟨hBJ,hJH.le.trans hHC,hn⟩ hJH.le)
  obtain ⟨hSQ,hMH,hodd⟩ := D.sourceOrbit_binary_pureLine_overgroup_structure
    h hd F hF hmodel hnon t ht hnt Z hZ hpure H hBH hHC
  have hex : ∃ K : Subgroup H, IsComponent H K := by
    by_contra hn
    push Not at hn
    apply hNH
    change centralizer (pCore 2 H : Set H) ≤ pCore 2 H
    have hh := centralizer_core_product_le_of_no_components 2 hn
    simpa only [hodd,sup_bot_eq] using hh
  obtain ⟨K₀,hK₀⟩ := hex
  let K := K₀.map H.subtype
  have hK : IsComponentIn K H := by
    refine ⟨map_subtype_le _,?_⟩
    change IsComponent H ((K₀.map H.subtype).comap H.subtype)
    rwa [comap_map_eq_self_of_injective H.subtype_injective]
  have hKM : ¬ K ≤ normalizer (L : Set G) := by
    intro hKM
    exact not_isComponent_of_twoCore hMH _ (hK.restrict (le_inf hK.1 hKM) inf_le_left).2
  have hgen : H = K ⊔ B := by
    have hJH : K ⊔ B ≤ H := sup_le hK.1 hBH
    apply le_antisymm _ hJH
    apply hH.2 ⟨le_sup_right,hJH.trans hHC,?_⟩ hJH
    intro hc
    exact not_isComponent_of_twoCore hc _ (hK.restrict le_sup_left hJH).2
  have hVW : V ≤ D.sourceOrbit := by
    rw [D.sourceOrbit_eq]
    exact le_componentOrbit V (T : Subgroup G)
  have hZW : Z ≤ D.sourceOrbit := hpure.elim (fun hh => hh.trans hVW) (fun hh =>
    (hh.trans (map_mono hVW)).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (D.sourceOrbit_weakClosure_setup.normalizes ht)))
  have hWH : D.sourceOrbit ≤ H := (le_inf D.sourceOrbit_weakClosure_setup.le_sylow
    ((le_centralizer D.sourceOrbit).trans (centralizer_le hZW))).trans
      (le_sup_right.trans hBH)
  have hnorm := DoubledBinaryIntersection.residual_movement_normalizes_component
    H D.sourceOrbit (localResidual L Z) K hSQ.stronglyQuasithin hK hWH
    (le_sup_left.trans hBH) (isPPerfect_embedded_pResidual 2 (L ⊓ centralizer (Z : Set G)))
  refine ⟨H,hBH,hHC,hNH,hmin,hSQ,hMH,hodd,K,hK,hKM,hgen,hnorm,?_⟩
  intro hfix
  exact hKM ((le_centralizer_iff.mp hfix).trans
    (D.sourceOrbit_binary_pureLine_moved_centralizer h hd F hF hmodel hnon t ht hnt Z hZ hpure).2)

/-- The actual offender produces the precise minimal H of source (H1),
with trivial odd core and a nontrivially acted-on ordinary component.
The bound w ≤ 1 is still explicit; no new local callback is assumed. -/
theorem sourceOrbit_binary_exists_pureLine_minimal_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    (hnon : D.SourceOrbitNonFF) (hw : globalW D.sourceOrbit T ≤ 1) :
    ∃ g : G, IsWOffenderAt D.sourceOrbit T g ∧
      ∃ t : G, t ∈ (T : Subgroup G) ∧ t ∉ normalizer (V : Set G) ∧
        let Z := ⁅offenderNormalizer D.sourceOrbit g,offenderFixedSpan D.sourceOrbit g⁆
        let C := centralizer (Z : Set G)
        let B := localBase L (T : Subgroup G) Z
        Nat.card Z = 2 ∧ (Z ≤ V ∨ Z ≤ V.map (MulAut.conj t).toMonoidHom) ∧
        Z ≤ D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj g).toMonoidHom ∧
        D.sourceOrbit ⊔ D.sourceOrbit.map (MulAut.conj g).toMonoidHom ≤ C ∧
        (∃ P : Sylow 2 C, (P : Subgroup C).map C.subtype = (T : Subgroup G) ⊓ C) ∧
        pPrimeCore 2 C = ⊥ ∧
        ∃ H : Subgroup G, B ≤ H ∧ H ≤ C ∧ ¬ HasCharacteristicTwo H ∧
          (∀ J : Subgroup G, B ≤ J → J < H → HasCharacteristicTwo J) ∧
          IsSQTK KnownSimple.IsKnownSimple H ∧
          HasCharacteristicTwo (H ⊓ normalizer (L : Set G) : Subgroup G) ∧
          pPrimeCore 2 H = ⊥ ∧ Z ≤ H.pCoreIn 2 ∧
          (∃ S : Sylow 2 H, (S : Subgroup H).map H.subtype = (T : Subgroup G) ⊓ C) ∧
          ∃ K : Subgroup G, IsComponentIn K H ∧ ¬ K ≤ normalizer (L : Set G) ∧
            H = K ⊔ B ∧
            ⁅D.sourceOrbit,localResidual L Z⁆ ≤ normalizer (K : Set G) ∧
            ¬ ⁅D.sourceOrbit,localResidual L Z⁆ ≤ centralizer (K : Set G) := by
  obtain ⟨g,hg,t,ht,hnt,hZ,hpure,hpair,hcentral,hP,hnc⟩ :=
    D.sourceOrbit_binary_exists_pureLine_not_characteristicTwo h hd F hF hmodel hnon hw
  let Z := ⁅offenderNormalizer D.sourceOrbit g,offenderFixedSpan D.sourceOrbit g⁆
  let C := centralizer (Z : Set G)
  have hBC : localBase L (T : Subgroup G) Z ≤ C :=
    sup_le ((map_subtype_le _).trans inf_le_right) inf_le_right
  have hodd := (D.sourceOrbit_binary_pureLine_overgroup_structure
    h hd F hF hmodel hnon t ht hnt Z hZ hpure C hBC le_rfl).2.2
  obtain ⟨H,hBH,hHC,hNH,hmin,hSQ,hMH,hoddH,hK⟩ :=
    D.sourceOrbit_binary_pureLine_minimal_component h hd F hF hmodel hnon t ht hnt Z hZ hpure hnc
  have hZW : Z ≤ D.sourceOrbit := hpair.trans inf_le_left
  have hZB : Z ≤ localBase L (T : Subgroup G) Z :=
    (le_inf (hZW.trans D.sourceOrbit_weakClosure_setup.le_sylow)
      (hZW.trans ((le_centralizer D.sourceOrbit).trans (centralizer_le hZW)))).trans le_sup_right
  have hcore : Z ≤ H.pCoreIn 2 := le_pCoreIn_of_normalizes
    ((IsElementaryAbelian.isPGroup 2 D.sourceOrbit).to_le hZW) (hZB.trans hBH)
    (hHC.trans (Subgroup.centralizer_le_normalizer _))
  obtain ⟨P,hP⟩ := hP
  obtain ⟨S,hS⟩ := DoubledBinarySylow.sylow_between hHC P
    (hP.trans_le (le_sup_right.trans hBH))
  exact ⟨g,hg,t,ht,hnt,hZ,hpure,hpair,hcentral,⟨P,hP⟩,hodd,
    H,hBH,hHC,hNH,hmin,hSQ,hMH,hoddH,hcore,⟨S,hS.trans hP⟩,hK⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
