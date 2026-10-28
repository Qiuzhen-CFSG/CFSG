module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryBaumann.CoreConjugates
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.CoreProduct

/-!
# The original unitary Baumann endpoint in the Frattini-small branch

The previous core-product theorem supplies Q = V × C_B(L), elementary Q,
and an escaping conjugate of V centralizing the fixed factor. That factor
is consequently central in B. The root-eight lifting theorem gives at most
two N_G(B)-conjugates of Q. Since the original Sylow subgroup normalizes Q,
the normalizer-index argument forces N_G(B) ≤ N_G(Q) ≤ N_G(L), contradicting
the original diagonal-A₅ escape. This proves the exact plane-noncentrality
premise and applies it to both original parabolic control and exclusion.

The exceptional MS93 Frattini containment remains explicit and belongs to
qt-d-13316-noncentrality. This is a conditional branch, not the unconditional
13.3.14 or 13.3.10 theorem. Final qt-d-13316-source discharges the independent
plane-centralizer and earlier universal source statements. No later ordinary
two-chief-factor contradiction is used.
Source: Aschbacher--Smith 13.3.10(2), p.888, and 13.3.14, pp.891--893.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open ChapterE Atlas.G2.Natural.BinaryPointFlag
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Noncentrality
universe u
variable {G : Type u} [Group G] [Finite G]
/-- The exceptional Frattini containment closes the original Baumann escape
and proves the literal plane commutator is nontrivial. -/
theorem unitary_original_noncentrality_of_frattini_small
    (D : ChapterF.Section09.Setup G) [IsElementaryAbelian 2 D.V]
    (h : Hypothesis1331 D.T D.L) (chosen : ChosenModule D.T D.L D.V)
    (hmax : D.L ∈ Chapter1.LStar G (D.T : Subgroup G))
    (eL : (D.L ⧸ pCore 2 D.L) ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (e : inducedAutomizer D.V D.L ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (E0 : Additive D.V ≃ₗ[F] Atlas.G2.Natural.Space F)
    (he0 : ∀ (l : inducedAutomizer D.V D.L) v,
      E0 (automizerRepresentation D.V l v) =
        Atlas.G2.Natural.derivedAction F (e l) (E0 v))
    (hUV : D.Vplus ≤ D.V) (hZV : D.V₁ ≤ D.V)
    (hTZ : (D.T : Subgroup G) ≤ normalizer (D.V₁ : Set G))
    (hTU : (D.T : Subgroup G) ≤ normalizer (D.Vplus : Set G))
    (hZ : Nat.card D.V₁ = 2) (hU : Nat.card D.Vplus = 8)
    (B : Subgroup G) (hBV : B ≤ D.V)
    (hTB : (D.T : Subgroup G) ≤ normalizer (B : Set G)) (hB : Nat.card B = 4)
    (hHfull : D.H = normalizer (D.V₁ : Set G))
    (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hplanes : UnitaryPlaneCentralizers D.V (normalizer (D.L : Set G)))
    (h1332 : Noncentrality.SupercriticalSource.Source1332OneTwo D.T)
    (fixed : OriginalFixedModule1332At D.T D.L)
    (five : OriginalAlternatingFiveModules1332At D.T D.L)
    (hsmall : let R := (D.L₁ ⊔ (D.T : Subgroup G)).pCoreIn 2
      let Y := D.L ⊔ ChapterB.baumann R
      ⁅pCore 2 Y,D.L.subgroupOf Y⁆ ≤
        (frattini (pCore 2 Y)).map (pCore 2 Y).subtype ⊔ omegaCenterIn (pCore 2 Y)) : ⁅D.QH,B⁆ ≠ ⊥ := by
  intro hc
  let R := (D.L₁ ⊔ (D.T : Subgroup G)).pCoreIn 2
  let S := ChapterB.baumann R
  let Y := D.L ⊔ S
  let Q := Y.pCoreIn 2
  let C := S ⊓ centralizer (D.L : Set G)
  obtain ⟨hprod,_,_,helem,x,hx,hext,hCA,hspan⟩ :=
    unitary_original_baumann_elementary_of_frattini_small D h chosen hmax eL structural
      e E0 he0 hUV hZV hTZ hTU hZ hU B hBV hTB hB hHfull earlier hplanes h1332 fixed five hc hsmall
  let : IsElementaryAbelian 2 Q := helem
  obtain ⟨rho,E,he,_,_,_,hVS,_,himage,_,_⟩ :=
    unitary_original_offender_images_of_plane_centrality D h chosen hmax eL structural
      e E0 he0 hUV hZV hTZ hTU hZ hU B hBV hTB hB hHfull earlier hplanes h1332 fixed five hc
  obtain ⟨_,hcore⟩ := unitary_original_baumann_core_of_plane_centrality D h chosen hmax eL structural
    e E0 he0 hUV hZV hTZ hTU hZ hU B hBV hTB hB hHfull earlier hplanes h1332 fixed five hc
  have hTN := (unitary_original_module_normalizers h hmax eL chosen structural).1
  let P := D.L₁ ⊔ (D.T : Subgroup G)
  have hRT : R ≤ (D.T : Subgroup G) := by
    have hh := pCoreIn_le_sylow P (D.T.subtype le_sup_right)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le
      (show (D.T : Subgroup G) ≤ P from le_sup_right)] using hh
  have hTR : (D.T : Subgroup G) ≤ normalizer (R : Set G) :=
    le_sup_right.trans (P.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image P (pCore 2 P)))
  have hTS : (D.T : Subgroup G) ≤ normalizer (S : Set G) :=
    hTR.trans (Stellmacher.normalizer_le_normalizer_baumann R)
  have hSN : S ≤ normalizer (D.V : Set G) := inf_le_left.trans (hRT.trans hTN)
  have hTQ : (D.T : Subgroup G) ≤ normalizer (Q : Set G) :=
    ((le_inf chosen.sylow_normalizes_component hTS).trans
      (normalizer_inf_normalizer_le_normalizer_sup D.L S)).trans
      (normalizer_le_normalizer_characteristic_image Y (pCore 2 Y))
  change Q = D.V ⊔ C at hprod
  change S = D.V.conjBy x⁻¹ ⊔ Q at hspan
  have hCQ : C ≤ Q := hprod ▸ le_sup_right
  have hCS : C ≤ centralizer (S : Set G) := by
    apply le_centralizer_iff.mpr
    rw [hspan]
    exact sup_le (le_centralizer_iff.mp hCA)
      ((le_centralizer Q).trans (centralizer_le hCQ))
  have horbit := unitary_baumann_core_conjugates D.V S Q C rho E he hSN himage
    hcore hprod hCS x⁻¹ ((normalizer _).inv_mem hx) hext
  have hn := normalizer_le_of_sylow_two_conjugates D.T S Q hTS hTQ
    x⁻¹ ((normalizer _).inv_mem hx) horbit
  have hbound := hn.trans (unitary_baumann_core_normalizer h chosen hmax eL hTN R hRT hTR hVS)
  exact unitary_original_baumann_escape D h chosen hmax eL structural e E0 he0 hUV hZV
    hTZ hTU hZ hU B hBV hTB hB hHfull earlier hplanes h1332 fixed five hc hbound

/-- The original exclusion consumer now receives proved noncentrality in
the Frattini-small branch. Its independent odd-normalizer and escape-action
inputs retain their original final assembly owner. -/
theorem unitary_original_false_of_frattini_small
    (D : ChapterF.Section09.Setup G) [IsElementaryAbelian 2 D.V]
    (h : Hypothesis1331 D.T D.L) (chosen : ChosenModule D.T D.L D.V)
    (hmax : D.L ∈ Chapter1.LStar G (D.T : Subgroup G))
    (eL : (D.L ⧸ pCore 2 D.L) ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (e : inducedAutomizer D.V D.L ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (E0 : Additive D.V ≃ₗ[F] Atlas.G2.Natural.Space F)
    (he0 : ∀ (l : inducedAutomizer D.V D.L) v,
      E0 (automizerRepresentation D.V l v) =
        Atlas.G2.Natural.derivedAction F (e l) (E0 v))
    (hUV : D.Vplus ≤ D.V) (hZV : D.V₁ ≤ D.V)
    (hTZ : (D.T : Subgroup G) ≤ normalizer (D.V₁ : Set G))
    (hTU : (D.T : Subgroup G) ≤ normalizer (D.Vplus : Set G))
    (hZ : Nat.card D.V₁ = 2) (hU : Nat.card D.Vplus = 8)
    (B : Subgroup G) (hBV : B ≤ D.V)
    (hTB : (D.T : Subgroup G) ≤ normalizer (B : Set G)) (hB : Nat.card B = 4)
    (hHfull : D.H = normalizer (D.V₁ : Set G))
    (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hplanes : UnitaryPlaneCentralizers D.V (normalizer (D.L : Set G)))
    (h1332 : Noncentrality.SupercriticalSource.Source1332OneTwo D.T)
    (fixed : OriginalFixedModule1332At D.T D.L)
    (five : OriginalAlternatingFiveModules1332At D.T D.L)
    (hsmall : let R := (D.L₁ ⊔ (D.T : Subgroup G)).pCoreIn 2
      let Y := D.L ⊔ ChapterB.baumann R
      ⁅pCore 2 Y,D.L.subgroupOf Y⁆ ≤
        (frattini (pCore 2 Y)).map (pCore 2 Y).subtype ⊔ omegaCenterIn (pCore 2 Y))
    (hact : MaximalEscapeAction D.V (normalizer (D.L : Set G)))
    (hodd : UnitaryPrimeNormalizerControl D.L D.V) : False := by
  have hm := unitary_original_noncentrality_of_frattini_small D h chosen hmax eL structural e E0 he0 hUV hZV
    hTZ hTU hZ hU B hBV hTB hB hHfull earlier hplanes h1332 fixed five hsmall
  exact unitary_original_false_of_earlier_sources D h hmax eL chosen structural earlier
    e E0 he0 hUV hZV hTZ hTU hZ hU B hBV hTB hB hHfull hm hplanes hact hodd

/-- The original13.3.15/17 parabolic-control consumer, with its exact
plane movement premise proved under the exceptional Frattini containment. -/
theorem unitary_original_parabolic_control_of_frattini_small
    (D : ChapterF.Section09.Setup G) [IsElementaryAbelian 2 D.V]
    (h : Hypothesis1331 D.T D.L) (chosen : ChosenModule D.T D.L D.V)
    (hmax : D.L ∈ Chapter1.LStar G (D.T : Subgroup G))
    (eL : (D.L ⧸ pCore 2 D.L) ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (e : inducedAutomizer D.V D.L ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (E0 : Additive D.V ≃ₗ[F] Atlas.G2.Natural.Space F)
    (he0 : ∀ (l : inducedAutomizer D.V D.L) v,
      E0 (automizerRepresentation D.V l v) =
        Atlas.G2.Natural.derivedAction F (e l) (E0 v))
    (hUV : D.Vplus ≤ D.V) (hZV : D.V₁ ≤ D.V)
    (hTZ : (D.T : Subgroup G) ≤ normalizer (D.V₁ : Set G))
    (hTU : (D.T : Subgroup G) ≤ normalizer (D.Vplus : Set G))
    (hZ : Nat.card D.V₁ = 2) (hU : Nat.card D.Vplus = 8)
    (B : Subgroup G) (hBV : B ≤ D.V)
    (hTB : (D.T : Subgroup G) ≤ normalizer (B : Set G)) (hB : Nat.card B = 4)
    (hHfull : D.H = normalizer (D.V₁ : Set G))
    (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hplanes : UnitaryPlaneCentralizers D.V (normalizer (D.L : Set G)))
    (h1332 : Noncentrality.SupercriticalSource.Source1332OneTwo D.T)
    (fixed : OriginalFixedModule1332At D.T D.L)
    (five : OriginalAlternatingFiveModules1332At D.T D.L)
    (hsmall : let R := (D.L₁ ⊔ (D.T : Subgroup G)).pCoreIn 2
      let Y := D.L ⊔ ChapterB.baumann R
      ⁅pCore 2 Y,D.L.subgroupOf Y⁆ ≤
        (frattini (pCore 2 Y)).map (pCore 2 Y).subtype ⊔ omegaCenterIn (pCore 2 Y)) :
    centralizer (D.Vplus : Set G) ≤ normalizer (D.V : Set G) ∧
      D.H ⊓ normalizer (D.Vplus : Set G) ≤ normalizer (D.V : Set G) := by
  have hm := unitary_original_noncentrality_of_frattini_small D h chosen hmax eL
    structural e E0 he0 hUV hZV hTZ hTU hZ hU B hBV hTB hB hHfull earlier hplanes
    h1332 fixed five hsmall
  have h12 := unitary_original_hypothesis1223 h hmax eL
  have hred := ((structural G D.T D.L h12).2.2 D.V chosen).2.1
  have hNL := (unitary_original_module_normalizers h hmax eL chosen structural).2
  let : IsSimpleGroup Atlas.G2.Natural.BinaryNormalizer.Derived :=
    Atlas.G2.isSimple_commutator_binary
  have hfaith : D.L ⊓ centralizer (D.V : Set G) ≤ D.L.pCoreIn 2 := by
    have hc := congrArg (map D.L.subtype) (chosen.centralizer_eq_core_of_simple eL.isSimpleGroup)
    exact (show D.L ⊓ centralizer (D.V : Set G) = D.L.pCoreIn 2 by
      simpa only [pCoreIn,subgroupOf_map_subtype,inf_comm] using hc).le
  exact unitary_original_parabolic_control D e E0 he0 hUV hZV hTZ hTU hZ hU
    ((pResidual_eq_top_iff 2 D.L).mpr (Chapter1.Section02.Adequate.mem_L_isPPerfect hmax.1))
    chosen.sylow_normalizes_component (chosen.le_sylow.trans le_sup_right) hred hNL hfaith
    B hBV hTB hB hHfull hm (h12.source_chosen_TI structural chosen)
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
