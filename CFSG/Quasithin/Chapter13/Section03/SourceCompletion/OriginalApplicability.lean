module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalTerminal
public import CFSG.Quasithin.Chapter14.Section03.Prelim.FaithfulSource.Hypothesis1311
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSource
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.ChosenSimpleAction
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import CFSG.Quasithin.Chapter1.Section02.Adequate.Families
public import Theory.GroupTheory.NormalModuleCore
public import Theory.SpecificGroups.SU3.BinaryG2Comparison

/-!
# Original-source applicability for the unitary exclusion

Starting with genuine Hypothesis13.3.1, the selected maximal component and
its actual chosen Irr⁺ module, the simple quotient detects O₂(L) as the
module kernel. The normal supplement calculation then identifies T∩C(V)
with O₂(LT). The universal 12.2 inputs supply reducedness, TI, uniqueness
and an escaping centralizer; natural-module transitivity moves that escape
to the original flag line. Even characteristic supplies both local
characteristic-two conditions.

These proofs discharge the local applicability premises of the terminal
argument and give a conditional exclusion of the literal PSU₃(3) matrix
quotient through the proved exceptional isomorphism. The preceding plane
centralizer theorem, maximal-escape action theorem, 13.3.14 noncentrality
and odd-local 4.4.3 control remain explicit source obligations. Thus this
module does not yet assert unconditional Theorem13.3.16.

Source: Aschbacher--Smith, 13.3.1--6 and 13.3.16--20, pp.884--886,893--896;
12.2.2 and 12.2.13, pp.795,799, combined manuscript of 1 March 2004.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup Theory.GroupTheory Chapter12.Section02 ChapterE
open Atlas.G2.Natural.BinaryPointFlag
open Chapter14.Section03.FaithfulSource
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original chosen module detects the full Sylow kernel as the literal
core of LT, once its actual component quotient is simple. -/
theorem unitary_chosen_sylow_kernel {T : Sylow 2 G} {L V : Subgroup G}
    (chosen : ChosenModule T L V) (hs : IsSimpleGroup (L ⧸ pCore 2 L))
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    (T : Subgroup G) ⊓ centralizer (V : Set G) = (L ⊔ T).pCoreIn 2 := by
  have hc : L ⊓ centralizer (V : Set G) = L.pCoreIn 2 := by
    have hm := congrArg (map L.subtype) (chosen.centralizer_eq_core_of_simple hs)
    simpa only [pCoreIn, subgroupOf_map_subtype, inf_comm] using hm
  have hLT := ambient_centralizer_eq_core_of_normal_supplement L V (T : Subgroup G)
    chosen.sylow_normalizes_component (chosen.le_sylow.trans le_sup_right)
    (sup_le chosen.normalizes hTV) T.isPGroup' hc chosen.core_centralizes
  apply le_antisymm
  · exact (inf_le_inf_right _ le_sup_right).trans hLT.le
  · refine le_inf ?_ chosen.core_centralizes
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)

/-- Transitivity transfers the original 12.2.13 escape to the actual flag line. -/
theorem unitary_original_line_escape {T : Sylow 2 G} {L V Z : Subgroup G}
    [IsElementaryAbelian 2 V]
    (h : Hypothesis1331 T L) (h1223 : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (chosen : ChosenModule T L V)
    (e : inducedAutomizer V L ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (E : Additive V ≃ₗ[ZMod 2] Atlas.G2.Natural.Space (ZMod 2))
    (he : ∀ (l : inducedAutomizer V L) v, E (automizerRepresentation V l v) =
      Atlas.G2.Natural.derivedAction (ZMod 2) (e l) (E v))
    (hZV : Z ≤ V) (hZ : Nat.card Z = 2) :
    ¬ normalizer (Z : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨v,hv,hv1,hescape⟩ := h.hypothesis1311.centralizer_escape earlier
    h1223.maximal_faithful h1223.quasisimple chosen
  have hZn : Z ≠ ⊥ := Z.one_lt_card_iff_ne_bot.mp (by omega)
  obtain ⟨z,hz1₀⟩ := ne_bot_iff_exists_ne_one.mp hZn
  have hz1 : (z : G) ≠ 1 := fun h => hz1₀ (Subtype.ext h)
  obtain ⟨l,hl,_,heq⟩ := unitary_component_transitive L e E he z v
    (hZV z.property) hv hz1 hv1
  intro hN
  have hC : centralizer ({(z : G)} : Set G) ≤ normalizer (L : Set G) :=
    (point_normalizer_eq_generator_centralizer Z hZ z z.property hz1).le.trans hN
  apply hescape
  intro y hy
  have hyc : l⁻¹ * y * l ∈ centralizer ({(z : G)} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have hyv := mem_centralizer_singleton_iff.mp hy
    rw [← heq] at hyv
    have hh := congrArg (fun a : G => l⁻¹ * a * l) hyv
    simpa only [MulAut.conj_apply, mul_assoc, inv_mul_cancel_left,
      inv_mul_cancel_right, inv_mul_cancel, mul_one] using hh
  have hlM : l ∈ normalizer (L : Set G) := L.le_normalizer hl
  have hyM := (normalizer (L : Set G)).mul_mem
    ((normalizer (L : Set G)).mul_mem hlM (hC hyc))
    ((normalizer (L : Set G)).inv_mem hlM)
  simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel_right,
    mul_inv_cancel, mul_one] using hyM

/-- The original 13.3.1 configuration supplies all local applicability and
kernel conditions for the conditional unitary terminal argument. Only the
universal earlier theorems, selected quotient/module/flag, and the four named
source obligations remain. In particular no rank, TI, uniqueness, escape,
Sylow-kernel, characteristic-two or parabolic condition is assumed. -/
theorem unitary_original_false_of_earlier_sources
    (D : ChapterF.Section09.Setup G) [IsElementaryAbelian 2 D.V]
    (h : Hypothesis1331 D.T D.L)
    (hmax : D.L ∈ Chapter1.LStar G (D.T : Subgroup G))
    (eL : (D.L ⧸ pCore 2 D.L) ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (chosen : ChosenModule D.T D.L D.V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u})
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
    (hm : ⁅D.QH,B⁆ ≠ ⊥)
    (hplanes : UnitaryPlaneCentralizers D.V (normalizer (D.L : Set G)))
    (hact : MaximalEscapeAction D.V (normalizer (D.L : Set G)))
    (hodd : UnitaryPrimeNormalizerControl D.L D.V) : False := by
  have hL := ((Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff
    D.T D.L).mp h.local_component).1
  have hf := ((Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff
    D.T D.L).mp h.local_component).2
  let : IsSimpleGroup Atlas.G2.Natural.BinaryNormalizer.Derived :=
    Atlas.G2.isSimple_commutator_binary
  let hs : IsSimpleGroup (D.L ⧸ pCore 2 D.L) := eL.isSimpleGroup
  let : Group.IsPerfect D.L := Chapter1.mem_L_isPerfect hL
  let : Group.IsPerfect (D.L ⧸ pCore 2 D.L) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (pCore 2 D.L))
  have hz : center (D.L ⧸ pCore 2 D.L) = ⊥ :=
    (inferInstance : (center (D.L ⧸ pCore 2 D.L)).Normal).eq_bot_or_eq_top.resolve_right
      (fun hz => Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp hz))
  have hq : IsQuasisimple (D.L ⧸ pCore 2 D.L) :=
    { simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans
        QuotientGroup.quotientBot).isSimpleGroup }
  have h12 := h.hypothesis1311.hypothesis1223 ⟨hmax,hf⟩ hq
  have hA := fun (X : Type u) [Group X] [Finite X] =>
    ChapterA.Section02.theoremA_knownSimple (G := X)
  have hC := fun (X : Type u) [Group X] [Finite X] =>
    ChapterA.Section02.theoremC_knownSimple (G := X)
  have hTV := ((structural G D.T D.L h12).2.2 D.V chosen).1
  have hred := ((structural G D.T D.L h12).2.2 D.V chosen).2.1
  have hfaith : D.L ⊓ centralizer (D.V : Set G) ≤ D.L.pCoreIn 2 := by
    have hc := congrArg (map D.L.subtype) (chosen.centralizer_eq_core_of_simple hs)
    exact (show D.L ⊓ centralizer (D.V : Set G) = D.L.pCoreIn 2 by
      simpa only [pCoreIn, subgroupOf_map_subtype, inf_comm] using hc).le
  have hcharL : generalizedFitting D.L = pCore 2 D.L :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2
      (Chapter1.Section02.Adequate.mem_L_hasCharacteristicTwo D.T
        (h.qtke.evenCharacteristic D.T) hL)
  have hZn : D.V₁ ≠ ⊥ := D.V₁.one_lt_card_iff_ne_bot.mp (by omega)
  have hZp : IsPGroup 2 D.V₁ := (IsElementaryAbelian.isPGroup 2 D.V).to_le hZV
  have hcharH : generalizedFitting D.H = pCore 2 D.H := by
    rw [hHfull]
    exact generalizedFitting_eq_pCore_of_selfCentralizing 2
      (Chapter1.mem_He_iff.mp (Chapter1.twoLocal_mem_He_of_sylow_le D.T
        (h.qtke.evenCharacteristic D.T) ⟨D.V₁,hZn,hZp,rfl⟩ hTZ))
  have hout : ¬ D.H ≤ normalizer (D.L : Set G) := by
    rw [hHfull]
    exact unitary_original_line_escape h h12 earlier chosen e E0 he0 hZV hZ
  exact unitary_false_of_earlier_sources D e E0 he0 hUV hZV hTZ hTU hZ hU
    ((pResidual_eq_top_iff 2 D.L).mpr
      (Chapter1.Section02.Adequate.mem_L_isPPerfect hL))
    chosen.sylow_normalizes_component hcharL
    (chosen.le_sylow.trans le_sup_right) hred
    (unitary_chosen_sylow_kernel chosen hs hTV) hcharH
    (h12.source_chosen_normalizer_le structural hA hC chosen) hfaith
    (h12.source_normalizer_maximal_unique structural hA hC).2 hout
    B hBV hTB hB hHfull hm h.qtke (h12.source_chosen_TI structural chosen)
    hplanes hact hodd

/-- The conditional original-source consumer excludes the actual PSU₃(3)
quotient. The exceptional comparison is a proved isomorphism of the projective
unitary matrix image with the binary octonion derived group. -/
theorem unitary_original_quotient_exclusion_of_earlier_sources
    (D : ChapterF.Section09.Setup G) [IsElementaryAbelian 2 D.V]
    (h : Hypothesis1331 D.T D.L)
    (hmax : D.L ∈ Chapter1.LStar G (D.T : Subgroup G))
    (chosen : ChosenModule D.T D.L D.V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u})
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
    (hm : ⁅D.QH,B⁆ ≠ ⊥)
    (hplanes : UnitaryPlaneCentralizers D.V (normalizer (D.L : Set G)))
    (hact : MaximalEscapeAction D.V (normalizer (D.L : Set G)))
    (hodd : UnitaryPrimeNormalizerControl D.L D.V) :
    ¬ ClassicalGroup.IsPSU (D.L ⧸ pCore 2 D.L) 3 3 := by
  rintro ⟨K,_,_,J,hK,hJ,⟨eJ⟩⟩
  exact unitary_original_false_of_earlier_sources D h hmax
    (eJ.trans (J.projectiveEquivBinaryG2Derived hK hJ)) chosen structural earlier
    e E0 he0 hUV hZV hTZ hTU hZ hU B hBV hTB hB hHfull hm hplanes hact hodd
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
