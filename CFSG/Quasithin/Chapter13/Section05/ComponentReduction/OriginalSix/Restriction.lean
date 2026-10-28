module
public import Theory.GroupTheory.IndexTwoSeedKernel
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Normalizers
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceElimination
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# F.9 on the actual normalizer intersection

For an escaping subgroup of the selected H containing L₁T, the selected
F.9 hypothesis already gives commutator lifting and normalizer control.
The original maximal local component supplies uniqueness and the normalizer
of V. The index-two seed kernel argument therefore supplies the remaining
normal-core bound. This is the F.9 application needed at N_H(L₁), without a
universal family of independent F.9 hypotheses.
Source: Aschbacher–Smith13.5.7 and13.5.19, printed pp.918 and922.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix
open Section08.SourceCompletion PlaneGeometry.TwoBlocks
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz) (h : D.Hypothesis)
  (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
include d e

/-- Faithfulness of the literal natural quotient bounds its ambient kernel. -/
theorem local_centralizer_le_core :
    D.L ⊓ centralizer (D.V : Set G) ≤ D.L.pCoreIn 2 := by
  intro x hx
  let l : D.L := ⟨x,hx.1⟩
  have he : localMap d l = 1 := by
    apply BinaryPermutation.naturalRepresentation_injective (Fin 6) (by decide)
    rw [map_one]
    ext w : 1
    obtain ⟨v,hv⟩ := d.coordinate.surjective (Multiplicative.ofAdd w)
    have hv' : (d.coordinate v).toAdd = w := hv
    rw [←hv']
    have hc := d.conjugation l v
    change (d.coordinate (D.V.normalizerMonoidHom
      ⟨l.val,d.normalizes_V (mem_sup_left l.property)⟩ v)).toAdd =
      BinaryPermutation.naturalRepresentation (Fin 6) (localMap d l) (d.coordinate v).toAdd at hc
    rw [←hc]
    apply congrArg (fun v : D.V => (d.coordinate v).toAdd)
    apply Subtype.ext
    change x*v.val*x⁻¹=v.val
    rw [←hx.2 v.val v.property,mul_inv_cancel_right]
  have hk : l ∈ (localMap d).ker := he
  rw [NormalBranch.SourceBarred.local_kernel_eq_core d e] at hk
  exact mem_map_of_mem D.L.subtype hk

include h
/-- Restrict the original F.9 application to the actual escaping overgroup.
The maximal-local hypothesis is used only for its source uniqueness theorem. -/
theorem restricted_hypothesis
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T D.L)
    (J : Subgroup G)
    (hJ : J ∈ Section08.Source.Hz D.L₁ D.T (normalizer (D.V₁ : Set G)) M)
    (hJH : J ≤ D.H) :
    ({D with H := J} : ChapterF.Section09.Setup G).Hypothesis := by
  have hlocal : D.L₁ ⊔ (D.T : Subgroup G) ≤ J := hJ.1.2
  have hTJ : (D.T : Subgroup G) ≤ J := le_sup_right.trans hlocal
  have hVJ : D.V ≤ J := h.V_le_T.trans hTJ
  have hJC : J ≤ D.Gz := hJH.trans h.H_centralizes
  have hHe : J ∈ Chapter1.He G := Chapter1.lemma_1_1_4_6 D.T
    (d.counterexample.qtke.evenCharacteristic D.T) ⟨hJ.1.1,hTJ⟩
  have hchar : generalizedFitting J = pCore 2 J :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2 (Chapter1.mem_He_iff.mp hHe)
  have hNL : normalizer (D.V : Set G) ≤ normalizer (D.L : Set G) :=
    h1221.normal_subgroup_normalizer_le d.normalizes_L h.V_le_LT d.chosen.ne_bot d.normalizes_V
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h1221.simpleQTKE D.T h1221.maximal_faithful.1
  have he : componentOrbit D.L (D.T : Subgroup G) = D.L :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer D.L D.T D.L le_rfl d.normalizes_L)
      (le_componentOrbit D.L D.T)
  have huniq : ∀ N : Subgroup G, IsMaximalTwoLocal N → D.LT ≤ N → N = M := by
    simpa only [ChapterF.Section09.Setup.LT,he,←d.local_normalizer] using hu.normalizer_unique
  have hcontrol : J ⊓ normalizer (D.Vplus : Set G) ≤ normalizer (D.V : Set G) := by
    intro x hx
    exact (h.normalizer_control ⟨hJH hx.1,hx.2⟩).2
  refine {
    elementary := h.elementary
    residual := h.residual
    normalizes_L := h.normalizes_L
    characteristic_L := h.characteristic_L
    V_le_LT := h.V_le_LT
    reduced := h.reduced
    sylow_centralizer := h.sylow_centralizer
    point_card := h.point_card
    normalizes_point := h.normalizes_point
    point_lt := h.point_lt
    plus_le := h.plus_le
    H_centralizes := hJC
    local_le := hlocal
    characteristic_H := hchar
    kernel_core := ?_
    local_normalizes := h.local_normalizes
    irreducible := h.irreducible
    normalizer_control := le_inf inf_le_left hcontrol
    generated_core := sup_twoCore_eq_bot_of_unique D.LT J M huniq hJ.2.2
    commutator_lifting := fun g hg => h.commutator_lifting g (hJH hg) }
  exact normalCore_point_kernel_le_of_index_two D.T D.L J M D.V D.Vplus D.V₁
    h.elementary.isPGroup h.plus_le (NormalBranch.SourceOrthogonal.seed_index d)
    hVJ h.point_lt.le hJC hcontrol hTJ d.normalizes_L
    (le_sup_left.trans d.normalizes_V) hNL (local_centralizer_le_core d e)
    huniq hJ.2.2 hHe
end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix
