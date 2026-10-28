module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationStrictDisplacement
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedWeakClosureRanks
public import Theory.GroupTheory.NormalSubgroupCoreQuotient

/-!
# The generated layer and its two-core in the strict branch

An automizer of the natural four-dimensional layer cannot fix a hyperplane
unless it fixes the whole layer. Consequently Z(U) centralizes V and its
H-normal closure K. An element of K in the kernel on U/Z(U) fixes both Z(U)
and U/Z(U); the automorphism-pair kernel is a two-group. The original action
kernel on U/⟨z⟩ then puts this entire kernel inside O₂(H).

Together with the reverse inclusion, this identifies the kernel of
K → H/C_H(U/Z(U)) with O₂(K), and constructs K/O₂(K) ≃ K-dot using
the literal quotient map, with its evaluation formula.

Source: Aschbacher--Smith, 6.2.15(3) and 6.2.16(3), printed pp.688--689.
The strict contradiction remains with this task; LocalAnalysis is discharged
by qt-d-1222-rankone-recognition-identification.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G] [Finite G]
  {κ : GroupClass.{u}} {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

theorem LocalAnalysis.strict_hyperplane_centralizer
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    (D : Subgroup G) (hDN : D ≤ normalizer (layer L R : Set G))
    (hDI : D ≤ centralizer (sourceClosure (T : Subgroup G) L R z ⊓ layer L R : Set G)) :
    D ≤ centralizer (layer L R : Set G) := by
  let V := layer L R
  let I := sourceClosure (T : Subgroup G) L R z ⊓ V
  let := h611.layer_elementary
  have hNL : normalizer (V : Set G) ≤ normalizer (L : Set G) :=
    A.normalizer_layer.trans ((normal_subgroupOf_iff_le_normalizer h611.L_le).mp h611.L_normal)
  have hi : I.relIndex V = 2 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) I V bot_le inf_le_right
    rw [relIndex_bot_left, relIndex_bot_left,
      (A.strict_intersection_eq_core h611 hnatural hstrict).2, hnatural.2.1.card] at hh
    omega
  have hcor : ChapterE.subgroupCorank V I = 1 := by
    rw [ChapterE.subgroupCorank, hi]
    decide
  apply (ChapterE.inducedAutomizer_eq_bot_iff hDN).mp
  apply eq_bot_iff.mpr
  intro a ha
  by_contra hn
  have hane : a ≠ 1 := by simpa only [mem_bot] using hn
  have hlo := natural_automizer_fixedCodim_ge hnatural.2.1 hNL hane
  have hmid := ChapterE.fixedCodim_mono (ChapterE.automizerRepresentation V) (zpowers_le.mpr ha)
  have hhi : fixedCodim (ChapterE.automizerRepresentation V)
      (ChapterE.inducedAutomizer V D) ≤ 1 := by
    rw [ChapterE.fixedCodim_inducedAutomizer V D hDN, ← hcor]
    exact ChapterE.Section06.subgroupCorank_antitone
      (le_inf inf_le_right (le_centralizer_iff.mp hDI))
  have hbad : 2 ≤ 1 := hlo.trans (hmid.trans hhi)
  omega

theorem LocalAnalysis.strict_center_centralizes_layer
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R) :
    (center (sourceClosure (T : Subgroup G) L R z)).map
      (sourceClosure (T : Subgroup G) L R z).subtype ≤ centralizer (layer L R : Set G) := by
  let U := sourceClosure (T : Subgroup G) L R z
  have hUn : U ≤ normalizer (layer L R : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr (A.layer_closure_commutator.trans inf_le_left)
  apply A.strict_hyperplane_centralizer h611 hnatural hstrict _ ((map_subtype_le _).trans hUn)
  rintro x ⟨u, hu, rfl⟩ y hy
  exact congrArg Subtype.val (mem_center_iff.mp hu ⟨y, hy.1⟩)

theorem LocalAnalysis.strict_layerClosure_fixes_center
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    (k : centralizer ({z} : Set G)) (hk : k ∈ equalityLayerClosure L R z)
    (c : center (sourceClosure (T : Subgroup G) L R z)) :
    strictClosureAction (T : Subgroup G) L R z k c = c := by
  let U := sourceClosure (T : Subgroup G) L R z
  let f := (MulAut.characteristic (center U)).comp (strictClosureAction (T : Subgroup G) L R z)
  have hK : equalityLayerClosure L R z ≤ f.ker := by
    apply normalClosure_le_normal
    intro v hv
    change MulAut.characteristic (center U) (strictClosureAction (T : Subgroup G) L R z v) = 1
    apply MulEquiv.ext
    intro w
    apply Subtype.ext
    apply Subtype.ext
    change (strictClosureAction (T : Subgroup G) L R z v w : G) = w.val.val
    rw [strictClosureAction_apply]
    have hh := A.strict_center_centralizes_layer h611 hnatural hstrict
      (mem_map_of_mem U.subtype w.property) (v : G) hv
    change (v : G) * w.val.val = w.val.val * (v : G) at hh
    rw [hh, mul_inv_cancel_right]
  have he := congrArg (fun a : MulAut (center U) => a c) (hK hk)
  exact congrArg Subtype.val he

theorem LocalAnalysis.strict_layerClosure_kernel_le_core
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R) :
    (strictQuotientAction (T : Subgroup G) L R z).ker ⊓ equalityLayerClosure L R z ≤
      pCore 2 (centralizer ({z} : Set G)) := by
  let H := centralizer ({z} : Set G)
  let U := sourceClosure (T : Subgroup G) L R z
  let N := (strictQuotientAction (T : Subgroup G) L R z).ker ⊓ equalityLayerClosure L R z
  let f := (strictClosureAction (T : Subgroup G) L R z).comp N.subtype
  have hpU : IsPGroup 2 U := (H.isPGroup_pCoreIn 2).to_le A.closure_le_core
  have hIm : f.range ≤ (automorphismPair (center U)).ker := by
    rintro a ⟨k, rfl⟩
    change automorphismPair (center U) (strictClosureAction (T : Subgroup G) L R z k.val) = 1
    rw [automorphismPair_apply]
    apply Prod.ext
    · apply MulEquiv.ext
      intro c
      apply Subtype.ext
      exact A.strict_layerClosure_fixes_center h611 hnatural hstrict k.val k.property.2 c
    · exact k.property.1
  have hpIm : IsPGroup 2 f.range :=
    (isPGroup_automorphism_pair_kernel (center U) (hpU.to_subgroup _)).to_le hIm
  have hk : f.ker ≤ (pCore 2 H).subgroupOf N := by
    intro k hk
    have ha : strictClosureAction (T : Subgroup G) L R z k.val = 1 := hk
    have hg : (k.val : G) ∈ H.pCoreIn 2 := (A.action_kernel _ k.val.property).mp (by
      intro u hu
      have he := congrArg (fun a : MulAut U => (a ⟨u, hu⟩ : G)) ha
      change (strictClosureAction (T : Subgroup G) L R z k.val ⟨u, hu⟩ : G) = u at he
      rw [strictClosureAction_apply] at he
      have hc : ⁅(k.val : G), u⁆ = 1 := by
        rw [commutatorElement_def, he, mul_inv_cancel]
      rw [hc]
      exact (zpowers z).one_mem)
    obtain ⟨x, hx, he⟩ := hg
    change k.val ∈ pCore 2 H
    exact (Subtype.ext he : x = k.val) ▸ hx
  have hpK : IsPGroup 2 f.ker :=
    ((pCore_isPGroup (p := 2) (G := H)).comap_subtype (K := N)).to_le hk
  have hpN : IsPGroup 2 N := by
    have hh := hpIm.comap_of_ker_isPGroup f hpK
    have ht : f.range.comap f = ⊤ := by
      ext x
      exact iff_of_true ⟨x, rfl⟩ (mem_top x)
    rw [ht] at hh
    exact hh.of_equiv Subgroup.topEquiv
  exact le_sSup ⟨inferInstance, hpN⟩

theorem LocalAnalysis.strict_core_le_action_kernel
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R) :
    pCore 2 (centralizer ({z} : Set G)) ≤ (strictQuotientAction (T : Subgroup G) L R z).ker := by
  let U := sourceClosure (T : Subgroup G) L R z
  have hline : zpowers z ≤ (center U).map U.subtype :=
    (A.strict_layer_center_intersection h611 hnatural hz horder hstrict) ▸ inf_le_left
  intro h hh
  apply (strictQuotientAction_mem_ker (T : Subgroup G) L R z h).mpr
  intro u hu
  exact hline (((A.action_kernel h h.property).mpr (mem_map_of_mem _ hh)) u hu)

theorem LocalAnalysis.strict_layerClosure_quotient_kernel
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R) :
    ((QuotientGroup.mk' (strictQuotientAction (T : Subgroup G) L R z).ker).comp
      (equalityLayerClosure L R z).subtype).ker = pCore 2 (equalityLayerClosure L R z) := by
  rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', pCore_eq_comap_of_normal]
  ext k
  constructor
  · intro hk
    exact A.strict_layerClosure_kernel_le_core h611 hnatural hstrict ⟨hk, k.property⟩
  · intro hk
    exact A.strict_core_le_action_kernel h611 hnatural hz horder hstrict hk

/-- The source identification K* ≃ K-dot, induced by the actual quotient map. -/
@[expose] def LocalAnalysis.strict_layerClosure_equiv_image
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R) :
    (equalityLayerClosure L R z) ⧸ pCore 2 (equalityLayerClosure L R z) ≃*
      (equalityLayerClosure L R z).map
        (QuotientGroup.mk' (strictQuotientAction (T : Subgroup G) L R z).ker) :=
  (QuotientGroup.quotientMulEquivOfEq
    (A.strict_layerClosure_quotient_kernel h611 hnatural hz horder hstrict).symm).trans
      ((QuotientGroup.quotientKerEquivRange
        ((QuotientGroup.mk' (strictQuotientAction (T : Subgroup G) L R z).ker).comp
          (equalityLayerClosure L R z).subtype)).trans
        (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, range_subtype])))

theorem LocalAnalysis.strict_layerClosure_equiv_image_mk
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    (k : equalityLayerClosure L R z) :
    ((A.strict_layerClosure_equiv_image h611 hnatural hz horder hstrict
      (QuotientGroup.mk' _ k)) : StrictActor (T : Subgroup G) L R z) =
      QuotientGroup.mk' _ (k : centralizer ({z} : Set G)) := rfl

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
