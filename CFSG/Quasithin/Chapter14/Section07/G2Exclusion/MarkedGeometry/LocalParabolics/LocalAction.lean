module

public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.FamilyAction
public import Theory.GroupAction.ModelConjugation
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.GroupTheory.PResidual.Defs

/-!
# The local vertex and its literal quotient actions

The source residual is O²(C_H(V₂)). The centralizer factorization and
surjectivity of L₂T on Aut(V₂) identify N_G(V₂) with L₂YT. Conjugation
on L₂/O₂(L₂) is constructed from the intrinsic core quotient, and the
earlier commutator bound forces that action to be trivial. All action
kernels are retained as relative centralizers; no ambient normality of
L₂ or its two-core is imposed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 14.7.4(2)
and 14.7.56(2), printed pp.1043 and 1066. The full action image on the
four-dimensional pencil span remains a separate linear calculation.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics
open Subgroup
open scoped commutatorElement
variable {G : Type*} [Group G]

/-- The source Y is the two-residual of the relative centralizer. -/
def localResidual (H V₂ : Subgroup G) : Subgroup G :=
  (pResidual 2 (H ⊓ centralizer (V₂ : Set G) : Subgroup G)).map
    (H ⊓ centralizer (V₂ : Set G)).subtype

theorem localResidual_le_centralizer (H V₂ : Subgroup G) :
    localResidual H V₂ ≤ centralizer (V₂ : Set G) :=
  (map_subtype_le _).trans inf_le_right

/-- Literal conjugation on W by a subgroup of its normalizer. -/
def ambientAction (X W : Subgroup G) (hXW : X ≤ normalizer W) : X →* MulAut W :=
  W.normalizerMonoidHom.comp (inclusion hXW)

/-- Retain the relative action kernel, even when C_G(W) is not contained in X. -/
theorem ambientAction_kernel (X W : Subgroup G) (hXW : X ≤ normalizer W) :
    (ambientAction X W hXW).ker = (centralizer (W : Set G)).subgroupOf X := by
  ext x
  change inclusion hXW x ∈ W.normalizerMonoidHom.ker ↔ _
  rw [normalizerMonoidHom_ker]
  rfl

theorem ambientAction_kernel_map (X W : Subgroup G) (hXW : X ≤ normalizer W) :
    (ambientAction X W hXW).ker.map X.subtype = X ⊓ centralizer (W : Set G) := by
  rw [ambientAction_kernel, subgroupOf_map_subtype, inf_comm]

/-- The centralizer factorization and the full action of L₂T on V₂ give
the local vertex group N_G(V₂)=L₂YT. -/
theorem vertex_eq_join (V₂ L₂ Y T : Subgroup G)
    (hLT : L₂ ⊔ T ≤ normalizer V₂)
    (hYC : Y ≤ centralizer (V₂ : Set G))
    (hC : centralizer (V₂ : Set G) = Y ⊔ (T ⊓ centralizer (V₂ : Set G)))
    (hfull : Function.Surjective (ambientAction (L₂ ⊔ T) V₂ hLT)) :
    normalizer V₂ = L₂ ⊔ Y ⊔ T := by
  let J := L₂ ⊔ Y ⊔ T
  have hLJ : L₂ ⊔ T ≤ J := sup_le (le_sup_left.trans le_sup_left) le_sup_right
  have hCJ : centralizer (V₂ : Set G) ≤ J := by
    rw [hC]
    exact sup_le (le_sup_right.trans le_sup_left) (inf_le_left.trans le_sup_right)
  apply le_antisymm
  · intro g hg
    obtain ⟨l,hl⟩ := hfull (V₂.normalizerMonoidHom ⟨g,hg⟩)
    let n : normalizer V₂ := ⟨g,hg⟩ * (inclusion hLT l)⁻¹
    have hn : n ∈ V₂.normalizerMonoidHom.ker := by
      change V₂.normalizerMonoidHom n = 1
      dsimp only [n]
      rw [map_mul, map_inv]
      change V₂.normalizerMonoidHom ⟨g,hg⟩ *
        (ambientAction (L₂ ⊔ T) V₂ hLT l)⁻¹ = 1
      rw [hl, mul_inv_cancel]
    rw [normalizerMonoidHom_ker] at hn
    have hm := J.mul_mem (hCJ hn) (hLJ l.property)
    change (g * (l : G)⁻¹) * l ∈ J at hm
    simpa only [inv_mul_cancel_right] using hm
  · exact sup_le (sup_le (le_sup_left.trans hLT)
      (hYC.trans (centralizer_le_normalizer _))) (le_sup_right.trans hLT)

/-- The actual quotient conjugation action on L₂/O₂(L₂). -/
def coreQuotientAction (L₂ Y : Subgroup G) (hYL : Y ≤ normalizer L₂) :
    Y →* MulAut (L₂ ⧸ pCore 2 L₂) :=
  (quotientAut (pCore 2 L₂)).comp (ambientAction Y L₂ hYL)

/-- The earlier local commutator bound forces trivial action on the literal
core quotient, without assuming L₂ or O₂(L₂) normal in the ambient group. -/
theorem coreQuotientAction_trivial (L₂ Y : Subgroup G) (hYL : Y ≤ normalizer L₂)
    (hcomm : ⁅Y,L₂⁆ ≤ L₂.pCoreIn 2) : coreQuotientAction L₂ Y hYL = 1 := by
  ext y q
  obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L₂) q
  change quotientAut (pCore 2 L₂) (ambientAction Y L₂ hYL y)
      (QuotientGroup.mk' (pCore 2 L₂) l) = QuotientGroup.mk' (pCore 2 L₂) l
  rw [quotientAut_apply_mk]
  apply QuotientGroup.eq_iff_div_mem.mpr
  change ambientAction Y L₂ hYL y l / l ∈ pCore 2 L₂
  have hc : (y : G) * (l : G) * (y : G)⁻¹ * (l : G)⁻¹ ∈ L₂.pCoreIn 2 :=
    hcomm (commutator_mem_commutator y.property l.property)
  obtain ⟨c,hc,he⟩ := hc
  have he' : c = ambientAction Y L₂ hYL y l / l := by
    apply Subtype.ext
    simpa [ambientAction, div_eq_mul_inv] using he
  rwa [← he']

/-- Source application of 14.7.4(2): C_{L₂}(V₂)=O₂(L₂), together with
[L₂,Y]≤C_{L₂}(V₂), discharges the quotient-action assertion of 14.7.56(2). -/
theorem source_centralizes_core_quotient (L₂ Y V₂ : Subgroup G)
    (hcomm : ⁅L₂,Y⁆ ≤ L₂ ⊓ centralizer (V₂ : Set G))
    (hcore : L₂ ⊓ centralizer (V₂ : Set G) = L₂.pCoreIn 2) :
    ∃ hYL : Y ≤ normalizer L₂, coreQuotientAction L₂ Y hYL = 1 := by
  have hn : Y ≤ normalizer L₂ :=
    le_normalizer_iff_commutator_le_left.mpr (hcomm.trans inf_le_left)
  refine ⟨hn,coreQuotientAction_trivial L₂ Y hn ?_⟩
  rw [commutator_comm]
  exact hcomm.trans_eq hcore

/-- L₂ normalizes the span because it normalizes every line in the family. -/
theorem local_fixer_normalizes_span (V V₂ L₂ Y : Subgroup G)
    (hV₂ : V₂ ≤ V) (hcomm : ⁅V,L₂⁆ = V₂)
    (hYL : Y ≤ normalizer L₂) (hYC : Y ≤ centralizer (V₂ : Set G)) :
    L₂ ≤ normalizer (generatedLineFamily V Y) := by
  apply (le_iInf fun y : Y => ?_).trans (iInf_normalizer_le_normalizer_iSup _)
  exact (source_family_action V V₂ L₂ Y hV₂ hcomm hYL hYC).1 _ ⟨y,rfl⟩

end CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics
