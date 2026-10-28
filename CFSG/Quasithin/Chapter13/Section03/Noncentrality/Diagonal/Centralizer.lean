module

public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Diagonal.Quotient
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Centralizer


/-!
# The residual quotient centralizer of a block

For a short K, an automorphism trivial on K/O₂(K) is trivial on K/U(K).
If C=C_KA(K/O₂(K)) also fixes U(K), its two-residual D fixes both layers
and therefore centralizes K. This supplies the coprime-action step in
13.3.14 with a legitimate two-perfect actor.

The literal full C cannot centralize K, since it contains O₂(K) and
U(K)=[O₂(K),K] is nontrivial. The first theorem checks this distinction
formally; it does not give a counterexample to the full source lemma.
The short-group identification and module fixation remain explicit inputs.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.10,
printed p.124, and the last paragraph of 13.3.14, printed p.893.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality.Diagonal
variable {G : Type*} [Group G]

/-- The literal quotient centralizer cannot centralize a short K:
 it contains the noncentral intrinsic two-core of K. -/
theorem quotientCentralizer_not_le_centralizer (K A : Subgroup G)
    (hn : A ≤ normalizer K) (hK : ChapterC.IsShort K) :
    ¬ quotientCentralizer K A hn ≤ centralizer (K : Set G) := by
  intro hc
  have hh : ⁅K.pCoreIn 2, K⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr
      ((core_le_quotientCentralizer K A hn).trans hc)
  have hu : (ChapterC.blockU K).map K.subtype = ⊥ := by
    rw [ChapterC.blockU, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
    exact hh
  exact hK.blockU_ne_bot (map_injective K.subtype_injective (by simpa using hu))

variable [Finite G]

/-- The correct coprime actor is O²(C), with C the actual quotient
 centralizer. Fixation of U(K) and the quotient action imply that this
 residual centralizes K; normality is only required inside KA. -/
theorem centralizerResidual_le_centralizer (K A : Subgroup G)
    (hn : A ≤ normalizer K) (hK : ChapterC.IsShort K)
    (hU : quotientCentralizer K A hn ≤
      centralizer ((ChapterC.blockU K).map K.subtype : Set G)) :
    centralizerResidual K A hn ≤ centralizer (K : Set G) := by
  have hcomm : ⁅quotientCentralizer K A hn, K⁆ ≤
      (ChapterC.blockU K).map K.subtype := by
    apply commutator_le.mpr
    rintro c ⟨c', hc, rfl⟩ k hk
    let a := K.normalizerMonoidHom (inclusion (sup_le K.le_normalizer hn) c')
    have hcore : ∀ z : K, a z * z⁻¹ ∈ pCore 2 K := by
      intro z
      have he : pCoreJoinAction 2 hn c' = 1 := hc
      have hx := DFunLike.congr_fun he (QuotientGroup.mk' (pCore 2 K) z)
      rw [pCoreJoinAction_mk] at hx
      simpa only [div_eq_mul_inv] using QuotientGroup.eq_iff_div_mem.mp hx
    have he := DFunLike.congr_fun (hK.quotient_blockU_aut_eq_one a hcore)
      (QuotientGroup.mk' (ChapterC.blockU K) ⟨k, hk⟩)
    rw [quotientAut_apply_mk] at he
    have hm : a ⟨k, hk⟩ * (⟨k, hk⟩ : K)⁻¹ ∈ ChapterC.blockU K := by
      simpa only [div_eq_mul_inv] using QuotientGroup.eq_iff_div_mem.mp he
    exact mem_map.mpr ⟨_, hm, rfl⟩
  exact residual_centralizes_of_two_layer _ K _
    ((pCore_isPGroup.to_le ChapterC.blockU_le_core).map K.subtype) hU hcomm

end CFSG.Quasithin.Chapter13.Section03.Noncentrality.Diagonal
