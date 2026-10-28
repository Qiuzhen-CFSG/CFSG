module

public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.BorelAction
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Lifting.Transport
public import Theory.SpecificGroups.Suzuki.BorelResidualRigidity

/-!
# The original A₅ module acts trivially on the Suzuki quotient

The Suzuki Borel residual centralizes V. Transport it through the actual
Sylow-normalizer inclusion, then apply pointwise Borel rigidity to each
conjugation automorphism induced by V. Its action on A/O₂(A) is trivial,
so [V,A] lies in the embedded two-core of A.

The final application constructs the genuine F.1.1 pair from the original
normal component of C_G(z). This strengthens the Borel action calculation
without asserting the still separate mixed-pair exclusion.

Source: Aschbacher–Smith, 5.2.2–6 and 13.6.27, printed pp.646–651,934.
-/

public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
open ChapterF.Source
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
include d

/-- In the genuine source pair, V centralizes the literal Suzuki quotient. -/
theorem suzuki_pair_module_commutator_le_twoCore
    (A : Subgroup G) (hF : HypothesisF11 ![L,A] (T : Subgroup G))
    {z : G} (hz : zpowers z = V₁) (hAC : A ≤ centralizer ({z} : Set G))
    {m : ℕ} (hm : 1 ≤ m)
    (e : (A ⧸ pCore 2 A) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    ⁅V,A⁆ ≤ A.pCoreIn 2 := by
  obtain ⟨P,hP⟩ : ∃ P : Sylow 2 A,
      (P : Subgroup A).map A.subtype = (T : Subgroup G) ⊓ A := by
    exact hF.sylow 1
  have hVN : V ≤ normalizer (A : Set G) := d.chosen.le_sylow.trans
    (show (T : Subgroup G) ≤ normalizer (A : Set G) by simpa using hF.S_normalizes 1)
  have hNA : (normalizer (P : Set A)).map A.subtype = borel A (T : Subgroup G) := by
    change (sylowNormalizer P).map A.subtype = _
    rw [← borel_subgroupOf_eq_sylowNormalizer A (T : Subgroup G) P hP]
    exact map_subgroupOf_eq_of_le (borel_le _ _)
  have hres : ((pResidual 2 (normalizer (P : Set A))).map
      (normalizer (P : Set A)).subtype).map A.subtype =
      (pResidual 2 (borel A (T : Subgroup G))).map
        (borel A (T : Subgroup G)).subtype := by
    rw [map_embedded_pResidual,hNA]
  have hB := suzuki_borel_residual_centralizes d A hF hz hAC hm e
  apply commutator_le.mpr
  intro v hv a ha
  let α := A.normalizerMonoidHom ⟨v,hVN hv⟩
  have hfix : ∀ x ∈ (pResidual 2 (normalizer (P : Set A))).map
      (normalizer (P : Set A)).subtype, α x = x := by
    intro x hx
    have hxa : (x : G) ∈ (pResidual 2 (borel A (T : Subgroup G))).map
        (borel A (T : Subgroup G)).subtype := hres ▸ mem_map_of_mem A.subtype hx
    apply Subtype.ext
    change v * (x : G) * v⁻¹ = (x : G)
    exact mul_inv_eq_iff_eq_mul.mpr ((mem_centralizer_iff.mp (hB hxa)) v hv)
  have hq := BenderSuzuki.MatrixGroups.suzuki_quotientAut_eq_one_of_fixing_borelResidual
    (show 0 < m by omega) e P α hfix
  let x : A := ⟨a,ha⟩
  have he : QuotientGroup.mk' (pCore 2 A) (α x) = QuotientGroup.mk' (pCore 2 A) x := by
    have hh := DFunLike.congr_fun hq (QuotientGroup.mk' (pCore 2 A) x)
    rw [quotientAut_apply_mk] at hh
    exact hh
  have hc : α x * x⁻¹ ∈ pCore 2 A := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (pCore 2 A) (α x * x⁻¹) = 1
    rw [map_mul,map_inv,he,mul_inv_cancel]
  exact mem_map.mpr ⟨α x * x⁻¹,hc,rfl⟩

/-- The extra normal component of the original centralizer has its entire
V-commutator in its own two-core; the source-pair premise is discharged. -/
theorem component_module_commutator_le_twoCore
    {z : G} (hz : zpowers z = V₁)
    (D : Subgroup (centralizer ({z} : Set G))) [D.Normal]
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D ⧸ pCore 2 D) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (hout : ¬ D.map (centralizer ({z} : Set G)).subtype ≤ normalizer (L : Set G))
    (h25 : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J →
      J ≤ normalizer (L : Set G)) :
    let A := D.map (centralizer ({z} : Set G)).subtype
    ⁅V,A⁆ ≤ A.pCoreIn 2 := by
  let eD := D.equivMapOfInjective (centralizer ({z} : Set G)).subtype
    (centralizer ({z} : Set G)).subtype_injective
  let eQ := QuotientGroup.congr _ _ eD (pCore_map_iso 2 eD)
  exact suzuki_pair_module_commutator_le_twoCore d _
    (source_A5_suzuki_pair_F11 d hz D e hout h25) hz (map_subtype_le D) hm (eQ.symm.trans e)

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
