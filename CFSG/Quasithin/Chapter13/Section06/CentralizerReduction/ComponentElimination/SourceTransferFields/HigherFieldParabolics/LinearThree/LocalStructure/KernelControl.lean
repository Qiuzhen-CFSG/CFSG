module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.LocalStructure.Consequences
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.LocalStructure.KernelControl.IntrinsicComponent
public import Theory.GroupTheory.PCoreCentralKernelTransfer
public import CFSG.Quasithin.Chapter6.SourceDefs

/-!
# Transfer of component kernel control to the flag residuals

The full earlier-source input W_K ∈ R₂(K₋LᵥTᵥ) identifies the literal plus
quotient as two-reduced. If K/O₂(K) is quasisimple, the map from it to K⁺
has central kernel. Restricting to any H ≤ K preserves centrality modulo
O₂(H), and the finite nilpotent-preimage argument preserves it when the
plus image's two-core is also removed. Thus the resulting map is exactly
`coreComparison`, with its actual centralizer kernel and representatives.

The source applications derive intrinsic quasisimplicity using A.3.6 in
the actual two-core quotient of K Tᵥ. The higher-field SL₃ image excludes
the nonquasisimple alternatives by the proved projective two-rank comparison.
They establish the literal kernel bound for both published flag preimages
and supply every conclusion of `flag_local_structure_of_central_kernel`.
No two-group claim about C_H(W_K) is used. The kernel bound holds for every
H ≤ K, so does not require the flag marking or its normalization.

The point, line and local-structure applications retain the full known-simple
catalogue. The universal A.3.6 input is owned by qt-a03-sqtk-structure;
its discharge, together with the full earlier reduced-family premise, belongs
to qt-13-06-centralizer-reduction. The reduced-family premise is not replaced
by an assumption about the quotient's core alone. The local-structure parent
retains final flag assembly and parabolic invariance, and the higher-field
branch owner retains the exclusion in 13.6.19.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
the setup before 13.6.14 and 13.6.19, printed pp.929–931.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.LocalStructure
open ComponentSelection
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
/-- Recover the actual plus quotient's trivial two-core from the full reduced-family input. -/
theorem plus_twoCore_eq_bot_of_reduced
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hW : WK K L T z v ∈ Chapter6.Source.reducedFamily (plusActor K L T v)) :
    pCore 2 (Gplus K L T z v hL hz) = ⊥ := by
  obtain ⟨hWA, _, hN, hred⟩ := hW
  let := hN
  have hk : (plusConjugation K L T z v hL hz).ker =
      centralizer ((WK K L T z v).subgroupOf (plusActor K L T v) :
        Set (plusActor K L T v)) := by
    rw [plusConjugation_ker]
    ext x
    constructor
    · intro hx y hy
      exact Subtype.ext (hx y hy)
    · intro hx y hy
      exact congrArg Subtype.val (hx ⟨y, hWA hy⟩ hy)
  let e := QuotientGroup.quotientMulEquivOfEq hk
  change pCore 2 (plusActor K L T v ⧸ (plusConjugation K L T z v hL hz).ker) = ⊥
  apply (map_eq_bot_iff_of_injective (f := e.toMonoidHom) _ e.injective).mp
  rw [pCore_map_iso, hred]

/-- Intrinsic quasisimplicity gives central control for the component's literal
plus kernel, allowing odd central elements. The source proof of intrinsic
quasisimplicity is a separate obligation. -/
theorem componentPlusMap_ker_central_of_quasisimple_core
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (hK : K ∈ Yz L T z v)
    (hW : WK K L T z v ∈ Chapter6.Source.reducedFamily (plusActor K L T v))
    [IsQuasisimple (K ⧸ pCore 2 K)] :
    (componentPlusMap K L T z v hL hz).ker.map (QuotientGroup.mk' (pCore 2 K)) ≤
      center (K ⧸ pCore 2 K) := by
  have hR := plus_twoCore_eq_bot_of_reduced K L T z v hL hz hW
  have hcore : pCore 2 (plusImage K L T z v hL hz K) = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 (plusImage_K_subnormal K L T z v hL hz hK), hR]
    exact (MonoidHom.ker_eq_bot_iff _).mpr
      (plusImage K L T z v hL hz K).subtype_injective
  have hc : pCore 2 K ≤ (componentPlusMap K L T z v hL hz).ker := by
    have hh := subgroupPlusMap_core_le K L T K z v hL hz le_rfl
    change pCore 2 K ≤ (pCore 2 (plusImage K L T z v hL hz K)).comap
      (componentPlusMap K L T z v hL hz) at hh
    rw [hcore] at hh
    exact hh
  let : Nontrivial (plusImage K L T z v hL hz K) :=
    (nontrivial_iff_ne_bot _).mpr (plusImage_ne_bot_of_mem_Yz K L T z v hL hz hK)
  exact MonoidHom.map_ker_central_of_quasisimple_pCore
    (componentPlusMap K L T z v hL hz)
    (componentPlusMap_surjective K L T z v hL hz) hc

/-- Centrality modulo O₂(K) restricts to the intrinsic core of every subgroup
of K. In particular it applies to the actual flag residuals. -/
theorem coreComparison_ker_le_center_of_component_core
    (K L T H : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (hHK : H ≤ K)
    (hK : K ∈ Yz L T z v)
    (hW : WK K L T z v ∈ Chapter6.Source.reducedFamily (plusActor K L T v))
    [IsQuasisimple (K ⧸ pCore 2 K)] :
    (coreComparison K L T H z v hL hz hHK).ker ≤ center (H ⧸ pCore 2 H) := by
  have hk := componentPlusMap_ker_central_of_quasisimple_core K L T z v hL hz hK hW
  have hh := MonoidHom.comap_central_mod_pCore_of_injective
    (inclusion hHK) (inclusion_injective hHK)
    (componentPlusMap K L T z v hL hz).ker hk
  have he : ((componentPlusMap K L T z v hL hz).ker).comap (inclusion hHK) =
      (subgroupPlusMap K L T H z v hL hz hHK).ker := by
    rw [componentPlusMap_ker, subgroupPlusMap_ker]
    rfl
  rw [he] at hh
  exact MonoidHom.coreMap_ker_le_center_of_map_ker
    (subgroupPlusMap K L T H z v hL hz hHK)
    (subgroupPlusMap_surjective K L T H z v hL hz hHK)
    (subgroupPlusMap_core_le K L T H z v hL hz hHK) hh

/-- Consumer application: derive every existing local-structure conclusion from
the upstream intrinsic component statement and the full reduced-family input. -/
theorem flag_local_structure_of_component_core
    (F : Type*) [Field F] [Finite F] [CharP F 2] (hcard : 4 ≤ Nat.card F)
    (K L T P : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (e : plusImage K L T z v hL hz K ≃* SL(3, F))
    (hflag : P ∈ ({pointPreimage F K L T z v hL hz e,
      linePreimage F K L T z v hL hz e} : Set (Subgroup G)))
    (hPK : P ≤ K) (hK : K ∈ Yz L T z v)
    (hn : Tv T v ≤ normalizer (P : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hf : generalizedFitting (Gv v) = pCore 2 (Gv v))
    (hW : WK K L T z v ∈ Chapter6.Source.reducedFamily (plusActor K L T v))
    [IsQuasisimple (K ⧸ pCore 2 K)] :
    residualIn P ∈ Chapter1.LIn (Gv v) (Tv T v) ∧
      IsQuasisimple (residualIn P ⧸ pCore 2 (residualIn P)) ∧
      ∀ S : Sylow 2 (residualIn P ⊔ Tv T v : Subgroup G),
        (S : Subgroup (residualIn P ⊔ Tv T v : Subgroup G)).map
          (residualIn P ⊔ Tv T v).subtype = Tv T v → ChapterB.IsMinimalParabolicOver S ⊤ := by
  exact flag_local_structure_of_central_kernel F hcard K L T P z v hL hz e hflag
    hPK hK hn hSylow hf (coreComparison_ker_le_center_of_component_core
      K L T (residualIn P) z v hL hz ((map_subtype_le _).trans hPK) hK hW)

open Chapter1.Section02

/-- Source kernel control for every subgroup of the actual selected component.
Intrinsic quasisimplicity is derived from A.3.6 and the higher-field SL₃ image. -/
theorem source_coreComparison_ker_le_center {κ : GroupClass.{u}}
    (hG : IsSimpleQTKE κ G)
    (hA36 : ∀ (D : Type u) [Group D] [Finite D], IsSQTK κ D → pCore 2 D = ⊥ →
      ∀ B : Subgroup D, B.IsCComponent → A36Conclusion B)
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hF : Nat.card F = 2 ^ m) (hm : 1 < m)
    (K L T H : Subgroup G) (z v : G) (hv : orderOf v = 2)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (hHK : H ≤ K)
    (hK : K ∈ Yz L T z v)
    (hW : WK K L T z v ∈ Chapter6.Source.reducedFamily (plusActor K L T v))
    (e : plusImage K L T z v hL hz K ≃* SL(3, F)) :
    (coreComparison K L T H z v hL hz hHK).ker ≤ center (H ⧸ pCore 2 H) := by
  let := IntrinsicComponent.source_intrinsic_quasisimple
    hG hA36 K L T z v hv hK hL hz F hF hm e
  exact coreComparison_ker_le_center_of_component_core K L T H z v hL hz hHK hK hW

/-- The required bound on the literal point-preimage residual, with the full
known-simple K-group hypothesis and no intrinsic-quasisimplicity premise. -/
theorem source_pointPreimage_coreComparison_ker_le_center
    (hG : IsSimpleQTKE CFSG.KnownSimple.IsKnownSimple G)
    (hA36 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK CFSG.KnownSimple.IsKnownSimple D → pCore 2 D = ⊥ →
      ∀ B : Subgroup D, B.IsCComponent → A36Conclusion B)
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hF : Nat.card F = 2 ^ m) (hm : 1 < m)
    (K L T : Subgroup G) (z v : G) (hv : orderOf v = 2)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (hK : K ∈ Yz L T z v)
    (hW : WK K L T z v ∈ Chapter6.Source.reducedFamily (plusActor K L T v))
    (e : plusImage K L T z v hL hz K ≃* SL(3, F))
    (hRK : residualIn (pointPreimage F K L T z v hL hz e) ≤ K) :
    (coreComparison K L T (residualIn (pointPreimage F K L T z v hL hz e))
      z v hL hz hRK).ker ≤
        center (residualIn (pointPreimage F K L T z v hL hz e) ⧸
          pCore 2 (residualIn (pointPreimage F K L T z v hL hz e))) :=
  source_coreComparison_ker_le_center hG hA36 F hF hm K L T _ z v hv hL hz hRK hK hW e

/-- The same source bound on the literal line-preimage residual and its
published core-comparison map. -/
theorem source_linePreimage_coreComparison_ker_le_center
    (hG : IsSimpleQTKE CFSG.KnownSimple.IsKnownSimple G)
    (hA36 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK CFSG.KnownSimple.IsKnownSimple D → pCore 2 D = ⊥ →
      ∀ B : Subgroup D, B.IsCComponent → A36Conclusion B)
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hF : Nat.card F = 2 ^ m) (hm : 1 < m)
    (K L T : Subgroup G) (z v : G) (hv : orderOf v = 2)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (hK : K ∈ Yz L T z v)
    (hW : WK K L T z v ∈ Chapter6.Source.reducedFamily (plusActor K L T v))
    (e : plusImage K L T z v hL hz K ≃* SL(3, F))
    (hRK : residualIn (linePreimage F K L T z v hL hz e) ≤ K) :
    (coreComparison K L T (residualIn (linePreimage F K L T z v hL hz e))
      z v hL hz hRK).ker ≤
        center (residualIn (linePreimage F K L T z v hL hz e) ⧸
          pCore 2 (residualIn (linePreimage F K L T z v hL hz e))) :=
  source_coreComparison_ker_le_center hG hA36 F hF hm K L T _ z v hv hL hz hRK hK hW e

/-- Actual consumer: discharge the central-kernel premise for either flag
residual and obtain its local-family, intrinsic and minimal-parabolic conclusions.
The earlier Sylow and characteristic-two hypotheses and flag invariance retain
their literal source meanings. -/
theorem source_flag_local_structure
    (hG : IsSimpleQTKE CFSG.KnownSimple.IsKnownSimple G)
    (hA36 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK CFSG.KnownSimple.IsKnownSimple D → pCore 2 D = ⊥ →
      ∀ B : Subgroup D, B.IsCComponent → A36Conclusion B)
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hF : Nat.card F = 2 ^ m) (hm : 1 < m)
    (K L T P : Subgroup G) (z v : G) (hv : orderOf v = 2)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (e : plusImage K L T z v hL hz K ≃* SL(3, F))
    (hflag : P ∈ ({pointPreimage F K L T z v hL hz e,
      linePreimage F K L T z v hL hz e} : Set (Subgroup G)))
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (P : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hf : generalizedFitting (Gv v) = pCore 2 (Gv v))
    (hW : WK K L T z v ∈ Chapter6.Source.reducedFamily (plusActor K L T v)) :
    residualIn P ∈ Chapter1.LIn (Gv v) (Tv T v) ∧
      IsQuasisimple (residualIn P ⧸ pCore 2 (residualIn P)) ∧
      ∀ S : Sylow 2 (residualIn P ⊔ Tv T v : Subgroup G),
        (S : Subgroup (residualIn P ⊔ Tv T v : Subgroup G)).map
          (residualIn P ⊔ Tv T v).subtype = Tv T v → ChapterB.IsMinimalParabolicOver S ⊤ := by
  have hcard : 4 ≤ Nat.card F := by
    rw [hF]
    exact (show 4 = (2 : ℕ) ^ 2 by decide).le.trans
      (pow_le_pow_right' (by decide : (1 : ℕ) ≤ 2) hm)
  have hPK : P ≤ K := by
    rcases hflag with h | h
    · subst P
      exact preimageIn_le _ _ _
    · have he : P = linePreimage F K L T z v hL hz e := Set.mem_singleton_iff.mp h
      subst P
      exact preimageIn_le _ _ _
  exact flag_local_structure_of_central_kernel F hcard K L T P z v hL hz e hflag
    hPK hK hn hSylow hf (source_coreComparison_ker_le_center hG hA36 F hF hm
      K L T (residualIn P) z v hv hL hz ((map_subtype_le _).trans hPK) hK hW e)
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.LocalStructure
