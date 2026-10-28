module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.Centralizers
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Normalizer
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.SymmetricLocal.ExchangedModel
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.SymmetricLocal.QuotientModel.LocalSylow

/-!
# The core identities, exchanged lift and original local Sylow

The selected component square gives both quotient-core bounds. Lifting them
identifies D with the joint centralizer's two-core and UD with O₂(K₀UD).
The actual original A₅ action and conjugate case-(3) coordinates then rule
out a factor-preserving action by z and identify the exchanged lift with D.
Finally the selected quotient involution's centralizer calculation pulls
back to exactly T ∩ N_G(D). The existing normalizer theorems apply to these
proved outputs, preserving both T and i = x⁻¹zx.

The earlier case-(3), core, selection, marked-action and centralizer-modulo-
⟨z⟩ inputs remain explicit. Their producers are the earlier 12.8/14.3,
14.4.7 and orthogonal Selection developments. In particular the comparison
uses the centralizer modulo the central line, not ordinary C_H(i).
This completes the symmetric/local implication used by Lift; the full
exclusion, transvection identification and Appendix A.3.14 application
remain with the parent source assembly.

Source: Aschbacher–Smith, Lemma 14.4.9, printed p.1010, with case (3) of
14.4.2, printed pp.1006–1007.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal

variable {G : Type*} [Group G] [Finite G]
variable (U : Subgroup G) [IsExtraspecial 2 U] (T : Sylow 2 G) (z x : G)
  (hz : orderOf z = 2)
  (hZ : (center U).map U.subtype = zpowers z)
  (hUcore : (centralizer ({z} : Set G)).pCoreIn 2 = U)
  (hUcard : Nat.card U = 512)
  (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
  (hiT : conjugateElement z x ∈ T)
  (hout : conjugateElement z x ∉ U)
  (hmoved : Nat.card (((⁅U,zpowers (conjugateElement z x)⁆).subgroupOf U).map
    (QuotientGroup.mk' (center U))) = 16)
  (hirr : ∀ E : Subgroup G, zpowers z ≤ E → E ≤ liftBase U z (conjugateElement z x) →
    diagonalResidual (centralizer ({z} : Set G)) (conjugateElement z x) ≤
      normalizer (E : Set G) → E = zpowers z ∨ E = liftBase U z (conjugateElement z x))
  (original : ExchangedModel.OriginalMovedAction U z (conjugateElement z x))
  (exchanged : ExchangedModel.CaseThreeAction
    (centralizer ({conjugateElement z x} : Set G)) (conjugateCore U x))
  (components : QuotientModel.SelectedComponentData
    ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G)))
    (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))
      ⟨conjugateElement z x,hTz hiT⟩)
    (((diagonalResidual (centralizer ({z} : Set G)) (conjugateElement z x)).subgroupOf
      (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))))))
  (hcompare : ((commutatorPreimage (centralizer ({z} : Set G))
      (zpowers (conjugateElement z x)) (zpowers z)).subgroupOf
      (centralizer ({z} : Set G))).map
    (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) =
    centralizer ({QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))
      ⟨conjugateElement z x,hTz hiT⟩} :
      Set ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G)))))

include hz hZ hUcore hUcard hTz hiT hout hmoved hirr original exchanged components hcompare

/-- The two intrinsic core identities, the symmetric source calculation,
and the exact local Sylow witness, all deduced from the earlier selected
configuration. No core identity, exchanged conclusion or Sylow witness is
an assumption. The core images use the literal subgroup subtype maps. -/
theorem lift_symmetric_local_of_selected :
    let i := conjugateElement z x
    let H := centralizer ({z} : Set G)
    let K₀ := diagonalResidual H i
    let D := centralizerLift U z i
    IsElementaryAbelian 2 D ∧ Nat.card D = 64 ∧
    D = (centralizer ((zpowers z ⊔ zpowers i : Subgroup G) : Set G)).pCoreIn 2 ∧
    U ⊔ D = (K₀ ⊔ U ⊔ D).pCoreIn 2 ∧
    diagonalResidual (conjugateCore H x) z = K₀ ∧
    ClassicalOrthogonal.FourPlusMatrix.Binary.InvolutionResidual.SwapsFactors
      (exchanged.action ⟨z, mem_centralizer_singleton_iff.mpr
        (mem_centralizer_singleton_iff.mp (hTz hiT)).symm⟩) ∧
    centralizerLift (conjugateCore U x) i z = D ∧
    K₀ ⊔ U ≤ normalizer (D : Set G) ∧
    conjugateCore U x ≤ normalizer (D : Set G) ∧
    D ⊓ centralizer (U : Set G) = zpowers z ∧
    D ⊓ centralizer (conjugateCore U x : Set G) = zpowers i ∧
    (U ⊔ D) ⊓ centralizer (D : Set G) = D ∧
    ∃ P : Sylow 2 (H ⊓ normalizer (D : Set G) : Subgroup G),
      (P : Subgroup (H ⊓ normalizer (D : Set G) : Subgroup G)) =
        (localSylow (T : Subgroup G) D).subgroupOf (H ⊓ normalizer (D : Set G)) := by
  let i := conjugateElement z x
  let H := centralizer ({z} : Set G)
  let K₀ := diagonalResidual H i
  have hiz : i ∈ H := hTz hiT
  have hi : orderOf i = 2 := by
    simpa only [i, conjugateElement, MulEquiv.orderOf_eq] using hz
  have hHU : H ≤ normalizer (U : Set G) := by
    rw [← hUcore]
    exact H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hKC : K₀ ≤ H ⊓ centralizer ({i} : Set G) := map_subtype_le _
  have hKU := (hKC.trans inf_le_left).trans hHU
  have hKi := hKC.trans inf_le_right
  obtain ⟨hD,hDcard,hA,hAcard⟩ := centralizerLift_elementary_and_card U K₀ z i
    hz hi hZ (hHU hiz) hiz hout hKU hKi hmoved hirr
  obtain ⟨hCcore,hJcore⟩ := QuotientModel.core_identities_of_selected U z i
    hZ hUcore hiz hUcard hD hA hAcard hmoved components
  obtain ⟨hswap,_,_,heq,hUxD,hCUx⟩ :=
    ExchangedModel.exchanged_components_and_symmetric_lift U z x hz hZ hUcore hUcard
      hiz hDcard hCcore exchanged original
  have hcore : centralizerLift U z i =
      (centralizer ((zpowers z ⊔ zpowers i : Subgroup G) : Set G)).pCoreIn 2 := by
    rw [joint_centralizer_eq]
    exact hCcore.symm
  exact ⟨hD, hDcard, hcore, hJcore.symm, diagonalResidual_symmetric z x,
    hswap, heq, lift_normalized_by_residual_join_core U K₀ z i hZ (hHU hiz) hKU hKi hmoved,
    hUxD, centralizerLift_fixed_line U z i hz hi hZ (hHU hiz) hD hAcard, hCUx,
    centralizerLift_self_centralizer U z i hZ (hHU hiz) hUcard hD hA hAcard,
    QuotientModel.lift_local_sylow_of_selected U T z i hZ hUcore hi hTz hiT hiz
      hD hmoved hout hcompare components⟩

/-- Application to the existing normalizer deductions. This discharges all
three symmetry/local premises of `lift_normalizer_consequences_of_moved_section`
without importing its parent module. The original T_D is Sylow in N_G(D). -/
theorem lift_normalizer_consequences_of_selected :
    let D := centralizerLift U z (conjugateElement z x)
    let N := normalizer (D : Set G)
    IsElementaryAbelian 2 D ∧ Nat.card D = 64 ∧
      D ≤ N.pCoreIn 2 ∧ N.pCoreIn 2 ≤ centralizer (D : Set G) ∧
      (U ⊔ D) ⊓ N.pCoreIn 2 = D ∧
      ∃ P : Sylow 2 N, (P : Subgroup N) = (localSylow (T : Subgroup G) D).subgroupOf N := by
  obtain ⟨hD,hDcard,_,_,_,_,_,hnorm,hUxD,hCU,hCUx,hself,hlocal⟩ :=
    lift_symmetric_local_of_selected U T z x hz hZ hUcore hUcard hTz hiT hout hmoved hirr
      original exchanged components hcompare
  have hUT : U ≤ (T : Subgroup G) := by
    rw [← hUcore]
    rintro u ⟨a,ha,rfl⟩
    exact pCore_isPGroup.le_sylow_of_normal (T.subtype hTz) ha
  have hY : symmetricActor U z x ≤
      normalizer (centralizerLift U z (conjugateElement z x) : Set G) := sup_le hnorm hUxD
  obtain ⟨hDN,hND,hinter⟩ := lift_normalizer_core U z x hz
    (IsExtraspecial.isPGroup 2 U) hD hY hCU hCUx hself
  exact ⟨hD,hDcard,hDN,hND,hinter,lift_normalizer_sylow U T z (conjugateElement z x)
    hz hUT (le_sup_right.trans hnorm) hTz hCU hlocal⟩

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal
