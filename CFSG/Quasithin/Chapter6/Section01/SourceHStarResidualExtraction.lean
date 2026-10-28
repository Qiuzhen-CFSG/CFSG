module
public import CFSG.Quasithin.Chapter6.Section01.SourceHStarTwoPerfectOmega
public import CFSG.Quasithin.Chapter6.Section01.SourceHStarCentralizerCore
public import Theory.GroupTheory.SymmetricThreeResidualKernel

/-!
# Canonical residual extraction in the bad H-star centralizer case

Let `U_H = ⟨Ω₁(Z(T))ᴴ⟩` and `C = C_H(U_H)`.  If `C` is larger than
`O₂(H)`, then `Y = O²(C)` is nontrivial: otherwise `C` would be a normal
two-subgroup of `H` and hence lie in `O₂(H)`.  The residual is characteristic
in `C`, so it is normalized by `H` and by the original Sylow subgroup.  Its
ambient image centralizes the literal orbit `U_H`, lies in the source Frattini
subgroup of the residual, and is contained in `M`.

This is a canonical candidate for the source witness before the remaining
Thompson-commutator calculation. The source's selected witness is not identified
with this residual. Normality and nontriviality do not imply `Y = [Y,J(T)]`
in isolation.

Source: Aschbacher--Smith 6.1.5, printed p.666, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher

namespace CFSG.Quasithin.Chapter6.Source.Hypothesis611

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V H : Subgroup G} {n : ℕ}
  (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
include h

/-- The residual of the literal H-star orbit centralizer supplies the
nontrivial two-perfect canonical witness in the bad-centralizer branch. -/
theorem hstar_omega_orbit_residual_extraction
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥)
    (hne : centralizer
      (((conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H) :
        Set H) ≠ pCore 2 H) :
    let U₀ := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H
    let U := U₀.subgroupOf H
    let C := centralizer (U : Set H)
    let Y := (pResidual 2 C).map C.subtype
    let YG := Y.map H.subtype
    YG ≠ ⊥ ∧
      IsPPerfect 2 YG ∧
      (T : Subgroup G) ≤ normalizer (YG : Set G) ∧
      (pResidual 2 H).map H.subtype ≤ normalizer (YG : Set G) ∧
      YG ≤ H ⊓ centralizer (U₀ : Set G) ∧
      YG ≤ (ChapterB.BaumannArgument.coreFrattini (pResidual 2 H)).map H.subtype ∧
      YG ≤ M := by
  let U₀ := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H
  let U := U₀.subgroupOf H
  let hinput := h.rankOneInput hout
  have hH' : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) :=
    h.maximal_eq_normalizer_L ▸ hH
  have hU := hinput.hstar_omega_orbit_reduced hH'
  let _ : U.Normal := hU.normal
  let C := centralizer (U : Set H)
  have hHC : (⊤ : Subgroup H) ≤ normalizer (C : Set H) := by
    exact (le_normalizer_of_normal : (⊤ : Subgroup H) ≤ normalizer (U : Set H)).trans
      (normalizer_le_normalizer_centralizer U)
  let _ : C.Normal := normalizer_eq_top_iff.mp (top_unique hHC)
  let Y := (pResidual 2 C).map C.subtype
  let YG := Y.map H.subtype
  have hcoreC : pCore 2 H ≤ C := le_centralizer_iff.mp hU.le_centralizer_pCore
  have hYne : Y ≠ ⊥ := by
    intro hY
    have hres : pResidual 2 C = ⊥ :=
      (map_eq_bot_iff_of_injective _ C.subtype_injective).mp hY
    have hCtwo : IsPGroup 2 C :=
      isPGroup_of_residual_isPGroup 2 (hres ▸ IsPGroup.of_bot)
    have hle : C ≤ pCore 2 H := le_sSup ⟨inferInstance, hCtwo⟩
    exact hne (le_antisymm hle hcoreC)
  have hYperfect : IsPPerfect 2 YG :=
    (isPPerfect_embedded_pResidual 2 C).of_surjective
      (H.subtype.subgroupMap Y) (H.subtype.subgroupMap_surjective Y)
  have hU₀H : U₀ ≤ H := conjugateSpanBy_le_self
    (fun _ hz => hH.1.1.2 ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1)
  have hCmap : C.map H.subtype = H ⊓ centralizer (U₀ : Set G) := by
    rw [map_centralizer_subtype, map_subgroupOf_eq_of_le hU₀H]
  have hYcentral : YG ≤ H ⊓ centralizer (U₀ : Set G) :=
    (map_mono (map_subtype_le (pResidual 2 C))).trans_eq hCmap
  have hYGnorm : H ≤ normalizer (YG : Set G) := by
    have hn := Y.le_normalizer_map H.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hn
  have hT : (T : Subgroup G) ≤ H := hH.1.1.2
  have hResidual : (pResidual 2 H).map H.subtype ≤ normalizer (YG : Set G) :=
    (map_subtype_le (pResidual 2 H)).trans hYGnorm
  have hYfrattini : Y ≤ ChapterB.BaumannArgument.coreFrattini (pResidual 2 H) := by
    apply (le_inf (map_pResidual_le 2 C.subtype) (map_subtype_le (pResidual 2 C))).trans
    exact h.hstar_omega_orbit_residual_centralizer_le_coreFrattini hout hH hZH
  have hYM : YG ≤ M := by
    apply (hYcentral.trans (inf_le_inf_left H
      (centralizer_le (le_conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H)))).trans
    exact hstar_omega_centralizer_le_M hH hZH
  exact ⟨fun he => hYne ((map_eq_bot_iff_of_injective _ H.subtype_injective).mp he), hYperfect,
    hT.trans hYGnorm, hResidual, hYcentral, map_mono hYfrattini, hYM⟩

end CFSG.Quasithin.Chapter6.Source.Hypothesis611
