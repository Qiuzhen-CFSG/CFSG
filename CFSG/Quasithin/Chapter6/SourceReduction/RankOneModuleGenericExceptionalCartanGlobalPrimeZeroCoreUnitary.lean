module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSylowSize
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFour.Sylow
public import Theory.GroupTheory.Amalgam.Reversal

/-!
# Excluding the marked binary-unitary zero-core pair

The genuine U₄(2) carrier has a Sylow two-subgroup of order 64. A marking
of the whole original Borel SB₂ embeds the original S into that carrier.
The source prime-pair size theorem gives |S| > 2^(3n) ≥ 64, a contradiction.
This excludes both orientations, even for parabolic equivalence without
compatible overlap maps. It uses neither S = T nor a comparison of the
original degree with a residual degree.

This is a shorter exclusion of the source unitary branch using the
already available original moved reduced module. Together with the J₂,
Aut(J₂) and binary-triality exclusions, it removes all four marked rows.
Recognition of those rows, higher-field reduction and changed-Sylow
assembly remain with qt-d-1222-rankone-cartan-local-to-global.
Source: Aschbacher–Smith 5.2.2, printed p.647, and F.1.12(I)(6),
pp.263–264 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
namespace Prime
open ChapterF.GreenBook.LieModels.UnitaryFour

/-- The actual whole overlap cannot be the Borel of U₄(2): its two-part is too small. -/
theorem LocalData.zeroCore_binaryUnitary_borel_contradiction
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (e : (Global.sourceS L H ⊔ (B ⊓ R) : Subgroup G) ≃* overlap 1 (by decide)) :
    False := by
  let f : Global.sourceS L H →* ProjectiveGroup 1 (by decide) :=
    (overlap 1 (by decide)).subtype.comp
      (e.toMonoidHom.comp (inclusion le_sup_left))
  apply d.sourceS_no_small_sylow_embedding h hH c hd (projectiveSylow 1 (by decide)) _ f
    ((overlap 1 (by decide)).subtype_injective.comp
      (e.injective.comp (inclusion_injective le_sup_left)))
  rw [projectiveSylow_card]
  change 2^6 ≤ 2^(3*n)
  exact Nat.pow_le_pow_right (by decide) (by have := h.exponent; omega)

/-- Both orientations of the genuine binary unitary parabolic model are excluded. -/
theorem LocalData.zeroCore_not_binaryUnitary_parabolic
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D) :
    ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
      (amalgam 1 (by decide))) ∧
    ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
      (amalgam 1 (by decide)).reverse) := by
  constructor <;> rintro ⟨e⟩ <;> exact d.zeroCore_binaryUnitary_borel_contradiction h hH c hd e.middle

end Prime
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
