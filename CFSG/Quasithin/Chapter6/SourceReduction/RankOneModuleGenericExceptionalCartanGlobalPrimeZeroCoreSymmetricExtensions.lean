module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeZeroCoreLieModels
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.SolvableEndpoints

/-!
# Symmetric Lie extension rows on the original Cartan pair

The actual selected pair has a solvable left endpoint and a nonsolvable right
endpoint. In a restored SourceExtension the whole overlap supplements the
inner part of each endpoint. The solvability transport therefore excludes
every extension whose two native parabolics have matching solvability.

The existing local SL₂/Suzuki quotients and binary parabolic calculations
supply this criterion for Sp₄, G₂ and all Ree parameters, including Model 0.
The argument needs neither an outer-index bound nor a collapse to a pure-model
isomorphism. Both orientations and the full extension overlap are retained;
regular isomorphisms may be forgotten to parabolic equivalences, but no weaker
source comparison is upgraded. The original S and selected R are unchanged.
Source: Aschbacher–Smith F.1.12, pp.263–264, and 5.2.2, pp.647–648.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
open ChapterF.SourceCompletion.UnitaryNonbinary
variable {G : Type*} [Group G] [Finite G]

variable {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
  (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
  (hz : (generated L H D R).pCoreIn 2 = ⊥)

include d h hH c hd hz in
/-- A full original extension with matching base solvability cannot mark the
selected source pair. The solvability of the whole overlap is proved internally. -/
theorem LocalData.zeroCore_not_sameSolvability_extension
    {X : Type*} [Group X] {P₀ P₁ : Subgroup X}
    (E : SourceExtension P₀ P₁)
    (hs : Group.IsSolvable P₀ ↔ Group.IsSolvable P₁) :
    ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R) E.amalgam) ∧
      ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv
        (zeroCoreAmalgam L H B D R) E.amalgam.reverse) := by
  obtain ⟨hl,hr⟩ := d.zeroCore_mixed_solvability h hH c hd hz
  let := hl
  have he := E.endpoints_solvable_iff hs
  constructor
  · rintro ⟨f⟩
    have hleft := Group.isSolvable_of_surjective (f := f.left.toMonoidHom) f.left.surjective
    let := he.mp hleft
    exact hr (Group.isSolvable_of_isSolvable_injective (f := f.right.toMonoidHom) f.right.injective)
  · rintro ⟨f⟩
    have hright := Group.isSolvable_of_surjective (f := f.left.toMonoidHom) f.left.surjective
    let := he.mpr hright
    exact hr (Group.isSolvable_of_isSolvable_injective (f := f.right.toMonoidHom) f.right.injective)

include d h hH c hd hz in
/-- All symplectic original extension rows, including the binary row, are
excluded without any outer-index or pure-model recognition premise. -/
theorem LocalData.zeroCore_not_symplectic_sourceExtension
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (E : SourceExtension
      (Theory.SpecificGroups.SymplecticFour.pointParabolic (F := F))
      (Theory.SpecificGroups.SymplecticFour.planeParabolic (F := F))) :
    ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R) E.amalgam) ∧
      ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv
        (zeroCoreAmalgam L H B D R) E.amalgam.reverse) :=
  d.zeroCore_not_sameSolvability_extension h hH c hd hz E (symplectic_parabolics_solvable_iff hm hF)

include d h hH c hd hz in
/-- Full G₂ extensions in either orientation are excluded at every actual
field degree. The binary model is the full G₂(2), without a derived-group shortcut. -/
theorem LocalData.zeroCore_not_g2_sourceExtension
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (E : SourceExtension (Atlas.G2.LieParabolicSetup.parabolic₁ (F := F))
      (Atlas.G2.LieParabolicSetup.parabolic₂ (F := F))) :
    ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R) E.amalgam) ∧
      ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv
        (zeroCoreAmalgam L H B D R) E.amalgam.reverse) :=
  d.zeroCore_not_sameSolvability_extension h hH c hd hz E (g2_parabolics_solvable_iff hm hF)

include d h hH c hd hz in
/-- Every genuine Ree extension is excluded, including Model 0. A binary
TYPE-only source clause remains separate and is not converted into this marking. -/
theorem LocalData.zeroCore_not_ree_sourceExtension (m : ℕ)
    (E : SourceExtension (ReeF4.Parabolics.parabolic m .suzuki)
      (ReeF4.Parabolics.parabolic m .linear)) :
    ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R) E.amalgam) ∧
      ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv
        (zeroCoreAmalgam L H B D R) E.amalgam.reverse) :=
  d.zeroCore_not_sameSolvability_extension h hH c hd hz E (ree_parabolics_solvable_iff m)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
