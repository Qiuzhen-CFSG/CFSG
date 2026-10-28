module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionPreparation
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.UnitaryFive.Exclusion

/-!
# Field filtering before original unitary-five extension collapse

The source endpoint embeds in the common original extension and contains the
image of the native line parabolic. Pulling that image back through the same
injective endpoint map constructs an actual line-parabolic embedding in G.
The proved quasithin rank obstruction then forces q = 4, including when the
original endpoint still has outer automorphisms. Both possible source endpoint
indices are retained. This does not assert that the extension has collapsed
or produce a pure amalgam comparison.

Source: Aschbacher--Smith F.1.12, final paragraph, printed p.264
(`refs/quasithin.pdf`). `UnitaryFive.Exclusion` owns the native obstruction;
this module applies it to the original marked source pair.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive

variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H R : Subgroup G} {n : ℕ}
  (h : Input κ T L W n)
include h

/-- Pull the marked native line parabolic back through the actual original
endpoint embedding, before making any inner-extension reduction. -/
theorem original_unitaryFive_extension_field
    {q : ℕ} (hq : IsPrimePow q) (heven : Even q) (M : Model q)
    {E : Type*} [Group E] (i : Fin 2)
    (f : ChapterF.Source.parabolic ![L,R] (sourceS L H) i →* E)
    (hf : Function.Injective f)
    (j : M.leftParabolic →* E) (hj : Function.Injective j)
    (hbase : j.range ≤ f.range) : q = 4 := by
  let j' : M.leftParabolic →* f.range :=
    j.codRestrict f.range (fun x => hbase ⟨x,rfl⟩)
  have hj' : Function.Injective j' := by
    intro x y hxy
    exact hj (congrArg Subtype.val hxy)
  let e := MonoidHom.ofInjective hf
  let P := ChapterF.Source.parabolic ![L,R] (sourceS L H) i
  exact M.field_size_eq_four_of_parabolic_embedding hq heven h.qtke.quasithin
    (P.subtype.comp (e.symm.toMonoidHom.comp j'))
    (P.subtype_injective.comp (e.symm.injective.comp hj'))

/-- The original U₅(2) extension is excluded in either endpoint orientation. -/
theorem not_original_unitaryFive_two_extension
    (M : Model 2) {E : Type*} [Group E] (i : Fin 2)
    (f : ChapterF.Source.parabolic ![L,R] (sourceS L H) i →* E)
    (hf : Function.Injective f)
    (j : M.leftParabolic →* E) (hj : Function.Injective j)
    (hbase : j.range ≤ f.range) : False := by
  have he := original_unitaryFive_extension_field h Nat.prime_two.isPrimePow
    (by decide) M i f hf j hj hbase
  exact (by decide : (2 : ℕ) ≠ 4) he
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
