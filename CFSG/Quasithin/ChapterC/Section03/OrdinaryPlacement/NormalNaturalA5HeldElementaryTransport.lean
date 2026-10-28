module

public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.NormalNaturalA5HeldElementaryClasses
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations
public import Theory.ElementaryAbelian.Basic

/-!
# Transport to the certified Held Sylow subgroup

Conjugation preserves the number of elements in the actual class of `Held.a`.
Every elementary two-subgroup can be conjugated into the literal four-word
Sylow representative. These facts transfer native subgroup certificates to
arbitrary subgroups in the ordinary case of Aschbacher--Smith 12.7.5.
-/

public section
open Subgroup
open scoped Pointwise
namespace Held.OrdinaryElementary
open LocalPairs.SylowGeometry.Calculations

/-- The actual class-A count is unchanged by conjugating the subgroup. -/
theorem card_classA_map_conj (E : Subgroup He) (g : He) :
    Nat.card {x : E.map (MulAut.conj g).toMonoidHom // IsConj a (x : He)} =
      Nat.card {x : E // IsConj a (x : He)} := by
  let e := E.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  symm
  apply Nat.card_congr (Equiv.subtypeEquiv e.toEquiv ?_)
  intro x
  have hx : IsConj (x : He) (e x : He) := isConj_iff.mpr ⟨g, rfl⟩
  exact ⟨fun h => h.trans hx, fun h => h.trans hx.symm⟩

/-- An arbitrary elementary two-subgroup has a conjugate in the native Sylow. -/
theorem exists_conjugate_le_representative (E : Subgroup He)
    [IsElementaryAbelian 2 E] :
    ∃ g : He, E.map (MulAut.conj g).toMonoidHom ≤ representative := by
  obtain ⟨T, hET⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_le_sylow
  obtain ⟨P, hP⟩ := exists_representative_sylow representative_isPGroup
    InnerNormalizer.normalizer_eq
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq He T P
  refine ⟨g, ?_⟩
  have hTP : (T : Subgroup He).map (MulAut.conj g).toMonoidHom = representative := by
    change ((g • T : Sylow 2 He) : Subgroup He) = representative
    rw [hg, hP]
  rw [← hTP]
  exact map_mono hET

end Held.OrdinaryElementary
