module
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.LocalPresentation
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.LocalRelations.Mixed.Contracts

/-!
# The first four max8 relations

The first four literal local words define a separate presentation. A checked
coset enumeration will bound its order by 12144. Mapping this group onto the
actual max8 subgroup requires only the quartic and first mixed equations.
The remaining five mixed equations and the order-23 equation are not assumed.

Source: John Bray, ATLAS M24G1-P1 and M24G1-max8W1; the unchanged local
words and their attribution are in `OrderBound/source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.FourRelators
open Subgroup.CosetWordCertificate

def relatorLetters (i : Fin 4) : Word (Fin 2) :=
  localRelatorLetters ⟨i.val, by omega⟩
def relator (i : Fin 4) : FreeGroup (Fin 2) := FreeGroup.mk (relatorLetters i)
abbrev Presented := PresentedGroup (Set.range relator)
def localGenerator (i : Fin 2) : Presented := PresentedGroup.of i

theorem generator_relations (i : Fin 4) : eval localGenerator (relatorLetters i) = 1 := by
  have hm : FreeGroup.lift localGenerator = PresentedGroup.mk (Set.range relator) := by
    apply FreeGroup.ext_hom
    intro i
    rfl
  change FreeGroup.lift localGenerator (relator i) = 1
  rw [hm]
  exact PresentedGroup.one_of_mem ⟨i, rfl⟩

def localCyclic : Subgroup Presented := Subgroup.zpowers (localGenerator 1)

theorem localCyclic_bound : Finite localCyclic ∧ Nat.card localCyclic ≤ 4 := by
  have hp : localGenerator 1 ^ 4 = 1 := by
    simpa [relatorLetters, localRelatorLetters, eval_cons, pow_succ, mul_assoc] using
      generator_relations 1
  have hx := isOfFinOrder_iff_pow_eq_one.mpr ⟨4, by decide, hp⟩
  refine ⟨hx.finite_zpowers.to_subtype, ?_⟩
  change Nat.card (Subgroup.zpowers (localGenerator 1)) ≤ 4
  rw [Nat.card_zpowers]
  exact orderOf_le_of_pow_eq_one (by decide) hp

/-- Exactly the first four equations on the unchanged abstract source subgroup. -/
theorem lifted_relations (hq : LocalRelations.QuarticRelation)
    (hf : LocalRelations.Mixed.FirstRelation) (i : Fin 4) :
    eval boundGenerator (relatorLetters i) = 1 := by
  fin_cases i
  · exact localRelator_zero_holds
  · exact localRelator_one_holds
  · exact hq
  · exact hf

def toUniversal (hq : LocalRelations.QuarticRelation)
    (hf : LocalRelations.Mixed.FirstRelation) : Presented →* UniversalGroup :=
  PresentedGroup.toGroup (f := boundGenerator) (by
    rintro _ ⟨i, rfl⟩
    exact lifted_relations hq hf i)

@[simp] theorem toUniversal_generator (hq : LocalRelations.QuarticRelation)
    (hf : LocalRelations.Mixed.FirstRelation) (i : Fin 2) :
    toUniversal hq hf (localGenerator i) = boundGenerator i :=
  PresentedGroup.toGroup.of _

theorem toUniversal_range (hq : LocalRelations.QuarticRelation)
    (hf : LocalRelations.Mixed.FirstRelation) : (toUniversal hq hf).range = boundSubgroup := by
  rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of (Set.range relator),
    MonoidHom.map_closure, ← Set.range_comp]
  congr 1
  apply congrArg Set.range
  funext i
  exact toUniversal_generator hq hf i

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.FourRelators
