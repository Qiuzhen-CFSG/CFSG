module

public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.NormalNaturalA5HeldPlaced
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.NormalNaturalA5HeldElementaryCentralizer

/-!
# Excluding the actual ordinary actor in a conjugate Held core

The pure elementary16 recovers its native local overgroup through its fixed
sextet. Conjugation places the original actor, module and whole native core
through one injective map. The section-centralizer condition then contradicts
the literal cubic, without an additional actor-placement assumption.

Source: the Held row of Aschbacher--Smith12.7.5, printed p.840.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterC.OrdinaryPlacement
open Held.LocalPairs.PairCoverage
open Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.CoreKernel

/-- A pure16 placed in a conjugate native core cannot be the original
fully fixed module of a perfect actor normalizing it. -/
theorem held_no_pure_sixteen_fixed_section
    (B E : Subgroup Held.He) [Group.IsPerfect B]
    (hE : Nat.card E = 16) (hpure : ∀ x : E, ¬ IsConj Held.a (x : Held.He))
    (hEB : E ≤ B) (hBN : B ≤ normalizer (E : Set Held.He))
    (i : Bool) (g : Held.He)
    (hplace : E ≤ (ambientWordCore i).map (MulAut.conj g).toMonoidHom)
    (hfixed : ChapterA.Section04.twoSectionCentralizer B ⊤ ≤
      centralizer (E : Set Held.He)) : False := by
  let α := MulAut.conj g
  let E₀ := E.comap α.toMonoidHom
  let B₀ := B.comap α.toMonoidHom
  have hErange : E ≤ α.toMonoidHom.range := by
    rw [MonoidHom.range_eq_top_of_surjective _ α.surjective]
    exact le_top
  have hBrange : B ≤ α.toMonoidHom.range := by
    rw [MonoidHom.range_eq_top_of_surjective _ α.surjective]
    exact le_top
  have hEm : E₀.map α.toMonoidHom = E := map_comap_eq_self hErange
  have hBm : B₀.map α.toMonoidHom = B := map_comap_eq_self hBrange
  have hE₀ : E₀ ≤ ambientWordCore i := by
    intro x hx
    exact (mem_map_iff_mem α.injective).mp (hplace hx)
  have hE₀c : Nat.card E₀ = 16 := by
    rw [←card_map_of_injective (K := E₀) (f := α.toMonoidHom) α.injective,hEm]
    exact hE
  have hpure₀ : ∀ x : E₀, ¬ IsConj Held.a (x : Held.He) := by
    intro x hx
    exact hpure ⟨α x,x.property⟩ (hx.trans (isConj_iff.mpr ⟨g,rfl⟩))
  have hB₀ : B₀ ≤ localOvergroup i :=
    ((comap_mono hBN).trans (E.le_normalizer_comap α.toMonoidHom)).trans
      (HeldElementaryCentralizer.normalizer_pure_sixteen_le_local E₀ hE₀c hpure₀ i hE₀)
  let f : localOvergroup i →* Held.He := α.toMonoidHom.comp (localOvergroup i).subtype
  have hf : Function.Injective f := α.injective.comp (localOvergroup i).subtype_injective
  have hBf : B ≤ f.range := by
    rw [show f = α.toMonoidHom.comp (localOvergroup i).subtype from rfl,
      MonoidHom.range_comp,range_subtype,←hBm]
    exact map_mono hB₀
  have hEf : E ≤ (pCore 2 (localOvergroup i)).map f := by
    rw [show f = α.toMonoidHom.comp (localOvergroup i).subtype from rfl,←map_map]
    simpa only [ambientWordCore,wordCore_eq_pCore] using hplace
  have hQc : Nat.card (pCore 2 (localOvergroup i)) = 64 := by
    have hh := HeldElementaryCentralizer.card_ambientWordCore i
    simpa only [ambientWordCore,wordCore_eq_pCore,
      card_map_of_injective (localOvergroup i).subtype_injective] using hh
  exact held_not_placed_with_fixed_sectionCentralizer i f hf B E hBf hEB hEf hE hQc hfixed

end CFSG.Quasithin.ChapterC.OrdinaryPlacement
