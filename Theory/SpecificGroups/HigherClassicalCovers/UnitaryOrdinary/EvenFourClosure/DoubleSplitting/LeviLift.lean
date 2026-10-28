module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure.DoubleSplitting.Setup
public import Theory.GroupTheory.CentralExtensionSections
public import GorensteinWalter.PSL2EvenDefiningKernel
public import BenderSuzuki.Converse.PSL2


/-!
# Lifting the marked plane Levi subgroup

Restriction of a central cover to the literal block diagonal SL₂ gives a
central extension of SL₂. In characteristic two SL₂ equals its projective
quotient. The checked even PSL₂ multiplier calculation makes the identity
cover universal when the field has at least eight elements, and hence gives
a section of this prescribed extension. Composing with the subgroup inclusion
lifts the original Levi map into the covering group.

Source: the even linear-two and unitary-four multiplier rows in
Aschbacher–Smith I.1.3–4, printed pp.407–408 of `refs/quasithin.pdf`,
and GLS3 §6.1. This lifts only the Levi; radical splitting is separate.
-/

@[expose] public noncomputable section

open BenderSuzuki.MatrixGroups Theory.GroupTheory
open Theory.SpecificGroups.ClassicalUnitary PerfectCentralCovering
open scoped MatrixGroups

namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure.DoubleSplitting
universe u
variable {F : Type u} [Field F] [Finite F] [CharP F 2]

private noncomputable def slEquivPSL : SL(2, F) ≃* PSL(2, F) :=
  MulEquiv.ofBijective (BenderSuzuki.Converse.pi F)
    ⟨BenderSuzuki.Converse.pi_injective, BenderSuzuki.Converse.pi_surjective⟩

private theorem sl2_section {D : Type u} [Group D] [Finite D]
    (hF : 8 ≤ Nat.card F) (f : D →* SL(2, F))
    (hf : Function.Surjective f) (hc : f.ker ≤ Subgroup.center D) :
    ∃ s : SL(2, F) →* D, f.comp s = MonoidHom.id _ := by
  let e : SL(2, F) ≃* PSL(2, F) := slEquivPSL
  let : Fact (3 < Nat.card F) := ⟨by omega⟩
  have heven : Even (Nat.card F) := by
    let : Fintype F := Fintype.ofFinite F
    exact Nat.even_iff.mpr (by
      simpa only [Nat.card_eq_fintype_card] using
        (FiniteField.even_card_of_char_two (ringChar.eq F 2)))
  have hk : (e.toMonoidHom.comp f).ker ≤ Subgroup.center D := by
    intro x hx
    apply hc
    change f x = 1
    apply e.injective
    rw [map_one]
    exact hx
  obtain ⟨s, hs⟩ := CentralExtension.exists_section_of_universal_cover
    (Covering.id : Covering PSL(2, F) PSL(2, F))
    (GorensteinWalter.PSL2Cover.identity_isUniversal_of_even F heven hF)
    (e.toMonoidHom.comp f) (e.surjective.comp hf) hk
  refine ⟨s.comp e.toMonoidHom, ?_⟩
  apply MonoidHom.ext
  intro A
  apply e.injective
  exact DFunLike.congr_fun hs (e A)

/-- Every finite central cover admits a lift of the actual block diagonal Levi. -/
theorem exists_levi_lift (J : HermitianForm 4 F)
    (hF : 8 ≤ Nat.card F) {E : Type u} [Group E] [Finite E]
    (d : Cover E (Standard J)) :
    ∃ l : SL(2, F) →* E, d.toMonoidHom.comp l = leviInclusion J := by
  let j := leviInclusion J
  let H := j.range.comap d.toMonoidHom
  let e := MonoidHom.ofInjective (leviInclusion_injective J)
  let q₀ : H →* j.range := d.toMonoidHom.subgroupComap j.range
  let q : H →* SL(2, F) := e.symm.toMonoidHom.comp q₀
  have hq (x : H) : j (q x) = d.toMonoidHom x :=
    congrArg Subtype.val (e.apply_symm_apply (q₀ x))
  have hqsur : Function.Surjective q :=
    e.symm.surjective.comp
      (d.toMonoidHom.subgroupComap_surjective_of_surjective j.range d.surjective)
  have hqker {x : H} (hx : x ∈ q.ker) : (x : E) ∈ d.toMonoidHom.ker := by
    change d.toMonoidHom x = 1
    rw [← hq, MonoidHom.mem_ker.mp hx, map_one]
  have hqcentral : q.ker ≤ Subgroup.center H := fun x hx =>
    Subgroup.mem_center_iff.mpr fun y =>
      Subtype.ext (Subgroup.mem_center_iff.mp (d.ker_le_center (hqker hx)) y)
  obtain ⟨s, hs⟩ := sl2_section hF q hqsur hqcentral
  refine ⟨H.subtype.comp s, ?_⟩
  apply MonoidHom.ext
  intro A
  change d.toMonoidHom (s A) = j A
  rw [← hq]
  exact congrArg j (DFunLike.congr_fun hs A)

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure.DoubleSplitting
