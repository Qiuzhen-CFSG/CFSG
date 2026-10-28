module

public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Tori.RankOne
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Tori.LinearThree
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Tori.SymplecticFour
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Tori.UnitaryThree
public import Theory.GroupTheory.CyclicQuotientEmbedding

/-!
# Cyclic subgroups from all surviving E.2.2 markings

Restrict the actual component recognition to the marked Borel and embed a
concrete cyclic torus. The surjection from M ∩ K to its image in X/J then
lifts its order to a cyclic subgroup upstairs. This finite cyclic lifting
argument preserves possible central extensions; it does not assert a section
of the quotient map. The unitary torus uses the Hermitian fixed field, and
the symplectic torus remains inside Sp₄′.

Each of the exchanged, Bender and diagram alternatives therefore supplies a
cyclic subgroup of order 2^n(X)-1 in the original unique maximal subgroup.
Placing it inside an abelian odd Hall group remains a separate construction.
Source: Aschbacher--Smith, E.2.2 and E.6.27, pp.215--216 and 257.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
universe u v w
variable {X : Type u} [Group X] [Finite X]

/-- The one marking identifies both the component and its Borel. -/
noncomputable def componentBorelEquiv {M K : Subgroup X}
    {A : Type v} [Group A] (B : Subgroup A)
    (e : sourceImage M K ≃* A)
    (he : (componentOverlap M K).map e.toMonoidHom = B) :
    sourceImage M (M ⊓ K) ≃* B :=
  (subgroupOfEquivOfLe (map_mono (f := QuotientGroup.mk' (sourceKernel M))
    (inf_le_right (a := M) (b := K)))).symm.trans
      ((e.subgroupMap _).trans (MulEquiv.subgroupCongr he))

/-- Lift the order of a cyclic torus from the marked Borel. This does not
assert a section of the quotient map or split a central extension. -/
theorem cyclic_of_marked_borel {M K : Subgroup X}
    {A : Type v} [Group A] {B : Subgroup A}
    (hB : ModelBorelPair M K B)
    {C : Type w} [Group C] [IsCyclic C]
    (i : C →* B) (hi : Function.Injective i) :
    ∃ D : Subgroup X, D ≤ M ∧ IsCyclic D ∧ Nat.card D = Nat.card C := by
  obtain ⟨e, he⟩ := hB
  let q := QuotientGroup.mk' (sourceKernel M)
  let b := componentBorelEquiv B e he
  obtain ⟨j, hj⟩ := Theory.GroupTheory.cyclic_injective_of_surjective
    (q.subgroupMap (M ⊓ K)) (q.subgroupMap_surjective (M ⊓ K))
    (b.symm.toMonoidHom.comp i) (b.symm.injective.comp hi)
  let k := (M ⊓ K).subtype.comp j
  have hk : Function.Injective k := (M ⊓ K).subtype_injective.comp hj
  refine ⟨k.range, ?_, ?_, ?_⟩
  · rintro _ ⟨c, rfl⟩
    exact (j c).property.1
  · exact isCyclic_of_surjective k.rangeRestrict k.rangeRestrict_surjective
  · exact (Nat.card_congr (MonoidHom.ofInjective hk).toEquiv).symm

/-- The exchanged linear/Suzuki markings supply a cyclic subgroup of exact
order 2^f - 1 in the original maximal subgroup, before choosing a Hall group. -/
theorem ExchangedModel.cyclic {M K : Subgroup X} {f : ℕ}
    (h : ExchangedModel M K f) :
    ∃ D : Subgroup X, D ≤ M ∧ IsCyclic D ∧ Nat.card D = 2 ^ f - 1 := by
  rcases h with ⟨F, hfield, hfin, hchar, hf, hF, hB⟩ | ⟨m, hm, hf, hB⟩
  · let := hfield
    let := hfin
    let := hchar
    obtain ⟨D, hDM, hc, hD⟩ := cyclic_of_marked_borel hB
      (Tori.psl2Torus (F := F)) Tori.psl2Torus_injective
    exact ⟨D, hDM, hc, by simpa only [Nat.card_units, hF] using hD⟩
  · obtain ⟨D, hDM, hc, hD⟩ := cyclic_of_marked_borel hB
      (Tori.suzukiTorus m hm) (Tori.suzukiTorus_injective m hm)
    refine ⟨D, hDM, hc, ?_⟩
    rw [hD, Nat.card_units, hf]
    congr 1
    exact GaloisField.card 2 (2 * m + 1) (by omega)

/-- The unitary parameter is the fixed-field order. The projective torus
uses fixed-field units, never the full quadratic-field unit group. -/
theorem UnitaryModel.cyclic {M K : Subgroup X} {f : ℕ}
    (h : UnitaryModel M K f) :
    ∃ D : Subgroup X, D ≤ M ∧ IsCyclic D ∧ Nat.card D = 2 ^ f - 1 := by
  obtain ⟨F, hfield, hfin, hchar, J, hJ, hf, hF, hconj, hfixed, hB⟩ := h
  let := hfield
  let := hfin
  let := hchar
  obtain ⟨D, hDM, hc, hD⟩ := cyclic_of_marked_borel hB
    (Tori.psu3Torus J hJ) (Tori.psu3Torus_injective J hJ)
  refine ⟨D, hDM, hc, ?_⟩
  rw [hD, Nat.card_units]
  exact congrArg (fun n : ℕ => n - 1) hfixed

/-- All three single Bender families use the actual marked Borel. -/
theorem BenderModel.cyclic {M K : Subgroup X} {f : ℕ}
    (h : BenderModel M K f) :
    ∃ D : Subgroup X, D ≤ M ∧ IsCyclic D ∧ Nat.card D = 2 ^ f - 1 :=
  h.elim ExchangedModel.cyclic UnitaryModel.cyclic

/-- The rank-two torus remains in Sp₄′; no identification with Sp₄ is used. -/
theorem DiagramModel.cyclic {M K T : Subgroup X} {f : ℕ}
    (h : DiagramModel M K T f) :
    ∃ D : Subgroup X, D ≤ M ∧ IsCyclic D ∧ Nat.card D = 2 ^ f - 1 := by
  rcases h with ⟨F, hfield, hfin, hchar, hf, hF, e, hB, hdiagram⟩ |
    ⟨F, hfield, hfin, hchar, hf, hF, e, hB, hdiagram⟩
  · let := hfield
    let := hfin
    let := hchar
    obtain ⟨D, hDM, hc, hD⟩ := cyclic_of_marked_borel ⟨e, hB⟩
      (Tori.psl3Torus F) (Tori.psl3Torus_injective F)
    exact ⟨D, hDM, hc, by simpa only [Nat.card_units, hF] using hD⟩
  · let := hfield
    let := hfin
    let := hchar
    obtain ⟨D, hDM, hc, hD⟩ := cyclic_of_marked_borel ⟨e, hB⟩
      (Tori.sp4DerivedTorus (F := F)) Tori.sp4DerivedTorus_injective
    exact ⟨D, hDM, hc, by simpa only [Nat.card_units, hF] using hD⟩

/-- The source reduction supplies the cyclic subgroup in every surviving case. -/
theorem ReducedCases.cyclic {M K T : Subgroup X} {f : ℕ}
    (h : ReducedCases M K T f) :
    ∃ D : Subgroup X, D ≤ M ∧ IsCyclic D ∧ Nat.card D = 2 ^ f - 1 := by
  cases h with
  | exchanged _ hm => exact hm.cyclic
  | bender _ hm => exact hm.cyclic
  | diagram _ hm => exact hm.cyclic

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
