module
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.TripleSevenExclusion.Intrinsic
public import Theory.Representation.BinaryOffender.CubicCenterSections
public import Theory.Representation.BinaryOffender.CubicSection
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models

/-!
# Triple-seven exclusion without irreducibility

In any faithful binary action of 3·A₇, the cubic-center construction supplies
an actual faithful irreducible section. Cubic action and the same actor's
fixed-codimension bound pass to this section. The established intrinsic
triple-seven exclusion applies there, so the original representation has
cubic ratio greater than two. Neither semisimplicity nor absence of global
fixed vectors is assumed.

The final theorem uses the actual perfect three-cover predicate consumed by
C.5.13, retaining its genuine quotient and cubic center. Source: Aschbacher–Smith
C.5.13, printed p.163, and K.1, printed p.452.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open GLS3.Chapter5.OddCentralCovers
namespace CFSG.Quasithin.ChapterK.Alternating
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- Every faithful binary action of the genuine triple cover has cubic ratio
strictly greater than two, even when the original module is reducible. -/
theorem two_lt_cubicRatio_of_tripleSeven
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (e : G≃*TripleSeven) : 2 < cubicRatio ρ := by
  by_contra! hq
  let : IsQuasisimple G := IsQuasisimple.of_mulEquiv e.symm
  let L : Subgroup G := ⊤
  let eL : L≃*G := topEquiv
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv eL.symm
  have hc : Nat.card (center L)=3 :=
    (Nat.card_congr (centerCongr (eL.trans e)).toEquiv).trans tripleSeven_center_card
  obtain ⟨I,hI,hfaith⟩ := exists_faithful_isIrrPlus_of_cubic_center ρ L
    (hf.comp L.subtype_injective) hc
  let σ := centralQuotientRepresentation ρ L I hI.choose
  have hσ : IsIrreducible σ := hI.choose_spec.2
  have hqL : cubicRatio (ρ.comp L.subtype) ≤ 2 := cubicRatio_comp_equiv_le_nat ρ eL 2 hq
  have hqI := cubicRatio_subrepresentation_le_nat (ρ.comp L.subtype)
    (invariantSubspace ρ L I hI.choose) 2 hqL
  have hqσ : cubicRatio σ ≤ 2 := cubicRatio_quotient_le_nat
    (invariantSubspace ρ L I hI.choose).toRepresentation
    (centralSubspace ρ L I hI.choose) 2 hqI
  let f : TripleSeven≃*L := (eL.trans e).symm
  exact tripleSevenIntrinsicExclusion (σ.comp f.toMonoidHom) (hfaith.comp f.injective)
    ((irreducible_comp_surjective_iff f.toMonoidHom f.surjective σ).mpr hσ)
    (cubicRatio_comp_equiv_le_nat σ f 2 hqσ)

/-- The actual three-cover model in the source is excluded on the original
faithful module. No choice of a replacement actor is assumed. -/
theorem not_alternating_seven_cover_of_cubic_ratio
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (hq : cubicRatio ρ ≤ 2) : ¬ Chapter1.Section02.LocalModels.IsAlternatingCover G 7 := by
  rintro ⟨hG,⟨eZ⟩,⟨eQ⟩⟩
  let : IsQuasisimple G := hG
  have hc : Nat.card (center G)=3 := by
    rw [Nat.card_congr eZ.toEquiv]
    simp [Nat.card_eq_fintype_card]
  obtain ⟨e⟩ := triple_seven_equiv eQ hc
  exact (not_lt_of_ge hq) (two_lt_cubicRatio_of_tripleSeven ρ hf e)

end CFSG.Quasithin.ChapterK.Alternating
