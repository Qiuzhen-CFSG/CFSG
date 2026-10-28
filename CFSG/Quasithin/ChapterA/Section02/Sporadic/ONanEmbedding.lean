module

public import Theory.SpecificGroups.ONan.E9A4.Words
public import Theory.SpecificGroups.ONan.E9A4.Embedding
public import Theory.SpecificGroups.Alternating.E9A4LocalRank

/-!
# Assembly of the O'Nan subgroup used in A.2.19

The source embeds E₉ × A₄ through E₉ × A₆ (Aschbacher--Smith,
*The Classification of Quasithin Groups*, printed p. 41, PDF p. 52).
Here four fixed words in the actual projective O'Nan model give an injective
homomorphism from E₉ × A₄. The checked linear word matrices and projective
transition table discharge all premises of the original conditional assembly,
whose interfaces are preserved below. Applying the normal subgroup 1 × V₄
obstruction gives m₂,₃(ONan.Model) ≥ 3 and excludes quasithinness of this model.
Transport along source identifications and the odd-cover case belong to the
enclosing A.2.19 proof.
-/

public section
namespace CFSG.Quasithin.ChapterA

open Theory.SpecificGroups.E9A4

/-- Construct the candidate embedding from its finite projective transition checks. -/
noncomputable def onanE9A4HomOfTransitions
    (hnext : ∀ c i, ONan.E9A4.normalForm (next c i) =
      ONan.E9A4.normalForm c * ONan.E9A4.generators i) : Source →* ONan.Model :=
  homOfTransitions ONan.E9A4.generators hnext

/-- Conditional assembly; the concrete matrix certificates must discharge both premises. -/
theorem onanE9A4HomOfTransitions_injective
    (hnext : ∀ c i, ONan.E9A4.normalForm (next c i) =
      ONan.E9A4.normalForm c * ONan.E9A4.generators i)
    (hsep : Function.Injective ONan.E9A4.normalForm) :
    Function.Injective (onanE9A4HomOfTransitions hnext) :=
  homOfTransitions_injective ONan.E9A4.generators hnext hsep

/-- The unconditional subgroup embedding required by the O'Nan case of A.2.19. -/
noncomputable def onanE9A4Hom :
    Multiplicative (ZMod 3 × ZMod 3) × alternatingGroup (Fin 4) →* ONan.Model :=
  ONan.E9A4.embedding

/-- The fixed word construction embeds the actual E₉ × A₄ product. -/
theorem onanE9A4Hom_injective : Function.Injective onanE9A4Hom :=
  ONan.E9A4.embedding_injective

/-- The source's E₉ × A₄ subgroup gives its stated two-local rank obstruction. -/
theorem onan_three_le_twoLocalPrimeRank : 3 ≤ twoLocalPrimeRank 3 ONan.Model :=
  Theory.Quasithin.three_le_twoLocalPrimeRank_of_e9_prod_a4_embedding
    onanE9A4Hom onanE9A4Hom_injective

/-- The actual projective O'Nan model is not quasithin. -/
theorem onan_not_quasithin : ¬ IsQuasithin ONan.Model :=
  Theory.Quasithin.not_quasithin_of_e9_prod_a4_embedding
    onanE9A4Hom onanE9A4Hom_injective

end CFSG.Quasithin.ChapterA
