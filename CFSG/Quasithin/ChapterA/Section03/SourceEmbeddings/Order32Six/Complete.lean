module

public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Order32Six.JankoFour
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Order32Six.Held
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.Source
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete

/-!
# The original order-32 A₆ section is impossible

The actual ordinary-carrier inspection leaves J₄ and Held. The native Held
cubic-commutator relation excludes its full A₆ section, and the J₄ Mathieu
placement and first-centralizer triple-cover obstruction exclude the remaining
carrier. Every application uses the supplied B, K and Sylow T, including
the literal restriction B.subgroupOf K and the full intrinsic two-core quotient.
No catalogue, module-recognition or centralizer-placement premise remains.

This is the specialized A.3.12 input in the final M₂₂-code contradiction
of Aschbacher–Smith 8.2.13, pp.722–723, using A.3.12, pp.47–48.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Order32Six

/-- The unchanged original source configuration with core order32 and full
A6 quotient has no containing proper C-component. -/
theorem source_order32_six_excluded {G : Type*} [Group G] [Finite G]
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (hO : pCore 2 G = ⊥)
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents T) (hK : K.IsCComponent) (hBK : B < K)
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hcore : Nat.card (pCore 2 B) = 32)
    (hA6 : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))) : False :=
  source_not_janko_four T hB hK hBK hTB hcore hA6
    (remaining_jankoFour hG hO T hB hK hBK hTB hcore hA6)

/-- The original local order-32 A6 section is impossible without choosing
a containing component. Genuine Theorems A and C produce that component;
subnormality and the ambient trivial two-core make containment proper. -/
theorem no_local_order32_six {G : Type*} [Group G] [Finite G]
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (hO : pCore 2 G = ⊥)
    (S : Sylow 2 G) (B : Subgroup G)
    (hlocal : B ∈ localCComponents S)
    (hnorm : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hcore : Nat.card (pCore 2 B) = 32)
    (hA6 : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))) : False := by
  obtain ⟨K,⟨hK,hBK⟩,_⟩ := Chapter1.Section02.containment_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X)) G hG hO S B hlocal
  have hne : B ≠ K := by
    intro he
    have hzero : pCore 2 B = ⊥ := by
      apply (map_eq_bot_iff_of_injective (pCore 2 B) B.subtype_injective).mp
      exact bot_unique ((pCoreIn_le_of_subnormal 2 (he.symm ▸ hK.subnormal)).trans hO.le)
    rw [hzero,card_bot] at hcore
    omega
  exact source_order32_six_excluded hG hO S hlocal hK (lt_of_le_of_ne hBK hne)
    hnorm hcore hA6

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Order32Six
