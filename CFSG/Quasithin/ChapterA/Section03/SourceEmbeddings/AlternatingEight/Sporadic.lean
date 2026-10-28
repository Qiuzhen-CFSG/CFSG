module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight.SporadicJanko
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight.SporadicMathieu
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight.SporadicLargeSylow

/-!
# The complete sporadic containing-model sieve for the original A₈ section

The literal local C-component B is normalized by the original full Sylow
and has B/O₂(B) isomorphic to PSL₄(2). The actual Theorem C sporadic
catalogue then leaves only M₂₄ and J₄. The order, element-order, local
normalizer and faithful Sylow arguments in the imported modules cover
all other rows, including both possibilities for the original two-core.

Source: Aschbacher–Smith A.3.12, printed pp.47–48, used in the original
15.3.32(3), printed p.1133. J₃ is absent from Theorem C, as encoded by
its existing `name ≠ .j3` constructor hypothesis.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight
variable {G : Type*} [Group G] [Finite G]

/-- The actual Theorem C sporadic row containing the literal local A₈ section
is M₂₄ or J₄. The original subgroup need not be quasisimple. -/
theorem sporadic_m24_or_j4 (S : Sylow 2 G) (B : Subgroup G)
    (hB : B ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2)
    (name : ClassificationModels.SporadicName) (hne : name ≠ .j3)
    (he : Nonempty (G ≃* name.Carrier)) :
    Nonempty (G ≃* Sporadic.Mathieu.M24) ∨ Nonempty (G ≃* Janko4.Model) := by
  obtain ⟨e⟩ := he
  cases name with
  | m11 => exact (not_mathieu_eleven h e).elim
  | m12 => exact (not_mathieu_twelve h e).elim
  | m22 => exact (not_mathieu_twentyTwo h e).elim
  | m23 => exact (not_mathieu_twentyThree S B hB hn h e).elim
  | m24 => exact Or.inl ⟨e⟩
  | j2 => exact (not_janko_two S B hB hn h e).elim
  | j3 => exact (hne rfl).elim
  | j4 => exact Or.inr ⟨e⟩
  | hs => exact (not_higmanSims S B hB hn h e).elim
  | he => exact (not_held S B hB hn h e).elim
  | ru => exact (not_rudvalis S B hB hn h e).elim

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight
