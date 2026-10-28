module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.Moved
public import CFSG.Quasithin.ChapterB.Section06To07.Elementary

/-!+# Structural covers for the moved odd-prime branch

Only a selected family over the full prescribed Sylow is requested. Each
member is solvable, or is a genuine minimal parabolic on its own carrier
with a generating C-component whose actual two-core quotient is odd-prime
PSL₂. This is structural data: no E-generation conclusion is part of it.

The outstanding cover construction is isolated in the two-core-free case,
where the original marked component has become an actual simple component.
The reduction and conditional source assembly are proved in sibling modules.
Source: Aschbacher--Smith 10.3.3, p.756, and E.1.12--14, p.214.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration
universe u
variable {H : Type u} [Group H] [Finite H]

/-- A local structural row over the literal restriction of the ambient Sylow.
No condition is imposed on unselected overgroups. -/
def IsPrimeParabolicRow (S : Sylow 2 H) (P : Subgroup H) : Prop :=
  ∃ hSP : (S : Subgroup H) ≤ P,
    Group.IsSolvable P ∨
      (ChapterB.IsMinimalParabolicOver (S.subtype hSP) ⊤ ∧
        ∃ L : Subgroup P, L.IsCComponent ∧ IsQuasisimple (L ⧸ pCore 2 L) ∧
          L ⊔ (S.subtype hSP : Subgroup P) = ⊤ ∧
          ∃ q : ℕ, q.Prime ∧ Odd q ∧ 7 ≤ q ∧
            ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 q)

/-- A specified structural generating family, together with the full Sylow
normalizer. Its members need not be all minimal parabolics. -/
def HasPrimeParabolicCover (S : Sylow 2 H) : Prop :=
  ∃ Δ : Set (Subgroup H),
    (∀ P ∈ Δ, IsPrimeParabolicRow S P) ∧
      sSup Δ ⊔ normalizer (S : Set H) = ⊤

/-- The remaining model construction after removing the actual two-core.
The simple component and the full quotient Sylow retain their embeddings. -/
def CoreFreeMovedPrimeCover : Prop :=
  ∀ (H : Type u) [Group H] [Finite H], IsSQTK KnownSimple.IsKnownSimple H →
    pCore 2 H = ⊥ → ∀ (S : Sylow 2 H) (K : Subgroup H),
      IsComponent H K → IsSimpleGroup K → ¬K.Normal →
      K ⊔ (S : Subgroup H) = ⊤ →
      ∀ p : ℕ, p.Prime → Odd p → 7 ≤ p →
        ClassicalGroup.IsPSL K 2 p → HasPrimeParabolicCover S

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration
