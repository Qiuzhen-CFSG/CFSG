module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.GaschutzComplement.SourceSylow
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.GaschutzComplement

/-!
# Application of the constructed source Sylow to the complement deduction

Instantiate the literal Sylow carrier in the existing averaging theorem with
the subgroup constructed from G.2.5. The natural coordinates and earlier G.2.5
conclusions remain explicit inputs, owned by Sections G.2 and 14.3. The
preceding centralizer conclusions are exactly those in the parent theorem.
No source-specific Sylow, odd-index, or candidate two-group premise remains.

Source: Aschbacher--Smith 14.4.7, printed p.1009, final paragraph.
-/

public section
open Subgroup
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.GaschutzComplement
open Matrix.PSL3Two
variable {G : Type*} [Group G]

/-- Apply the actual source Sylow to the existing complement construction. -/
theorem source_complement_of_g25 [Finite G]
    (H U V V₁ V₂ L : Subgroup G) (g l : G) [IsMulCommutative V]
    (hg : g ∈ L) (hl : l ∈ L)
    (hgen : conjugateSpan U L = L ⊔ U)
    (hIV : conjugateSpan U L ≤ normalizer (V : Set G))
    (he : ∀ v ∈ V, v ^ 2 = 1)
    (hVU : V ≤ rightConjugate U g)
    (hUH : rightConjugate U g ≤ rightConjugate H g)
    (hbound : ∀ x ∈ L, ⁅conjugateCentralizer H U g, rightConjugate U x⁆ ≤
      rightConjugate V₁ x)
    (hline : ∀ x ∈ L, rightConjugate V₁ x ≤ V)
    (hW : U ⊓ centralizer (V₂ : Set G) ≤
      centralizer (conjugateCentralizer H U g : Set G))
    (hWl : rightConjugate U l ⊓ centralizer (V : Set G) ≤
      centralizer (conjugateCentralizer H U g : Set G))
    (hVL : V ⊓ centralizer (L : Set G) = ⊥)
    (hcenter : rightConjugate U g ⊓ centralizer (rightConjugate U g : Set G) =
      rightConjugate V₁ g)
    (m : SourceNaturalFrame U V V₁ V₂ L g l hIV)
    (hU : (U.subgroupOf (conjugateSpan U L)).map m.actor = SourceFlag.secondRadical)
    (hUg : ((rightConjugate U g).subgroupOf (conjugateSpan U L)).map m.actor =
      MarkedAutomorphisms.pointV)
    (hfaith : (centralizer (V : Set G)).subgroupOf (conjugateSpan U L) =
      pCore 2 (conjugateSpan U L))
    (hnorm : pCore 2 (conjugateSpan U L) ≤
      normalizer (U.subgroupOf (conjugateSpan U L) : Set (conjugateSpan U L)))
    (hcore : (pCore 2 (conjugateSpan U L) : Set (conjugateSpan U L)) =
      (U.subgroupOf (conjugateSpan U L) ⊓ pCore 2 (conjugateSpan U L) : Set _) *
      ((rightConjugate U g).subgroupOf (conjugateSpan U L) ⊓ pCore 2 (conjugateSpan U L) : Set _) *
      ((rightConjugate U l).subgroupOf (conjugateSpan U L) ⊓ pCore 2 (conjugateSpan U L) : Set _)) :
    conjugateCentralizer H U g = rightConjugate V₁ g ⊔
      (conjugateCentralizer H U g ⊓ centralizer (L : Set G)) ∧
    ((conjugateCentralizer H U g ⊓ centralizer (L : Set G)).subgroupOf
      (conjugateCentralizer H U g)).IsComplement'
      ((rightConjugate V₁ g).subgroupOf (conjugateCentralizer H U g)) ∧
    (conjugateCentralizer H U g ⊓ centralizer (L : Set G) = ⊥ →
      conjugateCentralizer H U g = rightConjugate V₁ g) ∧
    ∃ e : V × ↥(conjugateCentralizer H U g ⊓ centralizer (L : Set G)) ≃*
      ↥(conjugateCentralizer H U g ⊔ V),
      ∀ v c, (e (v, c) : G) = (v : G) * (c : G) := by
  obtain ⟨_, P, hP⟩ := source_sylow U V V₁ V₂ L g l hg hl hIV m hgen
    hU hUg hfaith hnorm hcore
  exact source_complement_of_sylow H U V V₁ V₂ L g l hg hl hgen hIV he
    hVU hUH hbound hline hW hWl hVL hcenter P hP

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.GaschutzComplement
