module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Cases
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.EmptyCase
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Transport
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Elementary
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.Coordinates
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.Intersections
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.Eight.Transfer
public import CFSG.Quasithin.Chapter16.Section01To02.SourceHypothesis

/-!
# The A₈ marked-set and transfer argument

The five-coordinate calculation derives the exclusions for products of two,
three, four and five marked elements. It identifies zᴳ ∩ A with the source
set {z} ∪ (rᴸ ∩ A), derives nonfusion into L⟨rz⟩ and applies Thompson
transfer to the two-residual O²(G). The exact compatible transport from
16.4.2(4) identifies r with zᵍ; no appeal to the later 16.4.10 is made.

The theorem below is conditional on a marked embedding, its actual
conjugate-component placements, and the model's Sylow and index calculations.
Their construction from `AlternatingProductModel L z r 8` remains required
for the full A₈ branch of 16.4.9(2). In particular, this module does not
assert that the product-model witness alone supplies these geometric facts.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 16.4.9(2), printed p.1192.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.AlternatingEight
open Subgroup
variable {G : Type*} [Group G] [Finite G] {K : GroupClass}

/-- Conditional assembly with the actual 16.4.2(4) transport and the actual
A₈ identification. Only simplicity and nonabelianness of 16.1.1 are used,
so the K-class stays parametric. The remaining geometric premises are construction targets,
not substitutes for the source theorem. -/
theorem deltaZero_nonempty_of_marked_data
    {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}
    (hG : Hypothesis1611 K G)
    (h : IntersectionSetup T z L g R) (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hsmall : OrderTwoOutsideDeltaZero L) (hTC : commutingSylow T L = zpowers z)
    (htransport : (T : Subgroup G) ⊓
      normalizer ((centralizer (L : Set G)).conjBy g : Set G) ≤ (T : Subgroup G).conjBy g)
    (e : L ≃* alternatingGroup (Fin 8)) (F : MarkedEmbedding L z r)
    (hplacements : ¬ (deltaZero L).Nonempty → Nonempty (Placements F))
    (htransfer : TransferGeometry F T) : (deltaZero L).Nonempty := by
  let := hG.simple
  have hrz : r = MulAut.conj g z :=
    h.involution_eq_conjugate_of_commutingSylow hTC htransport hr hr2
  have hrconj : IsConj z r := isConj_iff.mpr ⟨g, hrz.symm⟩
  by_contra hempty
  obtain ⟨P⟩ := hplacements hempty
  exact hempty (deltaZero_nonempty_of_geometry hG.nonabelian F h.toStandardSetup hsmall
    (disjoint_centralizer_of_alternating_equiv (by decide : 4 ≤ 8) e) hrconj P htransfer)

end CFSG.Quasithin.Chapter16.Intersections.AlternatingEight
