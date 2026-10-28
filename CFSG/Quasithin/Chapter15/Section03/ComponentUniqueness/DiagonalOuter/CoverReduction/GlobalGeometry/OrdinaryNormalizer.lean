module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.GlobalGeometry.NormalizerEligibility
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.ComponentStructure.Outside

/-!
# Repeating the cover reduction for ordinary outside components

The full normalizer's larger C-component contains the original L outside M,
so it too lies outside M. The proved outside criterion promotes it to an
ordinary component. Its local overgroup hypotheses are supplied uniformly,
including the normalizer intersection and characteristic-two intersection
with M. Consequently the cover reduction need only be available for ordinary
outside components. The noncentral Y₊ action still proves Y₊≰L₁ through the
perfect-action argument in `NormalizerEligibility`.

Source: Aschbacher--Smith, combined 1 March 2004 manuscript, the adequate
outside route through 15.3.33 on p.1134 and the enlargement in 15.3.38, p.1136.
The universal inside-M C-component assertion is not used.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.GlobalGeometry
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The uniform local reduction only needs to treat ordinary outside
components. The larger C-component is promoted by the proved outside
criterion after all of its overgroup hypotheses have been supplied. -/
theorem normalizer_eq_of_ordinary_cover_reduction
    {κ : GroupClass.{u}} (earlier : EarlierEmbeddings κ)
    (hG : IsSimpleQTKE κ G)
    {Yplus S M I L V D : Subgroup G} [IsKleinFour V]
    (hI : I ∈ outsideFamily Yplus S M)
    (hSylow : OutsideSylowControl Yplus S M)
    (hQ : ∀ H ∈ outsideFamily Yplus S M, IsSQTK κ (H ⧸ pCore 2 H))
    (h25 : ∀ H ∈ outsideFamily Yplus S M, generalizedFitting H ≠ pCore 2 H)
    (hodd : ∀ H ∈ outsideFamily Yplus S M, pPrimeCore 2 H = ⊥)
    (hSM : S ≤ M)
    (hMI : ∀ H ∈ outsideFamily Yplus S M, H ⊓ normalizer (Yplus : Set G) = M ⊓ H)
    (hthree : IsPGroup 3 (Yplus ⧸ pCore 2 Yplus))
    (hFMI : ∀ H ∈ outsideFamily Yplus S M,
      generalizedFitting (M.subgroupOf H) = pCore 2 (M.subgroupOf H))
    (hLI : L ≤ I) (hL : IsComponent I (L.subgroupOf I))
    (hIL : I ≤ normalizer (L : Set G))
    (hZ : (center L).map L.subtype = V)
    (hLM : ¬ L ≤ M) (hrank : 2 ≤ primeRank 3 L)
    (hY : ¬ Yplus ≤ centralizer (V : Set G))
    (hgen : I = L ⊔ D ⊔ S)
    (reduce : ∀ H ∈ outsideFamily Yplus S M, ∀ B : Subgroup G,
      B ≤ H → IsComponent H (B.subgroupOf H) → (B.subgroupOf H).Normal →
      ¬ B ≤ M → primeRank 3 B = 2 → ¬ Yplus ≤ B →
      Nat.card (center B) = 4 ∧ Nonempty ((L ⧸ center L) ≃* (B ⧸ center B)) ∧
        H = B ⊔ D ⊔ S) :
    I = normalizer (V : Set G) := by
  apply normalizer_eq_of_uniform_cover_reduction earlier hG hI hSylow hQ hLI
    (component_isCComponent hL) hIL hZ hLM hrank hY hgen
  intro H hH B hBH hBC hBN hBM hB3 hYB
  have hBout : ¬ (B.subgroupOf H).map H.subtype ≤ M := by
    rwa [map_subgroupOf_eq_of_le hBH]
  have hB : IsComponent H (B.subgroupOf H) :=
    (Candidates.ComponentStructure.cComponent_ordinary_iff_outside hH hSylow h25 hodd
      hSM (hMI H hH) hthree (hFMI H hH) hBC).mpr hBout
  exact reduce H hH B hBH hB hBN hBM hB3 hYB

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.GlobalGeometry
