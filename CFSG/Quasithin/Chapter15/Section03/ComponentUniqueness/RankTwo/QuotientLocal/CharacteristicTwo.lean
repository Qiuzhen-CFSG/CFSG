module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.QuotientLocal.Transport
public import Theory.GroupTheory.PCoreCentralizerQuotient

/-!
# Characteristic two in the component quotient

For the actual I⁺ = I/C_I(L), with L normal in I and I = LS for a two-group S,
characteristic two passes from M ∩ I to its image. Apply normal inheritance
to M ∩ L, descend through its central kernel, and then use the two-group
quotient above that image. This supplies the F*(M_I⁺) = O₂(M_I⁺) clause of
15.3.41(2) from the genuine 15.3.11(7) equality on M ∩ I.

The argument needs no extra assumption on Z(L); the other local-quotient
clauses remain with the LocalConfiguration assembly owner.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.11(7) and 15.3.41(2), printed pp.1123 and 1138.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo
variable {G : Type*} [Group G] [Finite G]

/-- Self-centralization of the two-core descends to the actual component image. -/
theorem componentImage_core_selfCentralizing {I L M S : Subgroup G}
    [(L.subgroupOf I).Normal] (hLI : L ≤ I) (hI : I = L ⊔ S)
    (hS : IsPGroup 2 S)
    (hM : centralizer (pCore 2 (M.subgroupOf I) : Set (M.subgroupOf I)) ≤
      pCore 2 (M.subgroupOf I)) :
    centralizer (pCore 2 (componentImage I L M) : Set (componentImage I L M)) ≤
      pCore 2 (componentImage I L M) := by
  have hjoin : L.subgroupOf I ⊔ S.subgroupOf I = ⊤ := by
    apply Subgroup.map_injective I.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hLI,
      map_subgroupOf_eq_of_le (hI ▸ le_sup_right)]
    simpa only [← MonoidHom.range_eq_map, range_subtype] using hI.symm
  have hq : IsPGroup 2 (I ⧸ L.subgroupOf I) :=
    isPGroup_quotient_of_sup_eq_top _ _ hS.comap_subtype hjoin
  exact centralizer_pCore_image_mod_centralizer (L.subgroupOf I) hq (M.subgroupOf I) hM

/-- The characteristic-two clause of 15.3.41(2), from the source 15.3.11(7)
equality before taking the component quotient. -/
theorem componentImage_characteristicTwo {I L M S : Subgroup G}
    [(L.subgroupOf I).Normal] (hLI : L ≤ I) (hI : I = L ⊔ S)
    (hS : IsPGroup 2 S)
    (hM : generalizedFitting (M.subgroupOf I) = pCore 2 (M.subgroupOf I)) :
    generalizedFitting (componentImage I L M) = pCore 2 (componentImage I L M) := by
  apply generalizedFitting_eq_pCore_of_selfCentralizing 2
  apply componentImage_core_selfCentralizing hLI hI hS
  rw [← hM]
  exact ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le
end CFSG.Quasithin.Chapter15.Section03.RankTwo

end
