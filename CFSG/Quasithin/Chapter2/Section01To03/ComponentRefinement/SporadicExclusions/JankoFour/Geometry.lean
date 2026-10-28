module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.JankoFour.Contracts
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.JankoFour.Geometry.SourceModel
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.JankoFour.Geometry.Lift
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.JankoFour.Geometry.Layers
public import Theory.GroupTheory.ComponentLocalOrbitEmbedding

/-!
# A Mathieu local cover for the J4 component

A seed B inside the component need only be normalized by N_S(L). The relative
component-orbit theorem proves characteristic two for ⟨B,S⟩ even when S permutes
components. Since this overgroup contains the source involution, its two-core
is nontrivial. Generation with the centralizer then gives a singleton cover.

The model seed and its actual source action are constructed in `SourceModel`.
`Lift` pulls it back through the central two-kernel, proving invariance,
generation and self-centralization and supplying a surjection onto M24.
`Layers` uses that surjection to identify the middle quotient of the full
S-overgroup with an actual direct power of M24. These results discharge every
seed premise and construct the cover from the original local setup and J4
quotient/action input.

Source: Aschbacher--Smith, 2.3.9(7), printed p.526; GLS3, Table 5.3i.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.ComponentRefinement.JankoFour
variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- Conditional ambient assembly, retaining relative component normality and the Mathieu-layer obligation. -/
theorem cover_of_component_seed (h : LocalSetup H L M S z) (B : Subgroup G)
    (hBL : B ≤ L)
    (hinv : (S : Subgroup H).map H.subtype ⊓ normalizer (L : Set G) ≤
      normalizer (B : Set G))
    (hgen : L ≤ centralizer ({z} : Set G) ⊔ B)
    (hself : centralizer (pCore 2 B : Set B) ≤ pCore 2 B)
    (hlayer : Sporadic.Mathieu.HasMathieuTwoLayer (B ⊔ (S : Subgroup H).map H.subtype : Subgroup G)) :
    Nonempty (MathieuLocalCover L ((S : Subgroup H).map H.subtype) z) := by
  let := h.finite
  let A := (S : Subgroup H).map H.subtype
  let K := B ⊔ A
  have hAK : A ≤ K := le_sup_right
  have he : K ∈ Chapter1.He G :=
    h.component.relative_local_adjoin_centralizer h.component_le hBL
      (map_subtype_le _) (S.isPGroup'.map H.subtype) hinv
      ((inf_centralizer_pCoreIn_le_iff 2 B).mpr hself)
  have hne : K.pCoreIn 2 ≠ ⊥ := by
    intro hb
    change K ⊓ centralizer _ ≤ _ at he
    rw [hb] at he
    have hz : z ∈ K := hAK h.mem_sylow
    have hz1 : z = 1 := he ⟨hz, by
      intro y hy
      have hy1 : y = 1 := hy
      simp only [hy1, one_mul, mul_one]⟩
    simpa [hz1] using h.involution
  refine ⟨{
    locals := {K}
    generated := ?_
    within := ?_
    even := ?_
    layers := ?_
  }⟩
  · rw [sSup_singleton]
    exact hgen.trans (sup_le_sup_left le_sup_left _)
  · intro U hU
    obtain rfl := Set.mem_singleton_iff.mp hU
    exact sup_le_sup_right hBL A
  · intro U hU
    obtain rfl := Set.mem_singleton_iff.mp hU
    exact ⟨he, hne, hAK⟩
  · intro U hU
    obtain rfl := Set.mem_singleton_iff.mp hU
    exact hlayer

/-- The supplied Sylow subgroup has a generating Mathieu local cover in L ∨ S.
The local setup and actual J4 quotient/action supply all seed and layer data. -/
theorem exists_mathieuLocalCover (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .j4) :
    Nonempty (MathieuLocalCover L ((S : Subgroup H).map H.subtype) z) := by
  obtain ⟨B, hBL, hinv, hgen, hself, f, hf, hker⟩ := exists_source_component_seed h d
  exact cover_of_component_seed h B hBL hinv hgen hself
    (hasMathieuTwoLayer_of_component_seed h B hBL hinv f hf hker)

end CFSG.Quasithin.Chapter2.ComponentRefinement.JankoFour

end
