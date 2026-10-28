module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.LocalCentralizers
public import Theory.SpecificGroups.Janko1.Model.Presentation.Comparison

/-!+# A presentation route to J₁ uniqueness with two explicit premises

The requested source recognition theorem has inputs `Janko1CentralizerData G`,
order 175560 and fusion of involutions, for finite simple `G`. This module
proves its assembly through the full ATLAS presentation, retaining two missing
mathematical premises: a finite upper bound on that presentation and a
nontrivial pair in `G` satisfying its five relators. The source theorem is not
yet proved here.

Fusion conjugates any such pair so its first element is the distinguished
involution. The comparison map in `Presentation.Comparison` then gives an
actual equivalence to the specified matrix group. Pair generation need not be
assumed: simplicity of the matrix model and the supplied ambient order imply
surjectivity of that comparison map.

Source: Aschbacher–Smith, I.4.9, printed p.418, citing Z. Janko,
*A new finite simple group with abelian Sylow 2-subgroups and its
characterization*, J. Algebra 3 (1966), 147–186,
https://doi.org/10.1016/0021-8693(66)90010-X.
The five relators are the literal ones from ATLAS `J1G1-P1`.
-/

namespace CFSG.Quasithin.Janko1CentralizerData

variable {G : Type*} [Group G] [Finite G] (h : Janko1CentralizerData G)

/-- Under the supplied involution fusion, a nontrivial relator pair can be
chosen with first element exactly the source involution. -/
public theorem exists_marked_atlas_pair_iff
    (hfusion : ∀ x : G, orderOf x = 2 → ∃ g : G, g * x * g⁻¹ = h.z) :
    (∃ y : G, ∀ i, Janko1.atlasWord h.z y i = 1) ↔
      ∃ x y : G, x ≠ 1 ∧ ∀ i, Janko1.atlasWord x y i = 1 := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨h.z, y, h.z_ne_one, hy⟩
  · rintro ⟨x, y, hx, hrel⟩
    have hx2 : x ^ 2 = 1 := hrel 0
    obtain ⟨g, hg⟩ := hfusion x (orderOf_eq_prime hx2 hx)
    refine ⟨g * y * g⁻¹, ?_⟩
    simpa only [hg] using Janko1.atlas_relations_conj x y g hrel

/-- The source application of the actual comparison map. Its two additional
premises are the presentation bound and the existence of a relator pair. -/
public theorem nonempty_equiv_of_atlas_bound_and_pair
    (horder : Nat.card G = 175560)
    (hfusion : ∀ x : G, orderOf x = 2 → ∃ g : G, g * x * g⁻¹ = h.z)
    (hbound : Finite Janko1.AtlasPresentation ∧
      Nat.card Janko1.AtlasPresentation ≤ 175560)
    (hpair : ∃ x y : G, x ≠ 1 ∧ ∀ i, Janko1.atlasWord x y i = 1) :
    Nonempty (G ≃* Janko1.Model) := by
  obtain ⟨y, hy⟩ := (h.exists_marked_atlas_pair_iff hfusion).mpr hpair
  exact ⟨Janko1.equivModelOfAtlasPair hbound horder h.z y h.z_ne_one hy⟩

end CFSG.Quasithin.Janko1CentralizerData
