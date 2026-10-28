module

public import CFSG.Quasithin.ChapterG.Section02.Setup
public import Theory.Representation.BinaryPermutation.GroupIrreducible

/-!
# The orthogonal A₅ data and layers of G.2.4

The model identifies the actual starred image of L with A₅ and intertwines
ambient conjugation on V_L with the even-weight five-point core. This is
the orthogonal module, distinct from the natural SL₂(4)-modules occurring
in the upper section. The source denominator is V_L(U∩Uᵍ); expressions
W/S₂ denote images in S/S₂, without requiring S₂≤W.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Hypothesis G.2.1 and Lemma G.2.4, printed pp.332,334–335.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterG.Section02.AlternatingFive
open Setup
variable {G : Type*} [Group G]

def S₁ (D : Setup G) : Subgroup G := D.VL

def S₂ (D : Setup G) (g : G) : Subgroup G :=
  D.VL ⊔ (D.U ⊓ conjugate D.U g)

abbrev UpperQuotient (D : Setup G) (g : G) :=
  D.S g ⧸ (S₂ D g).subgroupOf (D.S g)

/-- The actual image, including when the denominator is not contained in A. -/
def upperImage (D : Setup G) (g : G)
    [((S₂ D g).subgroupOf (D.S g)).Normal] (A : Subgroup G) :
    Subgroup (UpperQuotient D g) :=
  (A.subgroupOf (D.S g)).map
    (QuotientGroup.mk' ((S₂ D g).subgroupOf (D.S g)))

/-- Restriction of LT→LT/O₂(LT) to L, with its actual image as codomain. -/
def starProjection (D : Setup G) : D.L →* D.star D.L :=
  ((QuotientGroup.mk' (pCore 2 D.LT)).comp
    (inclusion (show D.L ≤ D.LT from le_sup_left))).codRestrict _
    (fun l => mem_map.mpr ⟨⟨l, (show D.L ≤ D.LT from le_sup_left) l.property⟩,
      l.property, rfl⟩)

theorem starProjection_surjective (D : Setup G) : Function.Surjective (starProjection D) := by
  intro q
  obtain ⟨l, hl, he⟩ := q.property
  exact ⟨⟨l, hl⟩, Subtype.ext he⟩

theorem L_normalizes_VL (D : Setup G) : D.L ≤ normalizer (D.VL : Set G) :=
  le_normalizer_conjugateSpanBy D.V₁ D.L

/-- Exactly the additional assumptions of G.2.4, with an actual module
marking and the original conjugator. No conclusion of G.2.4 is a field. -/
structure Hypothesis [Finite G] (D : Setup G) (g : G) where
  setup : D.Hypothesis
  model : D.star D.L ≃* alternatingGroup (Fin 5)
  coordinates : D.VL ≃* Multiplicative (BinaryPermutation.core (Fin 5))
  equivariant (l : D.L) (v : D.VL) :
    coordinates ⟨(l : G) * v * (l : G)⁻¹,
      (mem_normalizer_iff.mp (L_normalizes_VL D l.property) v).mp v.property⟩ =
      Multiplicative.ofAdd (BinaryPermutation.coreRepresentation (Fin 5)
        (model (starProjection D l)).val (coordinates v).toAdd)
  point_card : Nat.card D.V₁ = 2
  seed_eq : D.V = ⁅D.VL, D.L₁⁆
  star_U_ne_bot : D.star D.U ≠ ⊥
  g_mem : g ∈ D.L
  g_not_normalizes : g ∉ D.G₁

end CFSG.Quasithin.ChapterG.Section02.AlternatingFive
