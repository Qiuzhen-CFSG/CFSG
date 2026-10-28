module

public import CFSG.Quasithin.ChapterG.Section02.Setup
public import Theory.Representation.BinaryConjugationSection
public import Theory.Representation.InvertedCubicTensor
public import Theory.GroupTheory.ConjugationLocalGeometry
public import Mathlib.FieldTheory.Finiteness

/-!
# The actual natural C₃ action in the binary G.2.3 hypothesis

The model is the alternating group on three letters acting on the
binary even-weight plane. The group equivalence is with the actual
image L* in LT/O₂(LT), and the coordinates intertwine that literal
quotient map with conjugation on V. Thus neither an abstract family tag
nor an unrelated faithful action can satisfy the natural-module input.

These data specify the n=1 source assumptions only. They contain no
S₃ quotient, generation, core-factorization or quotient-module conclusion.

Source: Aschbacher–Smith, G.2.3, printed p.333.
-/

@[expose] public section

open Subgroup

namespace CFSG.Quasithin.ChapterG.Section02.Setup
variable {G : Type*} [Group G]

/-- Restriction of the literal star quotient to L, with codomain its image. -/
def binaryLStar (D : Setup G) : D.L →* D.star D.L where
  toFun l := ⟨QuotientGroup.mk' (pCore 2 D.LT) ⟨l, (show D.L ≤ D.LT from le_sup_left) l.property⟩,
    ⟨⟨l, (show D.L ≤ D.LT from le_sup_left) l.property⟩, l.property, rfl⟩⟩
  map_one' := Subtype.ext (map_one (QuotientGroup.mk' (pCore 2 D.LT)))
  map_mul' a b := Subtype.ext
    (map_mul (QuotientGroup.mk' (pCore 2 D.LT))
      ⟨a, (show D.L ≤ D.LT from le_sup_left) a.property⟩ ⟨b, (show D.L ≤ D.LT from le_sup_left) b.property⟩)

/-- Genuine binary natural-action data, separate from Hypothesis G.2.1
and the earlier G.2.2 conclusions. The model A₃ is the cyclic derived
subgroup of the binary natural S₃ group. -/
structure BinaryNaturalData (D : Setup G) where
  quotientEquiv : D.star D.L ≃* alternatingGroup (Fin 3)
  seed_eq : D.V = D.VL
  coordinates : D.V ≃* Multiplicative (BinaryPermutation.core (Fin 3))
  equivariant (l : D.L) (v : D.V) :
    (coordinates
      (D.V.normalizerMonoidHom ⟨l, by
        rw [seed_eq]
        exact le_normalizer_conjugateSpanBy D.V₁ D.L l.property⟩ v)).toAdd =
      BinaryPermutation.coreRepresentation (Fin 3)
        (quotientEquiv (D.binaryLStar l)).val (coordinates v).toAdd
  point_card : Nat.card D.V₁ = 2
  image_nontrivial : D.star D.U ≠ ⊥


/-- The restricted star map is onto the actual image, not an abstract copy. -/
theorem binaryLStar_surjective (D : Setup G) : Function.Surjective D.binaryLStar := by
  rintro ⟨x, y, hy, rfl⟩
  exact ⟨⟨y, hy⟩, rfl⟩

/-- Cardinality of the genuine four-group from its natural coordinates. -/
theorem BinaryNaturalData.card_V {D : Setup G} (b : D.BinaryNaturalData) :
    Nat.card D.V = 4 := by
  rw [Nat.card_congr b.coordinates.toEquiv]
  change Nat.card (BinaryPermutation.core (Fin 3)) = 4
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), BinaryPermutation.finrank_core]
  norm_num [Nat.card_eq_fintype_card]

/-- The orbit-span definition makes the natural seed L-invariant. -/
theorem BinaryNaturalData.L_normalizes_V {D : Setup G} (b : D.BinaryNaturalData) :
    D.L ≤ normalizer (D.V : Set G) := by
  rw [b.seed_eq]
  exact le_normalizer_conjugateSpanBy _ _

/-- The original moving conjugator displaces the point to a disjoint line. -/
theorem BinaryNaturalData.point_disjoint {D : Setup G} (b : D.BinaryNaturalData)
    (g : G) (hg : g ∉ D.G₁) : Disjoint D.V₁ (conjugate D.V₁ g) := by
  have hc : Nat.card (conjugate D.V₁ g) = 2 := by
    rw [conjugate, card_map_of_injective (MulAut.conj g⁻¹).injective, b.point_card]
  apply disjoint_iff.mpr
  apply inf_eq_bot_of_card_two_of_ne _ _ b.point_card hc
  intro he
  have hi : g⁻¹ ∈ normalizer (D.V₁ : Set G) :=
    mem_normalizer_iff_map_conj_eq.mpr he.symm
  apply hg
  change g ∈ normalizer (D.V₁ : Set G)
  simpa only [inv_inv] using (normalizer (D.V₁ : Set G)).inv_mem hi

end CFSG.Quasithin.ChapterG.Section02.Setup
