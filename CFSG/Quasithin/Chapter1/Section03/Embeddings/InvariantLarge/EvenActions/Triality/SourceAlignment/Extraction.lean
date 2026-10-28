module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.Triality.SourceAlignment.Raw
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.Kernel

/-!
# Extracting the inner Cartan from the raw field–Cartan product

The raw definition of I as the inner-diagonal part of FBD first places every
inner automorphism in I. Once source field automorphisms are separated from
inner-diagonal automorphisms, F and I are disjoint. Cancellation in the actual
product FH then places the inner image of B in H. Since H preserves the marked
Sylow subgroup, B normalizes that subgroup in the carrier itself.

The model-specific separation assertion remains an explicit premise here.
These are reductions to that assertion, not a proof of its concrete triality
case. Source: Aschbacher–Smith, A.3.15(5), pp.50–51, and Proposition 1.3.4,
p.511, `refs/quasithin.pdf`.
-/

@[expose] public section
noncomputable section
open Subgroup
open scoped Pointwise
open Triality.Standard
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.Triality.SourceAlignment

variable {P : Parameters} {n : ℕ} {T B : Subgroup (Carrier P)}

/-- The raw inner-diagonal part contains the whole inner group. -/
theorem RawConfiguration.inner_le_part (h : RawConfiguration P n T B) :
    MulAut.innerSubgroup (Carrier P) ≤ h.I := by
  intro a ha
  change a ∈ (h.I : Set (MulAut (Carrier P)))
  rw [h.inner_diagonal_part]
  refine ⟨?_, inner_le_innerDiagonal P ha⟩
  have h1 : (1 : MulAut (Carrier P)) ∈
      (h.F : Set (MulAut (Carrier P))) * (innerImage B : Set (MulAut (Carrier P))) :=
    ⟨1, h.F.one_mem, 1, (innerImage B).one_mem, one_mul 1⟩
  exact ⟨1, h1, a, ha, one_mul a⟩

/-- I consists of inner-diagonal automorphisms, by its literal intersection definition. -/
theorem RawConfiguration.part_le_innerDiagonal (h : RawConfiguration P n T B) :
    h.I ≤ innerDiagonal P := by
  intro a ha
  exact (show a ∈ ((h.F : Set (MulAut (Carrier P))) *
    (innerImage B : Set (MulAut (Carrier P))) *
    (MulAut.innerSubgroup (Carrier P) : Set (MulAut (Carrier P)))) ∩
    (innerDiagonal P : Set (MulAut (Carrier P))) from h.inner_diagonal_part ▸ ha).2

/-- Source field/inner-diagonal separation implies disjointness of the raw F and I. -/
theorem RawConfiguration.field_disjoint_part (h : RawConfiguration P n T B)
    (hsep : ∀ a : MulAut (Carrier P), IsSourceFieldAutomorphism P a →
      a ∈ innerDiagonal P → a = 1) : Disjoint h.F h.I := by
  apply disjoint_iff_inf_le.mpr
  rintro a ⟨haF, haI⟩
  exact hsep a (h.field_elements a haF) (h.part_le_innerDiagonal haI)

/-- The p-subgroup's inner image lies in the source Cartan, by cancellation in FH. -/
theorem RawConfiguration.innerImage_le_cartan (h : RawConfiguration P n T B)
    (hsep : ∀ a : MulAut (Carrier P), IsSourceFieldAutomorphism P a →
      a ∈ innerDiagonal P → a = 1) : innerImage B ≤ h.H := by
  apply le_cartan_of_field_inner_disjoint (innerImage B) h.F h.H h.I
    ((map_le_range MulAut.conj B).trans h.inner_le_part) h.cartan.le_inner (h.field_disjoint_part hsep)
  intro b hb
  obtain ⟨f, hf, c, hc, he⟩ := h.subgroup_product hb
  exact ⟨f, hf, c, hc, he.symm⟩

/-- The extracted subgroup is in the inner part of the source Cartan. -/
theorem RawConfiguration.innerImage_le_inner_cartan (h : RawConfiguration P n T B)
    (hsep : ∀ a : MulAut (Carrier P), IsSourceFieldAutomorphism P a →
      a ∈ innerDiagonal P → a = 1) :
    innerImage B ≤ h.H ⊓ MulAut.innerSubgroup (Carrier P) :=
  le_inf (h.innerImage_le_cartan hsep) (map_le_range MulAut.conj B)

/-- Normalization in the carrier follows from the Cartan's actual action on T. -/
theorem RawConfiguration.normalizes (h : RawConfiguration P n T B)
    (hsep : ∀ a : MulAut (Carrier P), IsSourceFieldAutomorphism P a →
      a ∈ innerDiagonal P → a = 1) : B ≤ normalizer T := by
  intro b hb
  apply mem_normalizer_iff_map_conj_eq.mpr
  exact (mem_automorphismNormalizer T (MulAut.conj b)).mp
    (h.cartan.normalizes (h.innerImage_le_cartan hsep ⟨b, hb, rfl⟩))

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.Triality.SourceAlignment
