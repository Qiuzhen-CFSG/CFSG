module

public import Theory.GroupTheory.CoatomNormalizerIndex
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.SimpleNormal.SymplecticOvergroups.NormalizerBound.Inputs
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.SimpleNormal.SymplecticOvergroups.NormalizerBound.FieldFixedIndex
public import Theory.SpecificGroups.SymplecticFour.EvenProjective

/-!
# Reduction of the symplectic Ree normalizer upper bound

The proper ambient normalizer of the supplied socle image equals M by
relative normality and maximality. The action of M on the two parabolic
classes of its symplectic socle bounds the index once its kernel is contained
in the socle. Semilinear classification expresses an element of that kernel
as inner times field; after inner correction it centralizes the explicit
binary A₆. A trivial relative centralizer kills this correction.

This uses Malle's field-automorphism exclusion from Section 2.2 directly on
the supplied embedding. It therefore needs no conjugacy of that embedding
to the generic Sp₄ subgroup for this upper bound. The concrete A₆ centralizer
calculation and the separately owned semilinear classification remain explicit
prerequisites. This module does not yet prove
`symplecticNormalizerBound : SymplecticNormalizerBound`.

Source: G. Malle, *The maximal subgroups of ²F₄(q²)*, J. Algebra 139 (1991),
52–69, DOI 10.1016/0021-8693(91)90283-E, Sections 2.2 and 2.7.
Properness is an input here; the graph-extension and properness witnesses
are independent of this reduction.
-/

public section

namespace ReeF4.MaximalSubgroups.SimpleNormal

open Subgroup NormalizerBound Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms

/-- The genuine semilinear theorem and embedded binary centralizer calculation
suffice for the requested bound, preserving the original socle image. -/
theorem symplecticNormalizerBound_of_semilinear_of_binaryCentralizers
    (hclass : ∀ (F : Type) [Field F] [Finite F] [CharP F 2],
      ∀ a : MulAut (Sp F), PreservesDiagram a →
        ∃ (g : Sp F) (σ : F ≃+* F), a = MulAut.conj g * fieldAutomorphism σ)
    (hC : SymplecticBinaryCentralizers) : SymplecticNormalizerBound := by
  intro m hm M hM hsolv hR S hSn hSs hSa hCS F _ _ hcard e hproper
  let := hSn
  let := EvenProjective.charTwo_of_card hcard
  have hc := hC m hm M hM hsolv hR S hSn hSs hSa hCS F hcard e
  have hF : 2 < Nat.card F := by
    rw [hcard]
    exact (by decide : 2 < 2 ^ 3).trans_le
      (Nat.pow_le_pow_right (by decide) (by omega))
  have hindex : S.index ≤ 2 :=
    index_le_two_of_field_fixed_centralizer S e.symm hF binaryAlternatingEmbedding
      fieldAutomorphism_binaryAlternatingEmbedding hc (hclass F)
  rw [normalizer_map_eq_of_isCoatom_of_ne_top M hM S hproper,
    relIndex, subgroupOf, comap_map_eq_self_of_injective M.subtype_injective]
  exact hindex

end ReeF4.MaximalSubgroups.SimpleNormal
