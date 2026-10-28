module

public import CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Elementary

/-!
# Applying the subgroup deductions to the canonical parabolic

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), Proposition 8.2.2, printed pp.714–715
(PDF pp.731–732).

For the actual selected pair I = join(V,V^h), this module deduces centrality
of Z_I, the relative-normalizer equality, the actor rank and strict ratio,
and C_V(A) ≤ V intersect O₂(I). The actor is exactly V^h intersect O₂(I).
The input rank uses the actual quotient map I → I/O₂(I), and h is the source
right conjugator throughout.

The input provenance is as follows. The TI property comes from Chapter 7,
and normalizer containment from E.2.9. Nontriviality of Z_I follows from
E.2.13(5) and the preceding quadratic-ratio bound. The actor-normalizer and
action-kernel equalities are E.2.13(2). The rank of V* comes from E.2.4,
E.2.14(2), and the actual quotient models. The small-rank implication is
E.2.14(7), after verifying its local quadratic-ratio hypothesis. The
centralizer bound on AB is the source application of E.2.14(3,4,10); it can
also follow from the stronger section-centralizer bound E.2.13(7).

This is not yet the complete Proposition 8.2.2. The noncontainment
V not ≤ O₂(H), including the exceptional code case, remains to be proved.
The E.2.4 family witness, Sylow restriction, core equality, concrete quotient
isomorphisms and parameter divisibility, Borel and Sylow-center markings,
cubic action, and cyclic fixed-point assertion also remain to be assembled
from the earlier source theorems. No 8.2.2 conclusion is used as a theorem
under the name of that proposition.
-/

public section
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic
open Subgroup Representation.BinaryOffender ChapterE
variable {G : Type*} [Group G]

/-- The source application of the elementary deductions, using the same h,
quotient map, embedded core and actor in every clause. The classified witness
construction must discharge the displayed E.2 premises in final assembly. -/
theorem selected_pair_conclusions [Finite G]
    (I M V : Subgroup G) [IsElementaryAbelian 2 V]
    (h : G) (hh : h ∈ I) (k : ℕ) (hk : 0 < k)
    (hgen : V ⊔ V.map (MulAut.conj h⁻¹).toMonoidHom = I)
    (hTI : ∀ x ∈ M, V ⊓ V.map (MulAut.conj x).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj x).toMonoidHom = V)
    (hNV : normalizer (V : Set G) ≤ M)
    (hZ : V ⊓ V.map (MulAut.conj h⁻¹).toMonoidHom ≠ ⊥)
    (hA : V.map (MulAut.conj h⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype =
      offenderNormalizer V h⁻¹)
    (hkernel : (V.map (MulAut.conj h⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype) ⊓
      centralizer (V : Set G) = V ⊓ V.map (MulAut.conj h⁻¹).toMonoidHom)
    (hquotient : rank ((V.subgroupOf I).map (QuotientGroup.mk' (pCore 2 I))) = k)
    (hsmall : rank (inducedAutomizer V
      (V.map (MulAut.conj h⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype)) ≤ 2 * k →
      rank (inducedAutomizer V
        (V.map (MulAut.conj h⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype)) = 2 * k)
    (hC : I ⊓ centralizer
      ((V.map (MulAut.conj h⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype) ⊔
        (V ⊓ (pCore 2 I).map I.subtype) : Subgroup G) ≤ (pCore 2 I).map I.subtype) :
    let Z := V ⊓ V.map (MulAut.conj h⁻¹).toMonoidHom
    let A := V.map (MulAut.conj h⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
    Z ≤ (center I).map I.subtype ∧
      M ⊓ I = I ⊓ normalizer (V : Set G) ∧
      rank (inducedAutomizer V A) = subgroupCorank V Z - k ∧
      actionRatio (automizerRepresentation V) (inducedAutomizer V A) < 2 ∧
      V ⊓ centralizer (A : Set G) ≤ V ⊓ (pCore 2 I).map I.subtype := by
  have hVI : V ≤ I := hgen ▸ le_sup_left
  refine ⟨intersection_central I V h hgen,
    relative_normalizer I M V h hgen hTI hNV hZ, ?_, ?_,
    fixed_le_core_intersection I V _ hVI hC⟩
  · rw [hA]
    rw [hA] at hkernel
    exact actor_rank I V h hh hVI k hA hkernel hquotient
  · rw [hA]
    rw [hA] at hkernel hsmall
    exact actor_ratio_lt_two I V h hh hVI k hk hA hkernel hquotient hsmall

end CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic
