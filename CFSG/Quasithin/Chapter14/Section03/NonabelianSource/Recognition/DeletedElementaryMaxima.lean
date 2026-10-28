module
public import Theory.SpecificGroups.AlternatingSix.NaturalSplit.Automorphisms
public import Theory.Representation.BinaryOffender.SemidirectElementary
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six
public import CFSG.Quasithin.ChapterB.Section03.Offenders.OddParity

/-!
# Maximum elementary subgroups in the alternating deleted-module extension

A commutative subgroup of the deleted binary module extended by S₆ has order
at most the order of its permutation image times the corresponding fixed space.
An elementary subgroup of order at least 32 therefore has an offender image
unless its image is trivial. The degree-six deleted-module offender catalogue
contains only conjugates of nontrivial disjoint-transposition groups. Such a
group contains an odd permutation, so it cannot occur inside A₆.

Thus the translation subgroup is the unique elementary subgroup of order at
least 32 in the inverse image of A₆. This is the precise placement needed for
the Thompson-subgroup step of Aschbacher–Smith 14.3.20, using B.3.2(4).
-/

public section
open Subgroup SemidirectProduct BinaryPermutation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open BinaryPermutation.SixNaturalSplit

theorem deleted_no_even_offender (B : Subgroup (Equiv.Perm (Fin 6)))
    (hB : B≤alternatingGroup (Fin 6)) : ¬ IsOffender (deletedRepresentation (Fin 6)) B := by
  intro h
  exact ((ChapterB.Offenders.Six.isOffender_deleted_iff B).mp h).not_le_alternating hB

theorem deleted_elementary_kernel_card :
    Nat.card (rightHom : AutomorphismModel →* Equiv.Perm (Fin 6)).ker=32 := by
  rw [←range_inl_eq_ker_rightHom]
  rw [← Nat.card_congr (MonoidHom.ofInjective
    (f := (inl : Multiplicative (Deleted (Fin 6)) →* AutomorphismModel)) inl_injective).toEquiv]
  change Nat.card (Deleted (Fin 6))=32
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,finrank_deleted]
  decide

theorem deleted_elementary_le_kernel
    (E : Subgroup AutomorphismModel) [IsElementaryAbelian 2 E]
    (hEven : E≤(alternatingGroup (Fin 6)).comap rightHom)
    (hcard : 32≤Nat.card E) : E≤(rightHom : AutomorphismModel →* Equiv.Perm (Fin 6)).ker := by
  apply (Subgroup.map_eq_bot_iff E).mp
  by_contra hne
  have hB : E.map rightHom≤alternatingGroup (Fin 6) := (map_le_iff_le_comap).mpr hEven
  apply deleted_no_even_offender _ hB
  apply semidirect_elementary_image_offender (deletedRepresentation (Fin 6)) deletedAction
    (fun _ _ => rfl) E hne
  have hd : Nat.card (Deleted (Fin 6))=32 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,finrank_deleted]
    decide
  rwa [hd]

theorem deleted_elementary_eq_kernel
    (E : Subgroup AutomorphismModel) [IsElementaryAbelian 2 E]
    (hEven : E≤(alternatingGroup (Fin 6)).comap rightHom)
    (hcard : 32≤Nat.card E) : E=(rightHom : AutomorphismModel →* Equiv.Perm (Fin 6)).ker := by
  let : Finite (Deleted (Fin 6)) := Module.finite_of_finite (ZMod 2)
  let : Finite AutomorphismModel := Finite.of_equiv
    (Multiplicative (Deleted (Fin 6)) × Equiv.Perm (Fin 6)) SemidirectProduct.equivProd.symm
  apply eq_of_le_of_card_ge (deleted_elementary_le_kernel E hEven hcard)
  rwa [deleted_elementary_kernel_card]

theorem deleted_elementary_card_lt
    (E : Subgroup AutomorphismModel) [IsElementaryAbelian 2 E]
    (hEven : E≤(alternatingGroup (Fin 6)).comap rightHom)
    (hout : ¬E≤(rightHom : AutomorphismModel →* Equiv.Perm (Fin 6)).ker) : Nat.card E<32 :=
  lt_of_not_ge (fun h => hout (deleted_elementary_le_kernel E hEven h))

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
