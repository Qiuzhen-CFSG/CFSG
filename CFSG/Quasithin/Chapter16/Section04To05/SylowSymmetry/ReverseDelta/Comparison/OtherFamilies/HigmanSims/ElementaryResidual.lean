module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.Statements
public import Theory.SpecificGroups.SymmetricTwoResidual
public import Theory.GroupTheory.PResidual.FiniteImage
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# The two-residual in the elementary outer HS row

An extension of S₅ by E₁₆ has order 1920. Its two-residual maps onto A₅
and lies in the preimage of A₅, which has order 960. Consequently that
residual is nonsolvable and its order divides 960. These facts use the
actual normal kernel and quotient isomorphism, without assuming a splitting
or deriving a kernel-action condition from the extension shape.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
16.1.5(10), printed p.1172, as used in 16.4.11(2), printed p.1193.
-/

public section
namespace CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.OtherFamilies
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims

theorem hs_elementary_extension_card {C : Type*} [Group C] [Finite C] (h : IsHSElementaryExtension C) :
    Nat.card C = 1920 := by
  obtain ⟨Q, hQ, ⟨eQ⟩, ⟨e⟩⟩ := h
  let := hQ
  rw [card_eq_card_quotient_mul_card_subgroup Q,
    Nat.card_congr e.toEquiv, Nat.card_congr eQ.toEquiv]
  norm_num [S5, E16, C2, Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

theorem hs_elementary_residual_card_dvd {C : Type*} [Group C] [Finite C] (h : IsHSElementaryExtension C) :
    Nat.card (pResidual 2 C) ∣ 960 := by
  obtain ⟨Q, hQ, ⟨eQ⟩, ⟨e⟩⟩ := h
  let := hQ
  let f : C →* S5 := e.toMonoidHom.comp (QuotientGroup.mk' Q)
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective Q)
  have hc : Nat.card C = 1920 := by
    rw [card_eq_card_quotient_mul_card_subgroup Q,
      Nat.card_congr e.toEquiv, Nat.card_congr eQ.toEquiv]
    norm_num [S5, E16, C2, Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  let P := (alternatingGroup (Fin 5)).comap f
  have hi : P.index = 2 := by
    rw [index_comap_of_surjective _ hf, alternatingGroup.index_eq_two]
  have hP : Nat.card P = 960 := by
    have hm := P.card_mul_index
    rw [hi, hc] at hm
    omega
  rw [← hP]
  apply card_dvd_of_le
  apply (map_le_iff_le_comap).mp
  rw [map_pResidual_of_surjective 2 f hf, Equiv.Perm.twoResidual_eq_alternating]

theorem hs_elementary_residual_not_solvable {C : Type*} [Group C] [Finite C] (h : IsHSElementaryExtension C) :
    ¬ Group.IsSolvable (pResidual 2 C) := by
  obtain ⟨Q, hQ, _, ⟨e⟩⟩ := h
  let := hQ
  let f : C →* S5 := e.toMonoidHom.comp (QuotientGroup.mk' Q)
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective Q)
  have hm : (pResidual 2 C).map f = alternatingGroup (Fin 5) := by
    rw [map_pResidual_of_surjective 2 f hf, Equiv.Perm.twoResidual_eq_alternating]
  intro hs
  let := hs
  have hsA := Group.isSolvable_of_surjective (f.subgroupMap_surjective (pResidual 2 C))
  rw [hm] at hsA
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 5)) hsA

end CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.OtherFamilies
