module
public import Stellmacher.SectionsOneToFourDefs
public import Mathlib.GroupTheory.Commutator.Basic
/-!
# Irreducible sections force residual commutators into a normal subgroup

Let B act irreducibly on C/A, and let F be normal in the ambient group.
If F meets C outside A, then C = (F ∩ C)A. Consequently [A,K] ≤ F
forces [C,K] ≤ F, by passing to the quotient by F. A larger subgroup
E ≤ A ∩ F supplies the required element when a conjugate of E lies in C
and the intersection of A with its corresponding conjugate is smaller
than E.

Source application: Aschbacher--Smith, 14.6.9(l), printed p.1027.
The actor there is the point-centralizer I ∩ Mc, and F is the preimage
of the omega-center of the quotient two-core.
-/

public section
open Subgroup Stellmacher
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

theorem commutator_le_normal_of_irreducible_escape
    (B A C K F : Subgroup G) [F.Normal]
    (hBA : B ≤ normalizer (A : Set G)) (hBC : B ≤ normalizer (C : Set G))
    (hirr : IsIrreducibleSection B A C)
    (hsmall : ⁅A,K⁆ ≤ F) (hescape : ¬ F ⊓ C ≤ A) : ⁅C,K⁆ ≤ F := by
  let D := (F ⊓ C) ⊔ A
  have hBD : B ≤ normalizer (D : Set G) :=
    (le_inf ((le_inf le_normalizer_of_normal hBC).trans inf_normalizer_le_normalizer_inf)
      hBA).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hD : D = C := by
    rcases hirr.2.2 D le_sup_right (sup_le inf_le_right hirr.1)
      (fun b a ha => (mem_normalizer_iff.mp (hBD b.property) a).mp ha) with hh | hh
    · exact (hescape ((show F ⊓ C ≤ D from le_sup_left).trans_eq hh)).elim
    · exact hh
  let q := QuotientGroup.mk' F
  have hzero : (F ⊓ C).map q = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    simpa only [q,QuotientGroup.ker_mk'] using (show F ⊓ C ≤ F from inf_le_left)
  have hmap : C.map q = A.map q := by
    rw [←hD]
    change ((F ⊓ C) ⊔ A).map q = A.map q
    rw [Subgroup.map_sup,hzero,bot_sup_eq]
  have hcomm : ⁅C,K⁆.map q = ⊥ := by
    rw [map_commutator,hmap,←map_commutator]
    apply (Subgroup.map_eq_bot_iff _).mpr
    simpa only [q,QuotientGroup.ker_mk'] using hsmall
  simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hcomm

theorem conjugate_escapes_of_intersection_card [Finite G]
    (A E : Subgroup G) (hEA : E ≤ A) (a : G)
    (hcard : Nat.card (A ⊓ A.map (MulAut.conj a).toMonoidHom : Subgroup G) < Nat.card E) :
    ¬ E.map (MulAut.conj a).toMonoidHom ≤ A := by
  intro hle
  have hi := Subgroup.card_le_of_le (le_inf hle (map_mono hEA))
  rw [card_map_of_injective (MulAut.conj a).injective] at hi
  exact (not_le_of_gt hcard) hi

theorem commutator_le_normal_of_irreducible_conjugate [Finite G]
    (B A C K E F : Subgroup G) [F.Normal]
    (hBA : B ≤ normalizer (A : Set G)) (hBC : B ≤ normalizer (C : Set G))
    (hirr : IsIrreducibleSection B A C) (hsmall : ⁅A,K⁆ ≤ F)
    (hEA : E ≤ A) (hEF : E ≤ F) (a : G)
    (hEC : E.map (MulAut.conj a).toMonoidHom ≤ C)
    (hcard : Nat.card (A ⊓ A.map (MulAut.conj a).toMonoidHom : Subgroup G) < Nat.card E) :
    ⁅C,K⁆ ≤ F := by
  apply commutator_le_normal_of_irreducible_escape B A C K F hBA hBC hirr hsmall
  intro hh
  apply conjugate_escapes_of_intersection_card A E hEA a hcard
  apply (le_inf _ hEC).trans hh
  have hm : F.map (MulAut.conj a).toMonoidHom = F :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_of_normal (mem_top a))
  exact (map_mono hEF).trans_eq hm
end Theory.GroupTheory
