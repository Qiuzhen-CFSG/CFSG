module
public import CFSG.Quasithin.Chapter14.Section06.SourcePrimitiveOddResidual
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallIndexSource
public import Theory.GroupTheory.NormalizedSupCard
/-!
# The cyclic residual reaches the original small-index amalgam

In the primitive solvable reduction, the two-residual is elementary of
characteristic three or five. If it is cyclic, its order equals that prime.
It complements the mapped Sylow subgroup, so the original Sylow index is
three or five as well. The original 14.2.20 local construction then gives
F.1.1 on the literal pair (J, LT).

This is the exact small-index input used to exclude the cyclic residual
in 14.6.12(2). Global recognition of the resulting amalgam belongs to the
original 14.2.20 producer; it is not inferred from its local quotient model.

Source: Aschbacher--Smith, 14.6.12(2), printed p.1031, referring to 14.3.5
and 14.2.20, printed pp.991 and 988.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

include hG hempty hM hu hmany hcard e hab

theorem source_solvable_minimal_cyclic_residual_small_index
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    (hcyc : IsCyclic (pResidual 2 (J ⧸ pCore 2 J))) :
    (T : Subgroup G).relIndex J = 3 ∨ (T : Subgroup G).relIndex J = 5 := by
  obtain ⟨p,hp,hE,_hb,hne,_hm⟩ := source_solvable_minimal_elementary_residual
    hG T hempty hM hu hmany hcard e hab J hJ hs
  let P := pResidual 2 (J ⧸ pCore 2 J)
  let S₀ := T.subtype hJ.1.1.2
  let S := S₀.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 J))
  let : IsElementaryAbelian p P := hE
  let : IsCyclic P := hcyc
  have hprime : p.Prime := by rcases hp with rfl | rfl <;> decide
  let : Fact p.Prime := ⟨hprime⟩
  have hPc : Nat.card P = p := by
    have hd : Nat.card P ∣ p := by
      rw [← IsCyclic.exponent_eq_card]
      exact IsElementaryAbelian.exponent_dvd_p p P
    exact ((Nat.dvd_prime hprime).mp hd).resolve_left
      (fun h => hne ((eq_bot_iff_card _).mpr h))
  have hi : S.index = S₀.index := (S₀ : Subgroup J).index_map_eq
    (QuotientGroup.mk'_surjective _) (by
      rw [QuotientGroup.ker_mk']; exact pCore_isPGroup.le_sylow_of_normal S₀)
  have hPS : P ⊔ (S : Subgroup (J ⧸ pCore 2 J)) = ⊤ := pResidual_sup_sylow_eq_top S
  have hd : Disjoint P (S : Subgroup (J ⧸ pCore 2 J)) :=
    IsPGroup.disjoint_of_ne p 2 (by rcases hp with rfl | rfl <;> decide)
      _ _ (IsElementaryAbelian.isPGroup p P) S.isPGroup'
  have hc := card_sup_eq_mul_of_normalizes_of_disjoint P (S : Subgroup (J ⧸ pCore 2 J))
    le_normalizer_of_normal hd
  rw [hPS,Nat.card_congr (topEquiv : (⊤ : Subgroup (J ⧸ pCore 2 J)) ≃* _).toEquiv] at hc
  have hip : S.index = p := by
    have hh := (S : Subgroup (J ⧸ pCore 2 J)).index_mul_card
    rw [hc,hPc] at hh
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := S)) hh
  have hiJ : (T : Subgroup G).relIndex J = p := hi.symm.trans hip
  exact hp.elim (fun h => Or.inl (hiJ.trans h)) (fun h => Or.inr (hiJ.trans h))

/-- The cyclic residual branch reaches the actual small-index amalgam input. -/
theorem source_solvable_minimal_cyclic_residual_amalgam
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    (hcyc : IsCyclic (pResidual 2 (J ⧸ pCore 2 J))) :
    ChapterF.Source.HypothesisF11
      ![J, sourceResidual M Mc ⊔ (T : Subgroup G)] (T : Subgroup G) :=
  (Section02.SolvableAmalgam.source_small_index_hypothesis_F_1_1
    hG T hempty hM hu hmany hcard e J hJ.1.1 hJ.1.2
    (source_solvable_minimal_cyclic_residual_small_index
      hG T hempty hM hu hmany hcard e hab J hJ hs hcyc)).1

end CFSG.Quasithin.Chapter14.Section06
