module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticQuotient

/-!
# An actual quintic subgroup permuting with the original Sylow

The original torus of order five complements T in XT: normality of X
and the exact kernel O₂(X)=X∩T give [XT:T]=5. Both orders of the set
product are therefore the literal subgroup XT. This retains the actor
needed in the original A.3.15 application without choosing an abstract
cyclic quotient in place of it.
Source: Aschbacher--Smith 6.1.4, printed p.665.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
attribute [local instance] Representation.SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V : Subgroup G} {n : ℕ}

/-- An actual quintic torus in X permutes with T, and both set products
are exactly the original XT. -/
theorem original_hermitian_quintic_permuting_torus
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2)) :
    ∃ D : Subgroup G, Nat.card D = 5 ∧ D ≤ quinticResidual T L ∧
      (D : Set G) * (T : Set G) = ((quinticResidual T L ⊔ (T : Subgroup G) : Subgroup G) : Set G) ∧
      (T : Set G) * (D : Set G) = ((quinticResidual T L ⊔ (T : Subgroup G) : Subgroup G) : Set G) := by
  obtain ⟨D,hD,_,hDX,_,hjoin,_⟩ := original_hermitian_quintic_torus h hout hm
  obtain ⟨hc,hq⟩ := original_hermitian_quintic_core_quotient h hout hm
  let X := quinticResidual T L
  let Y := X ⊔ (T : Subgroup G)
  have hXc : Nat.card X = Nat.card (X ⊓ (T : Subgroup G) : Subgroup G) * 5 := by
    have hh := (pCore 2 X).card_mul_index
    have hk : Nat.card (pCore 2 X) = Nat.card (X ⊓ (T : Subgroup G) : Subgroup G) := by
      rw [←hc,pCoreIn,card_map_of_injective X.subtype_injective]
    rw [hk,index_eq_card,hq] at hh
    exact hh.symm
  have hYc : Nat.card Y = 5 * Nat.card T := by
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes X (T : Subgroup G)
      (sylow_normalizes_quinticResidual (h.reduced_enlargement.rankOneInput hout).sylow_normalizes)
    rw [hXc,mul_assoc] at hh
    exact (Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥(X ⊓ (T : Subgroup G)))) hh).symm
  have hDY : D ≤ Y := hDX.trans le_sup_left
  let A := D.subgroupOf Y
  let P := (T : Subgroup G).subgroupOf Y
  have hAc : Nat.card A = 5 := by rw [Nat.card_congr (subgroupOfEquivOfLe hDY).toEquiv,hD]
  have hPc : Nat.card P = Nat.card T :=
    Nat.card_congr (subgroupOfEquivOfLe (show (T : Subgroup G) ≤ Y from le_sup_right)).toEquiv
  have hd : Disjoint A P := by
    obtain ⟨k,hk⟩ := T.isPGroup'.exists_card_eq
    exact disjoint_of_coprime_natCard (by rw [hAc,hPc,hk]; exact (by decide : Nat.Coprime 5 2).pow_right k)
  have hcomp : A.IsComplement' P :=
    isComplement'_of_card_mul_and_disjoint (by rw [hAc,hPc,hYc]) hd
  have hAP : (D : Set G) * (T : Set G) = (Y : Set G) := by
    ext y
    constructor
    · rintro ⟨d,hd,t,ht,rfl⟩
      exact Y.mul_mem (hDY hd) ((show (T : Subgroup G) ≤ Y from le_sup_right) ht)
    · intro hy
      obtain ⟨⟨d,t⟩,he⟩ := hcomp.2 ⟨y,hy⟩
      exact ⟨d.val.val,d.property,t.val.val,t.property,congrArg (fun x : Y => x.val) he⟩
  have hPA : (T : Set G) * (D : Set G) = (Y : Set G) := by
    ext y
    constructor
    · rintro ⟨t,ht,d,hd,rfl⟩
      exact Y.mul_mem ((show (T : Subgroup G) ≤ Y from le_sup_right) ht) (hDY hd)
    · intro hy
      obtain ⟨⟨t,d⟩,he⟩ := hcomp.symm.2 ⟨y,hy⟩
      exact ⟨t.val.val,t.property,d.val.val,d.property,congrArg (fun x : Y => x.val) he⟩
  exact ⟨D,hD,hDX,hAP,hPA⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
