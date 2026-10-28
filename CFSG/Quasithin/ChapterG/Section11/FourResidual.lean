module
public import Theory.SpecificGroups.SymmetricSix.NonsolvableResidual
public import Theory.Representation.NonsplitFour
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.RankOneRecognition.FieldFour

/-!
# Literal A₅ module alternatives for a nonsolvable four-space

If a faithful six-letter image omits A₆, the solvable residual is A₅.
An element of order five acts irreducibly on every faithful binary
four-space, since five divides none of the smaller general linear orders.
Thus the restriction to this exact normal residual is irreducible. The
binary A₅ recognition supplies natural or deleted coordinates, with an
actual group equivalence and linear intertwiner in each alternative.

The original HS application is in SourceAction.AlternatingFive.
Source: Aschbacher--Smith 14.3.23(2), printed p.1000, and G.9.3.
-/

public noncomputable section
open Subgroup Module Representation
open scoped MatrixGroups
local instance : Algebra (ZMod 2) (OrthogonalFourMinus.FiniteModel.Field 1) :=
  ZMod.algebra _ 2
namespace CFSG.Quasithin.ChapterG.Section11.FourResidual
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

private theorem irreducible_of_five
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (hd : finrank (ZMod 2) V = 4) (h5 : 5 ∣ Nat.card G) : IsIrreducible ρ := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' 5 h5
  let A := zpowers a
  let : Fintype A := Fintype.ofFinite A
  let : Nontrivial V := Module.nontrivial_of_finrank_pos (by omega : 0 < finrank (ZMod 2) V)
  refine ⟨fun U => ?_⟩
  have h := invariant_eq_bot_or_top_of_prime_card_dvd_sq_add_one
    5 (by decide) (by decide) (show Nat.card A = 5 by rw [Nat.card_zpowers,ha])
    (ρ.comp A.subtype) (hf.comp A.subtype_injective) hd
    (by decide) (by decide) (by decide) U.toSubmodule
    (fun b w hw => U.apply_mem_toSubmodule b.val hw)
  rcases h with h | h
  · exact .inl (Subrepresentation.toSubmodule_injective h)
  · exact .inr (Subrepresentation.toSubmodule_injective h)

/-- The original residual acts irreducibly on the four-space. -/
theorem residual_irreducible
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (hd : finrank (ZMod 2) V = 4)
    (e : solvableResidual G ≃* alternatingGroup (Fin 5)) :
    IsIrreducible (ρ.comp (solvableResidual G).subtype) := by
  apply irreducible_of_five (ρ.comp (solvableResidual G).subtype) (hf.comp (solvableResidual G).subtype_injective) hd
  rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
  norm_num [Nat.factorial]

/-- Natural or deleted coordinates on the literal normal solvable residual.
The two alternatives are representations, not carrier-family labels. -/
theorem action_alternatives
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (hd : finrank (ZMod 2) V = 4)
    (j : G →* Equiv.Perm (Fin 6)) (hj : Function.Injective j)
    (hs : ¬ Group.IsSolvable G) (ha : ¬ alternatingGroup (Fin 6) ≤ j.range) :
    (∃ e : solvableResidual G ≃* SL(2,OrthogonalFourMinus.FiniteModel.Field 1),
      Nonempty (Representation.Equiv (ρ.comp (solvableResidual G).subtype)
        (SL2.BinarySmall.natural.comp e.toMonoidHom))) ∨
    (∃ e : solvableResidual G ≃* alternatingGroup (Fin 5),
      Nonempty (Representation.Equiv (ρ.comp (solvableResidual G).subtype)
        (OrthogonalFourMinus.AlternatingFive.alternatingRepresentation.comp e.toMonoidHom))) := by
  obtain ⟨e⟩ := Theory.SpecificGroups.SymmetricSix.residual_equiv_alternatingFive j hj hs ha
  let := residual_irreducible ρ hf hd e
  have hnon : ∃ g, (ρ.comp (solvableResidual G).subtype) g ≠ 1 := by
    let : Nontrivial (solvableResidual G) := Finite.one_lt_card_iff_nontrivial.mp (by
      rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
      norm_num [Nat.factorial])
    obtain ⟨g,hg⟩ := exists_ne (1 : solvableResidual G)
    refine ⟨g,fun hh => hg ?_⟩
    apply Subtype.ext
    apply hf
    exact hh.trans ρ.map_one.symm
  exact (Section09.DefiningCharacteristic.alternating_five_irreducible_action_alternatives
    _ e hnon).2

end CFSG.Quasithin.ChapterG.Section11.FourResidual
