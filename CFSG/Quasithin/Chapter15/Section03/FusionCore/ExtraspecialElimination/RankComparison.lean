module

public import Theory.Representation.BinaryOffender.Basic

/-!
# The rank squeeze in 15.3.49(h) and (n)

Cross-centralization puts `D̃_H` in the fixed space of `Vγ*`. The selected
rank inequality compares the codimension of `D̃_H` with the rank of `Uγ*`.
Together these imply the ordinary offender inequalities. If `Vγ*` is not
strong, all inequalities are equalities: `D̃_H` is its full fixed space,
`Uγ* = Vγ*`, and the rank comparison is symmetric.

The statements use actual subgroups acting on a binary representation.
They do not infer best-offender status from an ordinary rank bound. The
additional geometry establishing the book's FF-star assertion in (h), and
the use of symmetry to contradict (m), remain separate obligations.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.49(h), (n), printed pp.1143–1144.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination

open Representation.BinaryOffender

variable {K W : Type*} [Group K] [Finite K]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

private theorem rank_le_of_le {A B : Subgroup K} (hAB : A ≤ B) : rank A ≤ rank B := by
  apply Nat.log_mono_right
  exact Nat.card_le_card_of_injective
    (fun a : A => (⟨a, hAB a.property⟩ : B))
    (fun a b h => Subtype.ext (congrArg (fun x : B => (x : K)) h))

omit [Finite K] in
private theorem codim_le_of_le_fixedSpace
    (ρ : Representation (ZMod 2) K W) (D : Submodule (ZMod 2) W)
    (B : Subgroup K) (hD : D ≤ fixedSpace ρ B) :
    fixedCodim ρ B ≤ Module.finrank (ZMod 2) (W ⧸ D) := by
  have hd := D.finrank_quotient_add_finrank
  have hb := fixedCodim_add_finrank ρ B
  have hle := Submodule.finrank_mono hD
  omega

/-- The strengthened rank estimate obtained from cross-centralization,
as opposed to the ratio-at-most-two estimate in F.9.16. -/
theorem offenders_of_crossCentralization_rank
    (ρ : Representation (ZMod 2) K W) (D : Submodule (ZMod 2) W)
    (A B : Subgroup K) (hA : IsElementaryTwo A) (hB : IsElementaryTwo B)
    (hAB : A ≤ B) (hD : D ≤ fixedSpace ρ B)
    (hrank : Module.finrank (ZMod 2) (W ⧸ D) ≤ rank A) :
    IsOffender ρ A ∧ IsOffender ρ B := by
  have hDA : D ≤ fixedSpace ρ A := by
    intro v hv a
    exact hD hv ⟨a, hAB a.property⟩
  exact ⟨⟨hA, (codim_le_of_le_fixedSpace ρ D A hDA).trans hrank⟩,
    ⟨hB, (codim_le_of_le_fixedSpace ρ D B hD).trans
      (hrank.trans (rank_le_of_le hAB))⟩⟩

/-- The three equalities at the beginning of (n), derived without assuming
strong offending or any coset-geometry symmetry conclusion. -/
theorem equalities_of_not_strong
    (ρ : Representation (ZMod 2) K W) (D : Submodule (ZMod 2) W)
    (A B : Subgroup K) (hA : IsElementaryTwo A) (hB : IsElementaryTwo B)
    (hAB : A ≤ B) (hD : D ≤ fixedSpace ρ B)
    (hrank : Module.finrank (ZMod 2) (W ⧸ D) ≤ rank A)
    (hnot : ¬ IsStrongOffender ρ B) :
    D = fixedSpace ρ B ∧ A = B ∧
      rank A = Module.finrank (ZMod 2) (W ⧸ D) := by
  have hc := codim_le_of_le_fixedSpace ρ D B hD
  have hABrank := rank_le_of_le hAB
  have hge : rank B ≤ fixedCodim ρ B := by
    by_contra h
    exact hnot ⟨hB, by omega⟩
  have heqrank : rank A = rank B := by omega
  have heqcodim : fixedCodim ρ B = Module.finrank (ZMod 2) (W ⧸ D) := by omega
  have hDF : D = fixedSpace ρ B := by
    apply Submodule.eq_of_le_of_finrank_eq hD
    have hd := D.finrank_quotient_add_finrank
    have hb := fixedCodim_add_finrank ρ B
    omega
  have heq : A = B := by
    apply Subgroup.eq_of_le_of_card_ge hAB
    rw [hA.card_eq_two_pow_rank, hB.card_eq_two_pow_rank, heqrank]
  exact ⟨hDF, heq, by omega⟩

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination
