module

public import Theory.SpecificGroups.SL3.SplitMonomial
public import Theory.SpecificGroups.SL3.SplitMonomial.LocalCore.KernelCalculation
public import Theory.SpecificGroups.SL3.SplitMonomial.LocalCore.LinearFour
public import Theory.SpecificGroups.SL3.SplitMonomial.LocalCore.ProjectiveFour

/-!
# Three-cores inside the split monomial subgroups

The common group-theoretic calculation applies to the published stabilizer
of punctured coordinate axes and its actual central-quotient image. It
uses the normal diagonal sign subgroup of order four with abelian
centralizer inside the monomial subgroup. This subgroup descends through
the actual central quotient with its order and centralizer property
preserved. The full ambient Sylow hypothesis puts the four-subgroup
inside H. Conjugation on its three nonidentity elements has abelian
kernel, and the nonabelian three-subgroup forces an image of order three
or six. The product order then gives |O₃(H)| = 9.

The final linear and projective theorems discharge both normal-four
witnesses. Their field parameters match the split prime-field branch;
the core calculation itself uses only that the field has odd order.
The core is intrinsic to H, not the ambient linear or projective group.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, printed
p.511 (PDF p.528), and GLS3, Theorem 6.5.3(b),
`refs/KGroup/GLS3/chapter6.tex`.
-/

public section

open Subgroup

namespace Matrix.SL3.SplitMonomial

variable (F : Type*) [Field F] [Finite F]

/-- A normal four-subgroup with abelian relative centralizer supplies the
linear monomial core calculation. -/
theorem linear_core_card_nine_of_normal_four
    (hfour : ∃ V : Subgroup (linear F), V.Normal ∧ Nat.card V = 4 ∧
      IsMulCommutative (centralizer (V : Set (linear F))))
    (T : Sylow 2 (SpecialLinearGroup (Fin 3) F))
    (H : Subgroup (SpecialLinearGroup (Fin 3) F))
    (hTH : (T : Subgroup _) ≤ H) (hHM : H ≤ linear F)
    (hU : ∃ U : Subgroup (SpecialLinearGroup (Fin 3) F),
      U ≤ H ∧ IsPGroup 3 U ∧ ¬ IsMulCommutative U)
    (hcard : Nat.card H = 27 * Nat.card T) : Nat.card (pCore 3 H) = 9 := by
  obtain ⟨V, hVnormal, hVcard, hVcentralizer⟩ := hfour
  let := hVnormal
  exact LocalCore.card_core_of_normal_four (linear F) V hVcard hVcentralizer
    T H hTH hHM hU hcard

/-- A normal four-subgroup with abelian relative centralizer supplies the
projective monomial core calculation in the actual quotient model. -/
theorem projective_core_card_nine_of_normal_four
    (hfour : ∃ V : Subgroup (projective F), V.Normal ∧ Nat.card V = 4 ∧
      IsMulCommutative (centralizer (V : Set (projective F))))
    (T : Sylow 2 (ProjectiveSpecialLinearGroup (Fin 3) F))
    (H : Subgroup (ProjectiveSpecialLinearGroup (Fin 3) F))
    (hTH : (T : Subgroup _) ≤ H) (hHM : H ≤ projective F)
    (hU : ∃ U : Subgroup (ProjectiveSpecialLinearGroup (Fin 3) F),
      U ≤ H ∧ IsPGroup 3 U ∧ ¬ IsMulCommutative U)
    (hcard : Nat.card H = 27 * Nat.card T) : Nat.card (pCore 3 H) = 9 := by
  obtain ⟨V, hVnormal, hVcard, hVcentralizer⟩ := hfour
  let := hVnormal
  exact LocalCore.card_core_of_normal_four (projective F) V hVcard hVcentralizer
    T H hTH hHM hU hcard

/-- A subgroup of split monomial SL₃ containing a full ambient Sylow
two-subgroup and a nonabelian three-subgroup has three-core of order nine
when its order is twenty-seven times the Sylow two-order. -/
theorem linear_core_card_nine
    {p : ℕ} (hF : Nat.card F = p) (_hp : p.Prime) (hodd : Odd p)
    (_hlarge : 3 < p) (_hmod : p % 3 = 1)
    (T : Sylow 2 (SpecialLinearGroup (Fin 3) F))
    (H : Subgroup (SpecialLinearGroup (Fin 3) F))
    (hTH : (T : Subgroup _) ≤ H) (hHM : H ≤ linear F)
    (hU : ∃ U : Subgroup (SpecialLinearGroup (Fin 3) F),
      U ≤ H ∧ IsPGroup 3 U ∧ ¬ IsMulCommutative U)
    (hcard : Nat.card H = 27 * Nat.card T) : Nat.card (pCore 3 H) = 9 := by
  exact linear_core_card_nine_of_normal_four F
    (linear_normal_four F (hF.symm ▸ hodd)) T H hTH hHM hU hcard

/-- The corresponding three-core calculation inside the actual central
quotient image of the split monomial subgroup of SL₃. -/
theorem projective_core_card_nine
    {p : ℕ} (hF : Nat.card F = p) (_hp : p.Prime) (hodd : Odd p)
    (_hlarge : 3 < p) (_hmod : p % 3 = 1)
    (T : Sylow 2 (ProjectiveSpecialLinearGroup (Fin 3) F))
    (H : Subgroup (ProjectiveSpecialLinearGroup (Fin 3) F))
    (hTH : (T : Subgroup _) ≤ H) (hHM : H ≤ projective F)
    (hU : ∃ U : Subgroup (ProjectiveSpecialLinearGroup (Fin 3) F),
      U ≤ H ∧ IsPGroup 3 U ∧ ¬ IsMulCommutative U)
    (hcard : Nat.card H = 27 * Nat.card T) : Nat.card (pCore 3 H) = 9 := by
  exact projective_core_card_nine_of_normal_four F
    (projective_normal_four_of_linear F (linear_normal_four F (hF.symm ▸ hodd)))
    T H hTH hHM hU hcard

end Matrix.SL3.SplitMonomial
