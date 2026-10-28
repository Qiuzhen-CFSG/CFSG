module

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.Defs
public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Statements
public import Theory.SpecificGroups.AlternatingSix.M10.Contracts
public import Mathlib.GroupTheory.SpecificGroups.Quaternion

/-!
# The five-local calculation in J.2.7(5--6)

The literal images and quotient in this arithmetic helper are retained for
compatibility. This file does **not** prove J.2.7(5--6) from preceding source
clauses: `M10Witness.five_comparison` assumes (6), and
`FiveLocalData.centralizer_eq` assumes the product in (5).

Moreover, `FiveLocalData.core_le_GB` is not a valid source input. Together
with the helper's order-125 conclusion it would put a subgroup of order
125 in C_G(B), whose genuine cubic kernel and M₁₀ quotient give order
2160. The printed argument only puts the hypothetical order-45 odd
complement in a conjugate cubic centralizer. A source proof must work
with the odd complement before recognizing it as the five-core, and
must restrict that containment argument to the order-45 alternative.
The old public statements below are preserved, but their input records
must not be used as earlier J.2.1--6 witnesses.

Source: Aschbacher--Smith, printed pp.435--436 (PDF pp.446--447), J.2.7(5--6).
-/

@[expose] public section
noncomputable section
open Subgroup

namespace CFSG.Quasithin.ChapterJ.Centralizers

variable {G : Type*} [Group G] [Finite G]

namespace Choices

variable {d : LocalSetup G} (c : Choices d)

/-! ### Literal five-subgroups and the earlier J.2 inputs -/

/-- The image in `G` of a Sylow five-subgroup of the actual `H`. -/
abbrev B5Image (B5 : Sylow 5 d.toTypeRuSetup.H) : Subgroup G :=
  (B5 : Subgroup d.toTypeRuSetup.H).map d.toTypeRuSetup.H.subtype

/-- `C_Q(B₅)`, with the ambient image of `B₅` retained. -/
abbrev CQ (B5 : Sylow 5 d.toTypeRuSetup.H) : Subgroup G :=
  d.toTypeRuSetup.Q ⊓ centralizer (B5Image B5 : Set G)

/-- The centralizer in `G` of the literal ambient five-subgroup. -/
abbrev G5 (B5 : Sylow 5 d.toTypeRuSetup.H) : Subgroup G :=
  centralizer (B5Image B5 : Set G)

/-- Conjugacy is stated with both subgroups mapped into the ambient `G`. -/
def NotConjToLB (B5 : Sylow 5 d.toTypeRuSetup.H) : Prop :=
  ∀ S : Sylow 5 c.LB,
    ¬ ∃ g : G,
      (B5Image B5).map (MulAut.conj g).toMonoidHom =
        (S : Subgroup c.LB).map c.LB.subtype

/-- The earlier source clauses are inputs to this local calculation.  They are
not hidden in a stronger record and may be discharged by their chapter owners.
-/
structure EarlierJ27Inputs where
  center_order : Nat.card d.toTypeRuSetup.Z = 2
  j24 : Fusion.SourceJ24 d.toTypeRuSetup
  j25 : ∀ B : Sylow 3 d.toTypeRuSetup.L₁, Fusion.SourceJ25 d.toTypeRuSetup B
  j26 : Fusion.SourceJ26 d.toTypeRuSetup c.z

/-! ### The concrete M₁₀ quotient witness -/

/-- A source witness for the actual quotient `C_G(B)/B ≃ M₁₀`.

`no_order45` is the finite M₁₀ subgroup calculation consumed by the printed
argument.  Keeping it on the quotient witness makes the dependence explicit:
the five-core proof does not use a later triple-cover identification.
-/
structure M10Witness
    (hB : (c.B.subgroupOf c.GB).Normal) where
  quotientIso :
    let _ := hB
    (c.GB ⧸ c.B.subgroupOf c.GB) ≃* AlternatingSix.M10.extension
  no_order45 : ∀ P : Subgroup G, P ≤ c.GB → Nat.card P ≠ 45
  five_comparison : ∀ B5 : Sylow 5 d.toTypeRuSetup.H, NotConjToLB c B5

/-! ### The source-local calculation for one `B₅` -/

/-- The quaternion Sylow, the inverting involution, and the two hyperplane
centralizers used in the J.2.7(5) calculation.  Every field is a source
premise strictly before the final order and product conclusions.
-/
structure FiveLocalData (B5 : Sylow 5 d.toTypeRuSetup.H) where
  /-- `T₅ = C_Q(B₅)`, before the equality is transported to the result. -/
  T5 : Subgroup G
  T5_eq_CQ : T5 = CQ B5
  T5_quaternion : Nonempty (T5 ≃* QuaternionGroup 2)
  T5_isSylow :
    ∃ P : Sylow 2 (G5 B5),
      (P : Subgroup (G5 B5)).map (G5 B5).subtype = T5
  /-- The Brauer--Suzuki product in the literal ambient centralizer. -/
  centralizer_eq : G5 B5 = pCoreIn 5 (G5 B5) ⊔ T5
  /-- Legacy extra premise; this unconditional containment is incompatible with the source order-125 conclusion. -/
  core_le_GB : pCoreIn 5 (G5 B5) ≤ c.GB
  /-- The z-class involution used for the hyperplane factorization. -/
  i : G
  i_mem_H : i ∈ d.toTypeRuSetup.H
  i_square : i ^ 2 = 1
  i_z_class : IsConj i c.z
  i_inverts : ∀ x ∈ B5Image B5, i * x * i⁻¹ = x⁻¹
  i_noncentralizes_T5 : i ∉ centralizer (T5 : Set G)
  iz_fused_under_T5 : ∃ t : T5, (t : G) * i * (t : G)⁻¹ = c.z * i
  /-- `C_P(i)` and `C_P(iz)` have the same order. -/
  fixed_card_eq :
    Nat.card (pCoreIn 5 (G5 B5) ⊓ centralizer ({i} : Set G) : Subgroup G) =
      Nat.card (pCoreIn 5 (G5 B5) ⊓ centralizer ({c.z * i} : Set G) : Subgroup G)
  /-- The source odd-order calculation leaves exactly `1,3,5`. -/
  fixed_card_cases :
    Nat.card (pCoreIn 5 (G5 B5) ⊓ centralizer ({i} : Set G) : Subgroup G) = 1 ∨
      Nat.card (pCoreIn 5 (G5 B5) ⊓ centralizer ({i} : Set G) : Subgroup G) = 3 ∨
      Nat.card (pCoreIn 5 (G5 B5) ⊓ centralizer ({i} : Set G) : Subgroup G) = 5
  /-- Generation by the three hyperplane centralizers, after cardinal counting. -/
  core_card_formula :
    Nat.card (pCoreIn 5 (G5 B5)) =
      5 * Nat.card (pCoreIn 5 (G5 B5) ⊓ centralizer ({i} : Set G) : Subgroup G) ^ 2
  /-- Source bridge used to discharge the order-five alternative.  It says
  that if the core had the order of `B₅`, then the earlier quotient comparison
  would produce a Sylow five-subgroup of `L_B` conjugate to `B₅`. -/
  core_card_five_to_comparison :
    Nat.card (pCoreIn 5 (G5 B5)) = 5 →
      ∃ S : Sylow 5 c.LB, ∃ g : G,
        (B5Image B5).map (MulAut.conj g).toMonoidHom =
          (S : Subgroup c.LB).map c.LB.subtype

/-! ### The J.2.7(5--6) assembly -/

/-- The five-core and quaternion-centralizer conclusions for every literal
Sylow five-subgroup of `H`, together with the required nonconjugacy statement.

The hard source work is isolated in `FiveLocalData`; the proof here performs
the actual `1/3/5`, `45`, and `125` alternatives and transports the literal
quaternion and centralizer equalities.
-/
theorem five_core_conclusions
    (hB : (c.B.subgroupOf c.GB).Normal)
    (_earlier : EarlierJ27Inputs c)
    (m10 : M10Witness c hB)
    (ldata : ∀ B5 : Sylow 5 d.toTypeRuSetup.H, FiveLocalData c B5) :
    ∀ B5 : Sylow 5 d.toTypeRuSetup.H,
      G5 B5 = pCoreIn 5 (G5 B5) ⊔ CQ B5 ∧
      Nonempty (CQ B5 ≃* QuaternionGroup 2) ∧
      Nat.card (pCoreIn 5 (G5 B5)) = 125 ∧
      NotConjToLB c B5 := by
  intro B5
  let x := ldata B5
  have hcore45 : Nat.card (pCoreIn 5 (G5 B5)) ≠ 45 :=
    m10.no_order45 _ x.core_le_GB
  have hcore5 : Nat.card (pCoreIn 5 (G5 B5)) ≠ 5 := by
    intro h5
    obtain ⟨S, g, hg⟩ := x.core_card_five_to_comparison h5
    exact m10.five_comparison B5 S ⟨g, hg⟩
  have hcard : Nat.card (pCoreIn 5 (G5 B5)) = 125 := by
    rcases x.fixed_card_cases with h1 | h3 | h5
    · have hc : Nat.card (pCoreIn 5 (G5 B5)) = 5 := by
        calc
          Nat.card (pCoreIn 5 (G5 B5)) =
              5 * Nat.card (pCoreIn 5 (G5 B5) ⊓
                centralizer ({x.i} : Set G) : Subgroup G) ^ 2 := x.core_card_formula
          _ = 5 := by rw [h1]; norm_num
      exact (hcore5 hc).elim
    · have hc : Nat.card (pCoreIn 5 (G5 B5)) = 45 := by
        calc
          Nat.card (pCoreIn 5 (G5 B5)) =
              5 * Nat.card (pCoreIn 5 (G5 B5) ⊓
                centralizer ({x.i} : Set G) : Subgroup G) ^ 2 := x.core_card_formula
          _ = 45 := by rw [h3]; norm_num
      exact (hcore45 hc).elim
    · calc
        Nat.card (pCoreIn 5 (G5 B5)) =
            5 * Nat.card (pCoreIn 5 (G5 B5) ⊓
              centralizer ({x.i} : Set G) : Subgroup G) ^ 2 := x.core_card_formula
        _ = 125 := by rw [h5]; norm_num
  have hprod : G5 B5 = pCoreIn 5 (G5 B5) ⊔ CQ B5 := by
    calc
      G5 B5 = pCoreIn 5 (G5 B5) ⊔ x.T5 := x.centralizer_eq
      _ = pCoreIn 5 (G5 B5) ⊔ CQ B5 := by rw [x.T5_eq_CQ]
  have hq : Nonempty (CQ B5 ≃* QuaternionGroup 2) := by
    rw [← x.T5_eq_CQ]
    exact x.T5_quaternion
  have hnot : NotConjToLB c B5 := m10.five_comparison B5
  exact ⟨hprod, hq, hcard, hnot⟩

end Choices
end CFSG.Quasithin.ChapterJ.Centralizers
