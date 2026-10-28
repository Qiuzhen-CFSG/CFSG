module

public import CFSG.Quasithin.Chapter15.Section04.LocalIdentification.SourceData
public import Theory.GroupTheory.SimpleDisjoint
public import Theory.SpecificGroups.AlternatingSix.ElementaryAbelian
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# The alternate E₉ in the cross-commutator case

For either choice `L = X i`, set `A = X (!i)` and `I′ = ⟨A, Y j, T₀⟩`.
The sibling and cross-commutator bounds show that `I′` normalizes `L`.
Consequently the normal-factor alternative is impossible: if `A` were normal
in `I′`, then `I′` would normalize `L ⊔ A = X`, contrary to `Y j ≰ M₁`.
In the other alternative, take the actual A₆ subgroup `K ≤ I′`. Its intersection
with `L` is normal in `K`; simplicity and the orders `|K| = 360`,
`|L| = 3 · 2ⁿ` show that this intersection is trivial. Transport the explicit
A₃ × A₃ subgroup into `K` to obtain the required E₉.

Source: Aschbacher–Smith 15.4.23, printed p.1165/PDF p.1182, using the
structural alternatives 15.4.21–22 and the noncontainment 15.4.19(2).
This route uses the cross-commutator bound already available at that point
of the source proof. Thus independent images of the X-factors in X/O₂(X)
and the S₆ quotient are not additional hypotheses needed for this construction.
No rank obstruction is imported or used. The classification alternatives
remain the responsibility of the source theorem's assembly owner.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section04.Source

open Subgroup
variable {G : Type*} [Group G] {d : Geometry G}

/-- The alternate amalgam normalizes the original X-factor. -/
theorem LocalData.alternate_le_factor_normalizer (h : LocalData d) (i j : Bool)
    (hcross : ⁅d.Y j, d.X i⁆ ≤ (d.X i).pCoreIn 2) :
    d.alternateI i j ≤ normalizer (d.X i : Set G) := by
  rw [Geometry.alternateI, d.I_eq_join]
  exact sup_le (sup_le
    (le_normalizer_iff_commutator_le_right.mpr ((h.siblings_X i).trans (pCoreIn_le 2 _)))
    (le_normalizer_iff_commutator_le_right.mpr (hcross.trans (pCoreIn_le 2 _))))
    (h.X_normalized i)

/-- Under the cross bound, normality of the alternate factor would force
`Y j ≤ N_G(X)`, contradicting 15.4.19(2). This excludes the normal-factor
alternative without using any rank contradiction. -/
theorem LocalData.alternate_factor_not_normal_of_cross_commutator
    (h : LocalData d) (i j : Bool)
    (hcross : ⁅d.Y j, d.X i⁆ ≤ (d.X i).pCoreIn 2) :
    ¬ ((d.X (!i)).subgroupOf (d.alternateI i j)).Normal := by
  intro hA
  have ha : d.alternateI i j ≤ normalizer (d.X (!i) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (d.X_le_I (!i) j)).mp hA
  have hX : d.X i ⊔ d.X (!i) = d.wholeX := by
    cases i <;> simp [Geometry.wholeX, sup_comm]
  have hM : d.alternateI i j ≤ d.M₁ := by
    change _ ≤ normalizer (d.wholeX : Set G)
    rw [← hX]
    exact (le_inf (h.alternate_le_factor_normalizer i j hcross) ha).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  exact h.Y_outside j ((d.Y_le_I (!i) j).trans hM)

variable [Finite G]

private theorem five_not_dvd_card_of_twoCore_quotient_card_three (L : Subgroup G)
    (hL : Nat.card (L ⧸ pCore 2 L) = 3) : ¬ 5 ∣ Nat.card L := by
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := L)).exists_card_eq
  rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 L), hL, hn]
  intro hd
  rcases (Nat.Prime.dvd_mul (by decide : Nat.Prime 5)).mp hd with hd | hd
  · norm_num at hd
  · have := (by decide : Nat.Prime 5).dvd_of_dvd_pow hd
    norm_num at this

/-- Every actual A₆ subgroup in the alternate amalgam misses the original
X-factor. The normality used is that of the intersection inside `K`, obtained
from the action of `I′` on `X i`; cardinality alone would not suffice. -/
theorem LocalData.alternate_A6_disjoint_of_cross_commutator
    (h : LocalData d) (i j : Bool)
    (hcross : ⁅d.Y j, d.X i⁆ ≤ (d.X i).pCoreIn 2)
    (K : Subgroup G) (hKI : K ≤ d.alternateI i j)
    (e : K ≃* alternatingGroup (Fin 6)) : Disjoint (d.X i) K := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup K := e.isSimpleGroup
  apply disjoint_of_simple_of_normalizes_of_not_card_dvd K (d.X i)
    (hKI.trans (h.alternate_le_factor_normalizer i j hcross))
  intro hd
  have hc : Nat.card K = 360 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  rw [hc] at hd
  exact five_not_dvd_card_of_twoCore_quotient_card_three (d.X i) (h.X_quotient_card i)
    (dvd_trans (by decide : 5 ∣ 360) hd)

/-- Construct the E₉ inside the given A₆ subgroup, then prove its disjointness
from the original factor. No Sylow choice or rank contradiction is involved. -/
theorem LocalData.alternate_E9_of_A6_of_cross_commutator
    (h : LocalData d) (i j : Bool)
    (hcross : ⁅d.Y j, d.X i⁆ ≤ (d.X i).pCoreIn 2)
    (K : Subgroup G) (hKI : K ≤ d.alternateI i j)
    (e : K ≃* alternatingGroup (Fin 6)) :
    ∃ P : Subgroup G, IsElementaryAbelian 3 P ∧ Nat.card P = 9 ∧
      P ≤ d.alternateI i j ∧ Disjoint (d.X i) P := by
  obtain ⟨P, hP, hc⟩ := alternatingGroup.exists_elementaryAbelian_nine_of_equiv e
  let := hP
  refine ⟨P.map K.subtype, IsElementaryAbelian.map_subtype, ?_, ?_, ?_⟩
  · exact (Subgroup.card_map_of_injective K.subtype_injective).trans hc
  · exact (map_subtype_le P).trans hKI
  · exact (h.alternate_A6_disjoint_of_cross_commutator i j hcross K hKI e).mono_right
      (map_subtype_le P)

/-- A uniform construction for either X-factor. These are the only parts of
15.4.21–22 needed here: relative normality of the alternate factor, or an
actual A₆ subgroup of the alternate amalgam. The full alternatives imply
this disjunction; their classification proof is not assumed as a record. -/
theorem LocalData.alternate_E9_of_cross_commutator
    (h : LocalData d) (i j : Bool)
    (hcross : ⁅d.Y j, d.X i⁆ ≤ (d.X i).pCoreIn 2)
    (hcases : ((d.X (!i)).subgroupOf (d.alternateI i j)).Normal ∨
      ∃ K : Subgroup G, K ≤ d.alternateI i j ∧ Nonempty (K ≃* alternatingGroup (Fin 6))) :
    ∃ P : Subgroup G, IsElementaryAbelian 3 P ∧ Nat.card P = 9 ∧
      P ≤ d.alternateI i j ∧ Disjoint (d.X i) P := by
  rcases hcases with hn | ⟨K, hKI, ⟨e⟩⟩
  · exact (h.alternate_factor_not_normal_of_cross_commutator i j hcross hn).elim
  · exact h.alternate_E9_of_A6_of_cross_commutator i j hcross K hKI e

end CFSG.Quasithin.Chapter15.Section04.Source
