module

public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.RadicalGeometry.FixedSpaces
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.RadicalGeometry.Centralizer
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.RadicalGeometry.SmallIndex
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.RadicalGeometry.FlagThreeActions

/-!
# Intrinsic shear geometry on the binary SL₅ exterior square

The last-column subgroup U is identified with the additive four-dimensional
parameter space. Its actual exterior displacement is q(v) ∧ u, where q identifies
V/V₆ with Γ₄. Consequently C_V(U) = [V,U] = V₆, each nonidentity shear has fixed
quotient the line of its parameter, and the individual fixed spaces span V.
Every parameter subspace of dimension at least two fixes exactly V₆.

`HasSmallIndexFixedSpaceProperty` records the fixed-space equality clause of
E.3.8 using relative subgroup index, equivalently the dimension of the literal
quotient inside an elementary abelian subgroup. The three-space image bounds
put each A₃ subgroup of the flag group in the pointwise centralizer C. Since
C/U has order two, the same equality property puts it in U; the hyperplane
obstruction then forces it to equal U. For A₂, either the subgroup lies in U,
or one of the two three-space commutators contains V₁. The small-index fixed
spaces of the A₃ subgroup generate V, as required in 12.5.7.

These are intrinsic calculations for the actual exterior action. The
identification U = R₆ and the ambient fusion arguments belong to the source
assembly.

Source: Aschbacher--Smith, 12.5.7 and 12.5.10, printed pp.820--821
(PDF pp.837--838), with Definition E.3.8, printed p.232.
-/

public section
namespace Representation.SL5ExteriorSquare
open SL5TenDimensional
open scoped IsMulCommutative

variable {A : Subgroup Group}

/-- The E.3.8 equality clause for a larger threshold implies it for a smaller one. -/
theorem HasSmallIndexFixedSpaceProperty.mono {k l : ℕ}
    (h : HasSmallIndexFixedSpaceProperty k A) (hlk : l ≤ k) :
    HasSmallIndexFixedSpaceProperty l A :=
  fun B hBA hi => h B hBA (lt_of_lt_of_le hi hlk)

/-- For every elementary subgroup, the index convention is precisely the
dimension of the actual quotient by `B.subgroupOf A`, with normality inside A. -/
theorem smallIndex_iff_elementary_quotient_fixedSpace [IsElementaryAbelian 2 A] (k : ℕ) :
    HasSmallIndexFixedSpaceProperty k A ↔
      ∀ B ≤ A, Module.finrank (ZMod 2) (Additive (A ⧸ B.subgroupOf A)) < k →
        BinaryOffender.fixedSpace (exteriorAction 2) A =
          BinaryOffender.fixedSpace (exteriorAction 2) B := by
  unfold HasSmallIndexFixedSpaceProperty
  simp only [Subgroup.log_relIndex_eq_quotient_finrank]

/-- The two pointwise centralizations place an actual parabolic subgroup in C. -/
theorem le_C_of_fixes_threeSpaces (hA : A ≤ parabolic 4)
    (h₃ : V₃ ≤ BinaryOffender.fixedSpace (exteriorAction 2) A)
    (h₃' : V₃' ≤ BinaryOffender.fixedSpace (exteriorAction 2) A) : A ≤ C := by
  intro g hg
  refine ⟨hA hg, ?_⟩
  intro v hv
  exact (sup_le h₃ h₃') hv ⟨g, hg⟩

/-- The intrinsic A₃ conclusion in 12.5.7: the nontrivial elementary subgroup
is the full shear group, without an assumed centralizer or shear containment. -/
theorem eq_shearSubgroup_of_flag_smallIndex_three [IsElementaryAbelian 2 A]
    (hA : A ≤ flagGroup) (hne : A ≠ ⊥)
    (hsmall : HasSmallIndexFixedSpaceProperty 3 A) : A = shearSubgroup := by
  obtain ⟨h₃, h₃'⟩ := fixes_threeSpaces_of_smallIndex_three hA hsmall
  have hC := le_C_of_fixes_threeSpaces
    (hA.trans (flagGroup_le_parabolic 4 (by decide))) h₃ h₃'
  exact eq_shearSubgroup_of_smallIndex_three
    (le_shearSubgroup_of_smallIndex_two hC (hsmall.mono (by decide))) hne hsmall

/-- Including both source subgroup clauses, the A₃ family in the flag group
consists precisely of U. -/
theorem flag_elementaryTwo_smallIndex_three_iff (hA : A ≤ flagGroup) :
    (BinaryOffender.IsElementaryTwo A ∧ HasSmallIndexFixedSpaceProperty 3 A) ↔
      A = shearSubgroup := by
  constructor
  · rintro ⟨⟨hne, hel⟩, hsmall⟩
    let _ := hel
    exact eq_shearSubgroup_of_flag_smallIndex_three hA hne hsmall
  · rintro rfl
    exact (elementaryTwo_smallIndex_three_iff le_rfl).mpr rfl

/-- The intrinsic alternatives used in 12.5.10: an A₂ subgroup either lies
in U or its commutator on one of the two three-spaces contains V₁. -/
theorem le_shearSubgroup_or_commutator_of_flag_smallIndex_two [IsElementaryAbelian 2 A]
    (hA : A ≤ flagGroup) (hsmall : HasSmallIndexFixedSpaceProperty 2 A) :
    A ≤ shearSubgroup ∨
      V₁ ≤ BinaryOffender.subspaceCommutator (exteriorAction 2) V₃ A ∨
      V₁ ≤ BinaryOffender.subspaceCommutator (exteriorAction 2) V₃' A := by
  by_cases h₃ : V₃ ≤ BinaryOffender.fixedSpace (exteriorAction 2) A
  · by_cases h₃' : V₃' ≤ BinaryOffender.fixedSpace (exteriorAction 2) A
    · exact Or.inl (le_shearSubgroup_of_smallIndex_two
        (le_C_of_fixes_threeSpaces
          (hA.trans (flagGroup_le_parabolic 4 (by decide))) h₃ h₃') hsmall)
    · exact Or.inr (Or.inr (V₁_le_commutator_V₃'_of_smallIndex_two hA hsmall h₃'))
  · exact Or.inr (Or.inl (V₁_le_commutator_V₃_of_smallIndex_two hA hsmall h₃))

/-- Once the two commutator-line alternatives have been excluded (by the
source fusion argument), the A₂ subgroup lies in U. -/
theorem le_shearSubgroup_of_flag_smallIndex_two [IsElementaryAbelian 2 A]
    (hA : A ≤ flagGroup) (hsmall : HasSmallIndexFixedSpaceProperty 2 A)
    (h₃ : ¬ V₁ ≤ BinaryOffender.subspaceCommutator (exteriorAction 2) V₃ A)
    (h₃' : ¬ V₁ ≤ BinaryOffender.subspaceCommutator (exteriorAction 2) V₃' A) :
    A ≤ shearSubgroup := by
  rcases le_shearSubgroup_or_commutator_of_flag_smallIndex_two hA hsmall with h | h | h
  · exact h
  · exact (h₃ h).elim
  · exact (h₃' h).elim

/-- The fixed spaces indexed by the actual nonidentity elements of U span V. -/
theorem iSup_fixedSpace_shearSubgroup :
    (⨆ (g : shearSubgroup) (_ : g ≠ 1), fixedSpace g.val) = ⊤ := by
  apply top_unique
  intro v _
  obtain ⟨u, hu, hv⟩ := exists_nonzero_shear_fixed v
  let g : shearSubgroup := ⟨shear u, shear_mem u⟩
  have hg : g ≠ 1 := by
    intro h
    have he := congrArg (fun x : shearSubgroup => (x : Group)) h
    change shear u = 1 at he
    exact hu ((shear_eq_one_iff u).mp he)
  have hle : fixedSpace (shear u) ≤
      (⨆ (g : shearSubgroup) (_ : g ≠ 1), fixedSpace g.val) :=
    le_iSup_of_le g (le_iSup_of_le hg le_rfl)
  exact hle hv

/-- The small-index fixed-space generation used after A = U in 12.5.7.
The bound is `m(A/B) ≤ 3`, in contrast to the strict inequality in A₃. -/
theorem iSup_fixedSpace_subgroups_of_flag_smallIndex_three [IsElementaryAbelian 2 A]
    (hA : A ≤ flagGroup) (hne : A ≠ ⊥)
    (hsmall : HasSmallIndexFixedSpaceProperty 3 A) :
    (⨆ (B : Subgroup Group) (_ : B ≤ A) (_ : Nat.log 2 (B.relIndex A) ≤ 3),
      BinaryOffender.fixedSpace (exteriorAction 2) B) = ⊤ := by
  have he := eq_shearSubgroup_of_flag_smallIndex_three hA hne hsmall
  subst A
  apply top_unique
  intro v _
  obtain ⟨u, hu, hv⟩ := exists_nonzero_shear_fixed v
  let B := parameterShears (Submodule.span (ZMod 2) {u})
  have hB : B ≤ shearSubgroup := parameterShears_le _
  have hc : Nat.card B = 2 := by
    rw [card_parameterShears, finrank_span_singleton hu]
    rfl
  have hi : B.relIndex shearSubgroup = 8 := by
    have hm := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup Group) B shearSubgroup bot_le hB
    rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left, hc, card_shearSubgroup] at hm
    omega
  have hlog : Nat.log 2 (B.relIndex shearSubgroup) ≤ 3 := by rw [hi]; decide
  have hvB : v ∈ BinaryOffender.fixedSpace (exteriorAction 2) B := by
    rwa [fixedSpace_parameterLine]
  have hle : BinaryOffender.fixedSpace (exteriorAction 2) B ≤
      (⨆ (D : Subgroup Group) (_ : D ≤ shearSubgroup)
        (_ : Nat.log 2 (D.relIndex shearSubgroup) ≤ 3),
        BinaryOffender.fixedSpace (exteriorAction 2) D) :=
    le_iSup_of_le B (le_iSup_of_le hB (le_iSup_of_le hlog le_rfl))
  exact hle hvB

end Representation.SL5ExteriorSquare
