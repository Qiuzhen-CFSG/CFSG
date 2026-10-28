module

public import Theory.AlgebraicGroup.Borel.OppositeBigCell
public import Theory.AlgebraicGroup.Tori.UnipotentIntersection

/-!
# Triangular separation in an opposite Borel big cell

The positive unipotent subgroup meets the opposite Borel trivially: the
intersection of the two Borels is the torus, and a torus has trivial
intersection with a unipotent subgroup. Consequently an opposite unipotent
element times a torus element cannot be positive unipotent unless both
factors are the identity. Conjugating this assertion gives the separation
used for uniqueness within a Bruhat cell.

Source: GLS3, Theorems 1.11.4--1.11.5, and Steinberg 6.2--6.3,
`refs/KGroup/GLS3/Chapter1.tex` and `refs/KGroup/GLS3/Chapter2St2.tex`.
-/

public section

namespace Theory.AlgebraicGroup.OppositeBorelBigCell

universe u
variable {k : Type u} [Field k] {K : Variety k} [AlgebraicGroup K]
  {T : ClosedSubgroup K} {D : RootGroupData K T} {P : Set D.Root}

theorem positive_le_borel (H : OppositeBorelBigCell T D P) :
    RootSubgroupGenerated D P ≤ H.data.B.toSubgroup := by
  rw [← H.data.positive_witness.root_generated]
  exact H.data.positive_witness.radical.1

theorem negative_le_borel (H : OppositeBorelBigCell T D P) :
    RootSubgroupGenerated D (D.neg ⁻¹' P) ≤ H.data.Bopp.toSubgroup := by
  rw [← H.data.opposite_witness.root_generated]
  exact H.data.opposite_witness.radical.1

variable [IsAlgClosed k]

theorem torus_inf_positive_eq_bot (H : OppositeBorelBigCell T D P)
    (hT : IsSubtorus T) :
    T.toSubgroup ⊓ RootSubgroupGenerated D P = ⊥ := by
  rw [← H.data.positive_witness.root_generated]
  exact subtorus_inf_unipotent_eq_bot T H.data.positive_witness.unipotent hT
    H.data.positive_witness.radical.2.1

theorem torus_inf_negative_eq_bot (H : OppositeBorelBigCell T D P)
    (hT : IsSubtorus T) :
    T.toSubgroup ⊓ RootSubgroupGenerated D (D.neg ⁻¹' P) = ⊥ := by
  rw [← H.data.opposite_witness.root_generated]
  exact subtorus_inf_unipotent_eq_bot T H.data.opposite_witness.unipotent hT
    H.data.opposite_witness.radical.2.1

/-- Opposite Borels separate the positive unipotent subgroup from the
entire negative Borel, including its torus. -/
theorem positive_inf_negativeBorel_eq_bot (H : OppositeBorelBigCell T D P)
    (hT : IsSubtorus T) :
    RootSubgroupGenerated D P ⊓ H.data.Bopp.toSubgroup = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  have hxT : x ∈ T.toSubgroup := by
    rw [← H.intersection_eq_torus]
    exact ⟨H.positive_le_borel hx.1, hx.2⟩
  have hx' : x ∈ T.toSubgroup ⊓ RootSubgroupGenerated D P := ⟨hxT, hx.1⟩
  rwa [H.torus_inf_positive_eq_bot hT] at hx'

/-- Separation of the opposite unipotent and torus factors from the
positive unipotent subgroup. -/
theorem negative_mul_torus_separation (H : OppositeBorelBigCell T D P)
    (hT : IsSubtorus T) {v t : Variety.Point K}
    (hv : v ∈ RootSubgroupGenerated D (D.neg ⁻¹' P)) (ht : t ∈ T.toSubgroup)
    (hvt : v * t ∈ RootSubgroupGenerated D P) : v = 1 ∧ t = 1 := by
  have hvteq : v * t = 1 := by
    apply Subgroup.mem_bot.mp
    rw [← H.positive_inf_negativeBorel_eq_bot hT]
    exact ⟨hvt, H.data.Bopp.mul_mem (H.negative_le_borel hv)
      (H.torus_le_negative ht)⟩
  have hvT : v ∈ T.toSubgroup := by
    have h : v = t⁻¹ := (mul_eq_one_iff_eq_inv).mp hvteq
    rw [h]
    exact T.inv_mem ht
  have hveq : v = 1 := by
    apply Subgroup.mem_bot.mp
    rw [← H.torus_inf_negative_eq_bot hT]
    exact ⟨hvT, hv⟩
  exact ⟨hveq, by simpa only [hveq, one_mul] using hvteq⟩

/-- The triangular separation for an arbitrary actual torus normalizer
element. Its right factor is detected by the opposite unipotent subgroup. -/
theorem triangular_separation (H : OppositeBorelBigCell T D P)
    (hT : IsSubtorus T) (n : T.normalizer.toSubgroup) {v t : Variety.Point K}
    (hv : (n : Variety.Point K) * v * (n : Variety.Point K)⁻¹ ∈
      RootSubgroupGenerated D (D.neg ⁻¹' P))
    (ht : t ∈ T.toSubgroup)
    (hvt : (n : Variety.Point K) * (v * t) * (n : Variety.Point K)⁻¹ ∈
      RootSubgroupGenerated D P) : v = 1 ∧ t = 1 := by
  have hnt : (n : Variety.Point K) * t * (n : Variety.Point K)⁻¹ ∈ T.toSubgroup :=
    (Subgroup.mem_normalizer_iff.mp n.property t).mp ht
  have hprod : ((n : Variety.Point K) * v * (n : Variety.Point K)⁻¹) *
      ((n : Variety.Point K) * t * (n : Variety.Point K)⁻¹) ∈
        RootSubgroupGenerated D P := by
    convert hvt using 1
    group
  obtain ⟨hvone, htone⟩ := H.negative_mul_torus_separation hT hv hnt hprod
  constructor
  · have h := congrArg (fun x => (n : Variety.Point K)⁻¹ * x * n) hvone
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right, inv_mul_cancel, mul_one] using h
  · have h := congrArg (fun x => (n : Variety.Point K)⁻¹ * x * n) htone
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right, inv_mul_cancel, mul_one] using h

end Theory.AlgebraicGroup.OppositeBorelBigCell
