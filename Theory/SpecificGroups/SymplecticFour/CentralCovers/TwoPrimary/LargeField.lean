module

public import Theory.SpecificGroups.SymplecticFour.CentralCovers.TwoPrimary
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.TwoPrimary.LargeField.Relations

/-!
# Compatible positive-root lifts over larger even fields

For |F| > 4, the four positive matrix root groups have additive sections
through every surjective central extension. Choose the sections equivariant
for the whole diagonal torus. The independent torus weights then kill the
five commutator defects and the remaining crossing defect.

We instantiate this construction at the literal universal projection of
Sp₄(F). Its positive-root data feed the existing unipotent-section and
transfer theorems, excluding two from the universal kernel order. The
field of order four and odd-primary exclusion are separate arguments.

Source: Aschbacher–Smith I.1.3, printed p.407, citing GLS III §6.1;
the resulting whole-component identification is used in 13.6.6, p.927.
-/

public section

open PerfectCentralCovering

namespace Theory.SpecificGroups.SymplecticFour.CentralCovers.TwoPrimary.LargeField

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The complete positive-root relations lift through every surjective
central extension of the actual symplectic matrix group when |F| > 4. -/
theorem positiveRootLifts_of_central_extension (hF : 4 < Nat.card F)
    {E : Type*} [Group E] (f : E →* Sp F) (hf : Function.Surjective f)
    (hk : f.ker ≤ Subgroup.center E) : Nonempty (PositiveRootLifts f) := by
  choose u hu ht using fun r => exists_equivariant_root_lift hF f hf hk r
  have hcomm (r s : Fin 8) (h : CommutingPair r s) (x y : F) :=
    equivariant_lifts_commute (by omega : 2 < Nat.card F) f hf hk h
      (u r) (u s) (hu r) (hu s) (ht r) (ht s) x y
  exact ⟨{
    x6 := u 6
    x0 := u 0
    x4 := u 4
    x2 := u 2
    project6 := hu 6
    project0 := hu 0
    project4 := hu 4
    project2 := hu 2
    commute60 := hcomm 6 0 (Or.inl ⟨rfl,rfl⟩)
    commute64 := hcomm 6 4 (Or.inr (Or.inl ⟨rfl,rfl⟩))
    commute04 := hcomm 0 4 (Or.inr (Or.inr (Or.inl ⟨rfl,rfl⟩)))
    commute02 := hcomm 0 2 (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,rfl⟩))))
    commute42 := hcomm 4 2 (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl,rfl⟩))))
    crossing := equivariant_crossing (by omega) f hf hk u hu ht }⟩

/-- Compatible lifts of roots 6, 0, 4 and 2 into the literal universal cover,
with all five commuting pairs and the C₂ crossing relation. -/
theorem positiveRootLifts_universal (hF : 4 < Nat.card F) :
    Nonempty (PositiveRootLifts (universalProjection (Sp F))) := by
  let : Group.IsPerfect (Sp F) := CentralRootLifts.perfect (by omega)
  exact positiveRootLifts_of_central_extension hF (universalProjection (Sp F))
    (universalProjection_surjective (Sp F)) (universalProjection_ker_le_center (Sp F))

/-- The positive-root construction discharges the local relation premise
of two-primary transfer for the universal symplectic cover. -/
theorem not_two_dvd_universal_kernel (hF : 4 < Nat.card F) :
    ¬ 2 ∣ Nat.card (universalProjection (Sp F)).ker := by
  obtain ⟨L⟩ := positiveRootLifts_universal hF
  exact not_two_dvd_universal_kernel_of_positive_root_lifts (by omega) L

end Theory.SpecificGroups.SymplecticFour.CentralCovers.TwoPrimary.LargeField

end
