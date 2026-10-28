module
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.Tactic.Abel
/-!
# The small-field quaternion obstruction

The final paragraph of the single-block branch of Theorem 2.4.7 reduces
q = 4 to an embedding of Q₈ in C₂ × D₁₆. In a dihedral group, three
elements a, b and ab with a common square have trivial common square.
The same holds after adjoining a central factor of order two, whereas
the standard quaternion generators have a nontrivial common square.
The proof uses the concrete Mathlib carriers and their multiplication.

The subgroup consumer transports the actual inclusion I ≤ Tₛ through the
specified model isomorphisms. Those centralizer model identifications are
separate source obligations. Source: Aschbacher–Smith, combined manuscript
of 1 March 2004, printed p.539.
-/

public section
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single

private theorem dihedral_common_square {n : ℕ} (a b : DihedralGroup n)
    (hab : a ^ 2 = b ^ 2) (hab' : a ^ 2 = (a * b) ^ 2) : a ^ 2 = 1 := by
  rcases a with a | a <;> rcases b with b | b
  · simp only [pow_two, DihedralGroup.r_mul_r, DihedralGroup.r.injEq] at hab hab'
    have hb : b + b = 0 := by
      apply add_left_cancel (a := a + a)
      calc
        (a + a) + (b + b) = (a + b) + (a + b) := by abel
        _ = a + a := hab'.symm
        _ = (a + a) + 0 := (add_zero _).symm
    simp only [pow_two, DihedralGroup.r_mul_r, hab, hb, DihedralGroup.r_zero]
  · simpa [pow_two] using hab
  · simp [pow_two]
  · simp [pow_two]

private theorem binary_dihedral_common_square {n : ℕ}
    (a b : Multiplicative (ZMod 2) × DihedralGroup n)
    (hab : a ^ 2 = b ^ 2) (hab' : a ^ 2 = (a * b) ^ 2) : a ^ 2 = 1 := by
  apply Prod.ext
  · exact (by decide : ∀ c : Multiplicative (ZMod 2), c ^ 2 = 1) a.1
  · exact dihedral_common_square a.2 b.2 (congrArg Prod.snd hab) (congrArg Prod.snd hab')

/-- The quaternion eight-group does not embed in a binary-dihedral product. -/
theorem no_quaternionEight_in_binary_dihedral {n : ℕ}
    (f : QuaternionGroup 2 →* Multiplicative (ZMod 2) × DihedralGroup n) :
    ¬ Function.Injective f := by
  intro hf
  have hsq : (f (QuaternionGroup.a 1)) ^ 2 = 1 := by
    apply binary_dihedral_common_square _ (f (QuaternionGroup.xa 0))
    · simp only [← map_pow]
      congr 1
    · simp only [← map_mul, ← map_pow]
      congr 1
  have he : (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 2 = 1 :=
    hf (by simpa only [map_pow, map_one] using hsq)
  exact (by decide : (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 2 ≠ 1) he

/-- The literal final q = 4 centralizer configuration on printed p.539 is impossible. -/
theorem false_of_quaternion_centralizer_in_small_field
    {G : Type*} [Group G] (I Tₛ : Subgroup G) (hIT : I ≤ Tₛ)
    (hI : Nonempty (I ≃* QuaternionGroup 2))
    (hT : Nonempty (Tₛ ≃* Multiplicative (ZMod 2) × DihedralGroup 8)) : False := by
  obtain ⟨eI⟩ := hI
  obtain ⟨eT⟩ := hT
  exact no_quaternionEight_in_binary_dihedral
    (eT.toMonoidHom.comp ((Subgroup.inclusion hIT).comp eI.symm.toMonoidHom))
    (eT.injective.comp ((Subgroup.inclusion_injective hIT).comp eI.symm.injective))
end CFSG.Quasithin.Chapter2.LinearShadows.Single
