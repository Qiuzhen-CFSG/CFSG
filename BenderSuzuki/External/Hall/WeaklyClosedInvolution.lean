module

public import BenderSuzuki.External.Hall.Basic

/-!
# Element fusion in a weakly closed subgroup of order two

A weakly closed subgroup of order two fixes each of its elements under any
ambient conjugation whose image lies in the containing subgroup. No Sylow or
ambient finiteness hypothesis is necessary. This converts the subgroup
hypothesis used in ABG II.3, Proposition 1 (article pp. 21–22), into the element
hypothesis of Glauberman's Z-star theorem, cited there as [18].

The proof uses uniqueness of the nonidentity element to turn element containment
into containment of the conjugate subgroup. Weak closure then returns the element
to the original subgroup, where the same uniqueness forces it to be fixed.
-/

namespace BenderSuzuki.External

open BenderSuzuki.PFchapter1section1

private theorem eq_one_or_eq_of_card_two
    {G : Type*} [Group G] {Z : Subgroup G} (hZ : Nat.card Z = 2)
    {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1) {y : G} (hy : y ∈ Z) :
    y = 1 ∨ y = z := by
  obtain ⟨w, _, hw⟩ := (Nat.card_eq_two_iff' (1 : Z)).mp hZ
  by_cases hy1 : y = 1
  · exact Or.inl hy1
  · right
    have hy' : (⟨y, hy⟩ : Z) ≠ 1 := fun h => hy1 (congrArg Subtype.val h)
    have hz' : (⟨z, hz⟩ : Z) ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
    exact congrArg Subtype.val ((hw _ hy').trans (hw _ hz').symm)

/-- Weak closure of a subgroup of order two prevents fusion of its elements
inside the containing subgroup. -/
public theorem conj_eq_self_of_weaklyClosedIn_card_two
    {G : Type*} [Group G] {P Z : Subgroup G}
    (hZ : Nat.card Z = 2) (hweak : WeaklyClosedIn P Z)
    {z : G} (hz : z ∈ Z) (g : G) (hg : g * z * g⁻¹ ∈ P) :
    g * z * g⁻¹ = z := by
  by_cases hz1 : z = 1
  · simp [hz1]
  have hconj : rightConjugate Z g⁻¹ ≤ P := by
    intro y hy
    change y ∈ Z.map (MulAut.conj (g⁻¹)⁻¹).toMonoidHom at hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    rcases eq_one_or_eq_of_card_two hZ hz hz1 hx with rfl | rfl
    · simp
    · simpa using hg
  have hzconj : g * z * g⁻¹ ∈ rightConjugate Z g⁻¹ := by
    change g * z * g⁻¹ ∈ Z.map (MulAut.conj (g⁻¹)⁻¹).toMonoidHom
    exact Subgroup.mem_map.mpr ⟨z, hz, by simp⟩
  rw [hweak.2 _ hconj] at hzconj
  rcases eq_one_or_eq_of_card_two hZ hz hz1 hzconj with h | h
  · exfalso
    apply hz1
    have heq := congrArg (fun x => g⁻¹ * x * g) h
    simpa [mul_assoc] using heq
  · exact h

end BenderSuzuki.External
