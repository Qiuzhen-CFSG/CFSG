module
public import Theory.Representation.HexacodeAction.SixDimensionalRecognition.Coordinates

/-!
# A small generating pair for the actual even hexacode cover

The displayed monomial words have orders four and three. Their product has
fifth power one, and multiplying the first by the square of the second has
third power one. Explicit checked words recover the cubic scalar and all
Schreier generators `hexLift 0 * hexLift i`. An induction on the existing
full-group generating set proves generation of the entire even cover.
These relations reduce faithful field-linear image recognition to a small
matrix-pair calculation; they are not asserted to present the abstract group.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, K.1.3,
printed p.453 (PDF p.464). The underlying monomial generators are from the
licensed ATLAS port `Theory.AtlasPort.OtherSporadic.Codes.HexacodeGenerators`,
Gerald Höhn and ATLAS contributors; see `LICENSES/ATLAS.txt`. The pair and
word certificates here are derived from those actual generators.
-/

@[expose] public section
open Atlas.Codes Subgroup
namespace Representation.Hexacode.SixDimensional.EvenImage

/-- The even lift of the coordinate permutation `(0123)(45)`. -/
def generatorA : HexEvenAutomorphisms :=
  ⟨hexLift 0 * hexLift 1 * hexLift 2 * hexLift 4, by simp⟩
/-- The even lift of the coordinate permutation `(012)(345)`. -/
def generatorB : HexEvenAutomorphisms :=
  ⟨hexLift 3 * hexLift 0 * hexLift 1 * hexLift 4, by simp⟩

theorem generatorA_four : generatorA ^ 4 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Monomial.ext
  · apply _root_.Equiv.ext; intro i; revert i; decide +kernel
  · funext i; apply LinearEquiv.ext; intro u; revert i u; decide

theorem generatorA_sq_ne_one : generatorA ^ 2 ≠ 1 := by
  intro h
  have hh := congrArg (fun g : HexEvenAutomorphisms => hexCoordinateSixHom g.val 0) h
  exact (by decide : (2 : Fin 6) ≠ 0) hh

theorem generatorB_three : generatorB ^ 3 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Monomial.ext
  · apply _root_.Equiv.ext; intro i; revert i; decide +kernel
  · funext i; apply LinearEquiv.ext; intro u; revert i u; decide

theorem generatorAB_five : (generatorA * generatorB) ^ 5 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Monomial.ext
  · apply _root_.Equiv.ext; intro i; revert i; decide +kernel
  · funext i; apply LinearEquiv.ext; intro u; revert i u; decide

theorem generatorAB2_three : (generatorA * generatorB ^ 2) ^ 3 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Monomial.ext
  · apply _root_.Equiv.ext; intro i; revert i; decide +kernel
  · funext i; apply LinearEquiv.ext; intro u; revert i u; decide

private def pairWord (l : List Bool) : HexAutomorphisms :=
  (l.map fun b => if b then generatorB.val else generatorA.val).prod

private theorem pairWord_mem (l : List Bool) :
    pairWord l ∈ closure ({generatorA.val, generatorB.val} : Set HexAutomorphisms) := by
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx
  cases b <;> exact subset_closure (by simp)

private theorem scalar_word :
    pairWord [false,false,true,false,false,true,true,false,true,
      false,false,true,false,false,true,true,false,true] = hexZ := by
  apply Subtype.ext
  apply Monomial.ext
  · apply _root_.Equiv.ext; intro i; revert i; decide +kernel
  · funext i; apply LinearEquiv.ext; intro u; revert i u; decide

private def liftWord : Fin 5 → List Bool :=
  ![[],
    [false,true,false,false,true,false,true,false,false,true,false],
    [false,true,false,false,true,true,false,false,true,false,false,true,true,false,false,true],
    [false,true,true,false,true,false,false,true,false,true],
    [true,true,false,true,false,false,true,false,true,true,false]]

private theorem lift_word (k : Fin 5) :
    pairWord (liftWord k) = hexLift 0 * hexLift k := by
  apply Subtype.ext
  apply Monomial.ext
  · apply _root_.Equiv.ext; intro i; revert k i; decide +kernel
  · funext i; apply LinearEquiv.ext; intro u; revert k i u; decide

private theorem even_le_of_schreier_generators (D : Subgroup HexAutomorphisms)
    (hD : D ≤ hexSign.ker) (hz : hexZ ∈ D)
    (hs : ∀ i : Fin 5, hexLift 0 * hexLift i ∈ D) : hexSign.ker ≤ D := by
  have hi (i : Fin 5) : (hexLift i)⁻¹ = hexLift i :=
    inv_eq_of_mul_eq_one_right (hexLift_sq i)
  have hc : hexLift 0 * hexZ = hexZ⁻¹ * hexLift 0 :=
    mul_inv_eq_iff_eq_mul.mp (hexLift_inverts 0)
  have hci : hexLift 0 * hexZ⁻¹ = hexZ * hexLift 0 := by
    have h := congrArg (fun g => g⁻¹) (hexLift_inverts 0)
    apply mul_inv_eq_iff_eq_mul.mp
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using h
  have step (i : Fin 5) (g : HexAutomorphisms)
      (hg : g ∈ D ∨ hexLift 0 * g ∈ D) :
      hexLift i * g ∈ D ∨ hexLift 0 * (hexLift i * g) ∈ D := by
    rcases hg with hg | hg
    · right
      rw [← mul_assoc]
      exact D.mul_mem (hs i) hg
    · left
      have h := D.mul_mem (D.inv_mem (hs i)) hg
      simpa only [mul_inv_rev, hi, mul_assoc, ← mul_assoc (hexLift 0) (hexLift 0),
        hexLift_sq, one_mul] using h
  have all (g : HexAutomorphisms) : g ∈ D ∨ hexLift 0 * g ∈ D := by
    have hg : g ∈ closure hexGeneratingSet := by rw [hexAutomorphisms_generated]; trivial
    induction hg using Subgroup.closure_induction_left with
    | one => exact Or.inl D.one_mem
    | mul_left x hx y hy ih =>
      rcases hx with rfl | ⟨i,rfl⟩
      · rcases ih with ih | ih
        · exact Or.inl (D.mul_mem hz ih)
        · right
          rw [← mul_assoc, hc, mul_assoc]
          exact D.mul_mem (D.inv_mem hz) ih
      · exact step i y ih
    | inv_mul_cancel x hx y hy ih =>
      rcases hx with rfl | ⟨i,rfl⟩
      · rcases ih with ih | ih
        · exact Or.inl (D.mul_mem (D.inv_mem hz) ih)
        · right
          rw [← mul_assoc, hci, mul_assoc]
          exact D.mul_mem hz ih
      · rw [hi]
        exact step i y ih
  intro g hg
  rcases all g with h | h
  · exact h
  · have hh := hD h
    change hexSign (hexLift 0 * g) = 1 at hh
    rw [map_mul, hexSign_lift, show hexSign g = 1 from hg, mul_one] at hh
    exact (by decide : (-1 : ℤˣ) ≠ 1) hh |>.elim

/-- These two actual even monomial automorphisms generate the full even cover. -/
theorem generators_closure :
    closure ({generatorA, generatorB} : Set HexEvenAutomorphisms) = ⊤ := by
  let D := closure ({generatorA.val, generatorB.val} : Set HexAutomorphisms)
  have hD : D ≤ hexSign.ker := by
    rw [closure_le]
    intro x hx
    rcases hx with rfl | rfl <;> exact Subtype.property _
  have hz : hexZ ∈ D := scalar_word ▸ pairWord_mem _
  have hs (i : Fin 5) : hexLift 0 * hexLift i ∈ D := lift_word i ▸ pairWord_mem _
  have he : D = hexSign.ker := le_antisymm hD (even_le_of_schreier_generators D hD hz hs)
  apply (Subgroup.map_injective hexSign.ker.subtype_injective)
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  simpa only [Set.image_insert_eq, Set.image_singleton, Subgroup.subtype_apply] using (show closure ({generatorA.val, generatorB.val} : Set HexAutomorphisms) = hexSign.ker from he)

end Representation.Hexacode.SixDimensional.EvenImage
