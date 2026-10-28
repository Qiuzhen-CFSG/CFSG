module

public import Theory.Representation.HexacodeAction.ThreeRank
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.Sylow

/-!
# Exponent three in the concrete hexacode cover

The explicit lifts X and Y and the central scalar Z generate a subgroup
with the 27 distinct normal forms XⁱYʲZᵏ, for 0 ≤ i,j,k < 3. Right
multiplication by the generators preserves these forms, and every form
has cube one. Their coordinate identities are verified by Lean's kernel.
Since the cover has order 1080, this is a Sylow three-subgroup. Sylow
conjugacy then shows that an element with ninth power one has cube one.

The generators and their concrete monomial realization come from the
licensed ATLAS port `HexacodeNonsplit` and `HexacodeAutomorphismPackage`.
This supplies the order-27 exponent assertion in Aschbacher–Smith,
combined manuscript (1 March 2004), A.3.18, printed p.52, for the actual
triple cover used in 15.3.49(k), printed p.1144.
-/

public section

open Atlas.Codes Subgroup
namespace Theory.GroupTheory.HexacodeTheta
open Representation.Hexacode
private def evenY : HexEvenAutomorphisms := ⟨hexY, hexY_even⟩
private abbrev Indices := Fin 3 × Fin 3 × Fin 3
private def word (t : Indices) : HexEvenAutomorphisms :=
  evenX ^ t.1.val * evenY ^ t.2.1.val * hexEvenZ ^ t.2.2.val

private theorem word_X (t : Indices) :
    word t * evenX = word (t.1 + 1, t.2.1, t.2.2 + t.2.1) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Monomial.ext
  · apply Equiv.ext
    intro i
    revert t i
    decide +kernel
  · funext i
    apply LinearEquiv.ext
    intro u
    revert t i u
    decide +kernel

private theorem word_Y (t : Indices) :
    word t * evenY = word (t.1, t.2.1 + 1, t.2.2) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Monomial.ext
  · apply Equiv.ext
    intro i
    revert t i
    decide +kernel
  · funext i
    apply LinearEquiv.ext
    intro u
    revert t i u
    decide +kernel

private theorem word_Z (t : Indices) :
    word t * hexEvenZ = word (t.1, t.2.1, t.2.2 + 1) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Monomial.ext
  · apply Equiv.ext
    intro i
    revert t i
    decide +kernel
  · funext i
    apply LinearEquiv.ext
    intro u
    revert t i u
    decide +kernel

private theorem word_cube (t : Indices) : word t ^ 3 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Monomial.ext
  · apply Equiv.ext
    intro i
    revert t i
    decide +kernel
  · funext i
    apply LinearEquiv.ext
    intro u
    revert t i u
    decide +kernel

private theorem word_injective : Function.Injective word := by
  have hs : Function.Injective (fun t : Indices =>
      ((hexCoordinateSixHom (word t).val) 0,
       (hexCoordinateSixHom (word t).val) 3,
       (word t).val.val.localMap (hexPos 0) a)) := by decide +kernel
  intro t s h
  apply hs
  exact congrArg (fun g : HexEvenAutomorphisms =>
    ((hexCoordinateSixHom g.val) 0, (hexCoordinateSixHom g.val) 3,
      g.val.val.localMap (hexPos 0) a)) h

private def threeGroup : Subgroup HexEvenAutomorphisms :=
  closure {evenX, evenY, hexEvenZ}

private theorem word_mem (t : Indices) : word t ∈ threeGroup := by
  apply mul_mem
  · apply mul_mem
    · exact pow_mem (subset_closure (by simp)) _
    · exact pow_mem (subset_closure (by simp)) _
  · exact pow_mem (subset_closure (by simp)) _

private theorem word_mul_gen (t : Indices) (y : HexEvenAutomorphisms)
    (hy : y ∈ ({evenX, evenY, hexEvenZ} : Set HexEvenAutomorphisms)) :
    ∃ u, word t * y = word u := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl | rfl
  · exact ⟨_, word_X t⟩
  · exact ⟨_, word_Y t⟩
  · exact ⟨_, word_Z t⟩

private theorem gen_cube (y : HexEvenAutomorphisms)
    (hy : y ∈ ({evenX, evenY, hexEvenZ} : Set HexEvenAutomorphisms)) : y ^ 3 = 1 := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl | rfl
  · exact evenX_cube
  · simpa [word] using word_cube (0, 1, 0)
  · simpa [word] using word_cube (0, 0, 1)

private theorem threeGroup_normal_form {g : HexEvenAutomorphisms} (hg : g ∈ threeGroup) :
    ∃ t, word t = g := by
  apply closure_induction_right (p := fun x _ => ∃ t, word t = x) ?_ ?_ ?_ hg
  · exact ⟨(0, 0, 0), by simp [word]⟩
  · rintro x hx y hy ⟨t, rfl⟩
    obtain ⟨u, hu⟩ := word_mul_gen t y hy
    exact ⟨u, hu.symm⟩
  · rintro x hx y hy ⟨t, rfl⟩
    have hi : y⁻¹ = y * y := inv_eq_of_mul_eq_one_right (by
      simpa [pow_succ, mul_assoc] using gen_cube y hy)
    obtain ⟨u, hu⟩ := word_mul_gen t y hy
    obtain ⟨v, hv⟩ := word_mul_gen u y hy
    exact ⟨v, by rw [hi, ← mul_assoc, hu, hv]⟩

private theorem threeGroup_card : Nat.card threeGroup = 27 := by
  let f : Indices → threeGroup := fun t => ⟨word t, word_mem t⟩
  have hf : Function.Bijective f := by
    constructor
    · intro t u he
      exact word_injective (congrArg Subtype.val he)
    · intro g
      obtain ⟨t, ht⟩ := threeGroup_normal_form g.property
      exact ⟨t, Subtype.ext ht⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf)]
  simp [Indices]

private theorem threeGroup_cube (g : threeGroup) : g ^ 3 = 1 := by
  apply Subtype.ext
  obtain ⟨t, ht⟩ := threeGroup_normal_form g.property
  change g.val ^ 3 = 1
  rw [← ht, word_cube]

private noncomputable def threeSylow : Sylow 3 HexEvenAutomorphisms :=
  (IsPGroup.of_card (p := 3) (n := 3) threeGroup_card).toSylow (by
    have hc := threeGroup.card_mul_index
    rw [threeGroup_card, hexEven_card] at hc
    have hi : threeGroup.index = 40 := by omega
    rw [hi]
    decide)

/-- The concrete triple cover has no element of order nine. -/
theorem cube_eq_one_of_ninth {g : HexEvenAutomorphisms} (hg : g ^ 9 = 1) :
    g ^ 3 = 1 := by
  have hp : IsPGroup 3 (zpowers g) := IsPGroup.of_card_dvd_pow (n := 2) (by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hg)
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  let gP : P := ⟨g, hP (mem_zpowers g)⟩
  let e := P.equiv threeSylow
  have hc : e gP ^ 3 = 1 := threeGroup_cube (e gP)
  have he : gP ^ 3 = 1 := e.injective (by simpa only [map_pow, map_one] using hc)
  exact congrArg Subtype.val he

end Theory.GroupTheory.HexacodeTheta
