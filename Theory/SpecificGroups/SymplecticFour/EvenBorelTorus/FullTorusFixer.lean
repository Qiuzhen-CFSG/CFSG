module
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.ActorReduction
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
public import Theory.GroupTheory.Hall.PointwiseFixer

/-!
# Full Borel torus fixers in even symplectic groups

A Borel-preserving automorphism of Sp4(2^n), n > 1, fixing the whole Borel
torus quotient belongs to the kernel of the torus action. That kernel
consists of inner automorphisms, so the actor preserves both diagram types.
Pointwise fixation of any actual odd Hall subgroup yields the same result
through its complement to the Borel two-core.

Source: Aschbacher--Smith, 14.2.12, printed pp.983--984.
-/

public section
open Subgroup

namespace Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.FullTorusFixer
open DiagramAutomorphisms ActorReduction
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [CharP F 2] in
theorem map_unipotent_of_map_borel {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (a : MulAut (Sp F)) (hB : (borel (F := F)).map a.toMonoidHom = borel) :
    (unipotent (F := F)).map a.toMonoidHom = unipotent := by
  rw [← borel_twoCoreIn hF, map_pCoreIn_of_injective 2 _ _ a.injective, hB]

theorem preservesDiagram_of_fixed_torus {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (a : MulAut (Sp F)) (hB : (borel (F := F)).map a.toMonoidHom = borel)
    (hfix : ∀ x : Fˣ × Fˣ, borelCharacters
      ⟨a (torusSection x).val, hB.le (mem_map_of_mem _ (torusSection x).property)⟩ = x) :
    PreservesDiagram a := by
  let aU : ActorReduction.stabilizer (F := F) := ⟨a,map_unipotent_of_map_borel hF a hB⟩
  have ht : torusAction hF aU = 1 := by
    apply MulEquiv.ext
    intro x
    rw [← characters_torusSection x, torusAction_characters]
    change borelCharacters ((borelAction aU) (torusSection x)) =
      borelCharacters (torusSection x)
    have hb : (borelAction aU) (torusSection x) =
        ⟨a (torusSection x).val, hB.le (mem_map_of_mem _ (torusSection x).property)⟩ := by
      apply Subtype.ext
      rfl
    rw [hb, characters_torusSection]
    exact hfix x
  obtain ⟨g,hg⟩ := (torusAction_eq_one_iff_inner hF hn
    SemilinearClassification.inner_field_of_preservesDiagram aU).mp ht
  change MulAut.conj g = a at hg
  rw [← hg]
  exact inner_preservesDiagram g

theorem preservesDiagram_of_pointwise_torus {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (a : MulAut (Sp F)) (hB : (borel (F := F)).map a.toMonoidHom = borel)
    (hfix : ∀ x y : Fˣ, a (diagonalTorus x y) = diagonalTorus x y) : PreservesDiagram a := by
  apply preservesDiagram_of_fixed_torus hF hn a hB
  intro x
  have he : (⟨a (torusSection x).val,
      hB.le (mem_map_of_mem _ (torusSection x).property)⟩ : borel (F := F)) = torusSection x := by
    apply Subtype.ext
    exact hfix x.1 (x.1⁻¹*x.2)
  rw [he, characters_torusSection]

theorem preservesDiagram_of_fixed_hall {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (a : MulAut (Sp F)) (hB : (borel (F := F)).map a.toMonoidHom = borel)
    (D : Subgroup (borel (F := F))) (hD : IsHallSubgroup OddHall.oddPrimes D)
    (hfix : ∀ d ∈ D, a d.val = d.val) : PreservesDiagram a := by
  let aB : MulAut (borel (F := F)) := restrict a borel hB
  have hh : ∀ d ∈ D, aB d = d := fun d hd => Subtype.ext (hfix d hd)
  have hc : Odd (pCore 2 (borel (F := F))).index := by
    rw [index_eq_card, Nat.card_congr (quotientTorusEquiv hF).toEquiv]
    exact Nat.coprime_two_left.mp (torus_odd hF)
  apply preservesDiagram_of_fixed_torus hF hn a hB
  intro x
  have h := OddHall.fixed_mod_core_of_pointwise_hall hc aB D hD hh (torusSection x)
  rw [twoCore_eq_unipotent hF, ← characters_ker, MonoidHom.mem_ker,
    map_mul, map_inv, mul_inv_eq_one] at h
  exact h.trans (characters_torusSection x)

end Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.FullTorusFixer
