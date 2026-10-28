module

public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.Maximal
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.BinaryKernel.Translations
-- Internal computational dependency: reduce the existing binary translation tables
-- in the kernel certificate, without exposing their private definitions.
import all Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.BinaryKernel.Translations

/-!
# Pointwise rigidity at an M23 heptad stabilizer

Let H be the concrete heptad stabilizer, and let s be the certified involution
`m23M22GeneratorA` outside H. We prove C_M23(C_H(s)) = {1, s} by a finite
certificate in the actual degree-23 action. Twenty-four explicit words in H
centralize s. Their action reduces a commuting permutation to its values on
six orbit representatives. There are 405 possible value tuples; injectivity
and preservation of one Witt heptad leave only 1 and s. The certificate is
checked by kernel reduction, and its data can be reproduced with
`OuterRestriction/Pointwise/source/generate.py`.

An automorphism fixing H pointwise takes s into this double centralizer, hence
fixes s by injectivity. Its fixed subgroup strictly contains H, so ordinary
maximality of H makes the automorphism the identity.

This supplies the pointwise-kernel step for the M23 outer-group restriction
in GLS3, Table 5.3d, and Aschbacher--Smith, combined manuscript of 1 March
2004, printed p.510. All permutations and block tests use the existing Witt
design model; there is no assumption on automorphism coverage.
-/

open Subgroup
open scoped Pointwise
namespace Sporadic.Mathieu.M23Geometry.OuterRestriction
set_option maxRecDepth 100000

private noncomputable def outside : M23 := ⟨m23M22GeneratorA, m23M22GeneratorA_mem_M23⟩

private noncomputable def translation : heptadStabilizer :=
  ⟨⟨heptadBinaryPermutation ![1, 0, 0, 0], heptadBinaryPermutation_mem _⟩, by
    apply MulAction.mem_stabilizer_finset'.mpr
    intro x hx
    change heptadBinaryPermutation _ x ∈ omega
    rwa [heptadBinaryPermutation_fix _ x hx]⟩

private noncomputable def letter : Fin 3 → heptadStabilizer :=
  ![AlternatingSection.cycleElement.val, AlternatingSection.rotationElement.val, translation]

private def actorWord : Fin 24 → List (Fin 3) :=
  ![[],
    [0, 1, 0, 0, 1, 1, 1, 0, 1],
    [0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 2],
    [0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1],
    [0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 2],
    [0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 2, 0, 1, 0, 0, 1, 1, 1, 0, 1],
    [0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 2],
    [0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 2, 0, 1, 0, 0, 1, 1, 1, 0, 1],
    [0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 2, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1],
    [0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 2, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 2],
    [0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 2, 0, 1, 0, 0, 1, 1, 1, 0, 1],
    [0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 2, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1],
    [0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 2, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 2],
    [0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 2, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 2],
    [0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 2, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 2, 0, 1, 0, 0, 1, 1, 1, 0, 1],
    [0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 2, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1],
    [0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 2, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 2],
    [0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 2, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 2],
    [0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 2, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 2, 0, 1, 0, 0, 1, 1, 1, 0, 1],
    [0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 2, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 2, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1],
    [0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 2, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 2, 0, 1, 0, 0, 1, 1, 1, 0, 1],
    [0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 2, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 2, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 2],
    [0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 2, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 2, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 2],
    [0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 2, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 2, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 2]]

private noncomputable def actor (i : Fin 24) : heptadStabilizer :=
  ((actorWord i).map letter).prod

private def actorTable : Fin 24 → Fin 23 → Fin 23 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22],
    ![0, 17, 5, 2, 4, 3, 7, 20, 16, 19, 13, 1, 9, 22, 14, 15, 21, 11, 18, 12, 6, 8, 10],
    ![6, 17, 2, 3, 5, 4, 0, 16, 14, 9, 10, 11, 19, 13, 8, 15, 7, 1, 22, 12, 21, 20, 18],
    ![0, 11, 3, 5, 4, 2, 20, 6, 21, 12, 22, 17, 19, 10, 14, 15, 8, 1, 18, 9, 7, 16, 13],
    ![7, 11, 5, 2, 3, 4, 0, 21, 14, 19, 13, 1, 12, 22, 16, 15, 20, 17, 10, 9, 8, 6, 18],
    ![6, 1, 4, 2, 5, 3, 16, 21, 7, 12, 13, 17, 9, 18, 8, 15, 20, 11, 22, 19, 0, 14, 10],
    ![20, 1, 3, 5, 2, 4, 0, 8, 14, 12, 22, 17, 9, 10, 21, 15, 6, 11, 13, 19, 16, 7, 18],
    ![7, 17, 4, 5, 3, 2, 21, 8, 20, 9, 22, 11, 19, 18, 16, 15, 6, 1, 10, 12, 0, 14, 13],
    ![6, 11, 3, 4, 5, 2, 21, 0, 20, 19, 18, 1, 12, 10, 8, 15, 14, 17, 22, 9, 16, 7, 13],
    ![16, 11, 4, 2, 3, 5, 6, 20, 8, 12, 13, 17, 19, 18, 7, 15, 21, 1, 10, 9, 14, 0, 22],
    ![20, 11, 4, 3, 2, 5, 8, 16, 6, 19, 10, 1, 12, 18, 21, 15, 7, 17, 13, 9, 0, 14, 22],
    ![7, 1, 2, 4, 3, 5, 8, 0, 6, 12, 18, 17, 9, 13, 16, 15, 14, 11, 10, 19, 21, 20, 22],
    ![21, 1, 4, 5, 2, 3, 7, 6, 16, 9, 22, 11, 12, 18, 20, 15, 8, 17, 13, 19, 14, 0, 10],
    ![21, 17, 3, 4, 2, 5, 6, 14, 8, 19, 18, 1, 9, 10, 20, 15, 0, 11, 13, 12, 7, 16, 22],
    ![16, 1, 5, 4, 3, 2, 20, 14, 21, 9, 18, 11, 12, 22, 7, 15, 0, 17, 10, 19, 6, 8, 13],
    ![20, 17, 5, 4, 2, 3, 16, 0, 7, 9, 18, 11, 19, 22, 21, 15, 14, 1, 13, 12, 8, 6, 10],
    ![8, 17, 4, 3, 5, 2, 20, 7, 21, 19, 10, 1, 9, 18, 6, 15, 16, 11, 22, 12, 14, 0, 13],
    ![8, 11, 2, 4, 5, 3, 7, 14, 16, 12, 18, 17, 19, 13, 6, 15, 0, 1, 22, 9, 20, 21, 10],
    ![21, 11, 5, 3, 2, 4, 14, 7, 0, 12, 10, 17, 19, 22, 20, 15, 16, 1, 13, 9, 6, 8, 18],
    ![16, 17, 2, 5, 3, 4, 14, 6, 0, 19, 22, 1, 9, 13, 7, 15, 8, 11, 10, 12, 20, 21, 18],
    ![8, 1, 3, 2, 5, 4, 14, 20, 0, 9, 13, 11, 12, 10, 6, 15, 21, 17, 22, 19, 7, 16, 18],
    ![14, 1, 5, 3, 4, 2, 21, 16, 20, 12, 10, 17, 9, 22, 0, 15, 7, 11, 18, 19, 8, 6, 13],
    ![14, 11, 2, 5, 4, 3, 16, 8, 7, 19, 22, 1, 12, 13, 0, 15, 6, 17, 18, 9, 21, 20, 10],
    ![14, 17, 3, 2, 4, 5, 8, 21, 6, 9, 13, 11, 19, 10, 0, 15, 20, 1, 18, 12, 16, 7, 22]]

private theorem actor_table : ∀ i : Fin 24, ∀ x : Fin 23,
    ((actor i : M23) : Equiv.Perm (Fin 23)) x = actorTable i x := by
  decide +kernel

private theorem actor_commutes : ∀ i : Fin 24,
    (actor i : M23) * outside = outside * (actor i : M23) := by
  intro i
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change ((actor i : M23) : Equiv.Perm (Fin 23)) (m23M22GeneratorA x) =
    m23M22GeneratorA (((actor i : M23) : Equiv.Perm (Fin 23)) x)
  simp only [actor_table]
  revert i x
  decide +kernel

private def base : Fin 6 → Fin 23 := ![0, 1, 2, 9, 10, 15]
private def baseIndex : Fin 23 → Fin 6 := ![0, 1, 2, 2, 2, 2, 0, 0, 0, 3, 4, 1, 3, 4, 0, 5, 0, 1, 4, 3, 0, 0, 4]
private def actorIndex : Fin 23 → Fin 24 := ![0, 0, 0, 3, 5, 1, 2, 4, 16, 0, 0, 3, 3, 1, 21, 0, 9, 1, 8, 1, 6, 12, 3]

private theorem reconstruct_point : ∀ x : Fin 23,
    actorTable (actorIndex x) (base (baseIndex x)) = x := by decide +kernel

private def options : Fin 6 → Finset (Fin 23) :=
  ![{0, 4, 14, 15, 18}, {1, 15, 19}, {2, 13, 15}, {9, 11, 15}, {3, 10, 15}, {15}]

private theorem fixed_options : ∀ k : Fin 6, ∀ y : Fin 23,
    (∀ i : Fin 24, actorTable i (base k) = base k → actorTable i y = y) →
      y ∈ options k := by decide +kernel

private def seeds (i : Fin 5) (j k l m : Fin 3) : Fin 6 → Fin 23 :=
  ![![0, 4, 14, 15, 18] i, ![1, 15, 19] j, ![2, 13, 15] k,
    ![9, 11, 15] l, ![3, 10, 15] m, 15]

private def reconstruct (i : Fin 5) (j k l m : Fin 3) (x : Fin 23) : Fin 23 :=
  actorTable (actorIndex x) (seeds i j k l m (baseIndex x))

private theorem reconstruction_check : ∀ (i : Fin 5) (j k l m : Fin 3),
    Function.Injective (reconstruct i j k l m) →
    (∃ b : Fin 253, ∀ z ∈ m23BlockAt 1, reconstruct i j k l m z ∈ m23BlockAt b) →
    (reconstruct i j k l m = id) ∨
      (reconstruct i j k l m = m23M22GeneratorA) := by
  decide +kernel

/-- The centralizer inside M23 of the heptad elements commuting with the
chosen outside involution consists only of that involution and the identity. -/
private theorem doubleCentralizer (x : M23)
    (hx : ∀ y ∈ heptadStabilizer, y * outside = outside * y → y * x = x * y) :
    x = 1 ∨ x = outside := by
  let f : Equiv.Perm (Fin 23) := x.val
  have hc (i : Fin 24) (z : Fin 23) :
      f (actorTable i z) = actorTable i (f z) := by
    have h := congrArg (fun g : M23 => (g : Equiv.Perm (Fin 23)) z)
      (hx (actor i) (actor i).property (actor_commutes i))
    simpa only [Subgroup.coe_mul, Equiv.Perm.mul_apply, actor_table] using h.symm
  have hs (k : Fin 6) : f (base k) ∈ options k := by
    apply fixed_options k
    intro i hi
    rw [← hc, hi]
  have choose0 : ∀ y ∈ options 0, ∃ i : Fin 5, ![0, 4, 14, 15, 18] i = y := by
    decide +kernel
  have choose1 : ∀ y ∈ options 1, ∃ j : Fin 3, ![1, 15, 19] j = y := by
    decide +kernel
  have choose2 : ∀ y ∈ options 2, ∃ k : Fin 3, ![2, 13, 15] k = y := by
    decide +kernel
  have choose3 : ∀ y ∈ options 3, ∃ l : Fin 3, ![9, 11, 15] l = y := by
    decide +kernel
  have choose4 : ∀ y ∈ options 4, ∃ m : Fin 3, ![3, 10, 15] m = y := by
    decide +kernel
  obtain ⟨i, hi⟩ := choose0 _ (hs 0)
  obtain ⟨j, hj⟩ := choose1 _ (hs 1)
  obtain ⟨k, hk⟩ := choose2 _ (hs 2)
  obtain ⟨l, hl⟩ := choose3 _ (hs 3)
  obtain ⟨m, hm⟩ := choose4 _ (hs 4)
  have h15 : f 15 = 15 := by simpa [options, base] using hs 5
  have hseeds (s : Fin 6) : seeds i j k l m s = f (base s) := by
    fin_cases s
    · exact hi
    · exact hj
    · exact hk
    · exact hl
    · exact hm
    · exact h15.symm
  have hf : reconstruct i j k l m = f := by
    funext z
    rw [reconstruct, hseeds, ← hc, reconstruct_point]
  have hb : (m23BlockAt 1).image f ∈ m23Blocks := by
    have hb1 : m23BlockAt 1 ∈ m23Blocks :=
      Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
    exact smul_heptad x hb1
  obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hb
  have hb' : ∃ b : Fin 253, ∀ z ∈ m23BlockAt 1, f z ∈ m23BlockAt b := by
    refine ⟨b, ?_⟩
    intro z hz
    rw [hb]
    exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
  have hd := reconstruction_check i j k l m (hf.symm ▸ f.injective) (hf.symm ▸ hb')
  rcases hd with h | h
  · left
    apply Subtype.ext
    apply Equiv.ext
    intro z
    exact congrFun (hf.symm.trans h) z
  · right
    apply Subtype.ext
    apply Equiv.ext
    intro z
    exact congrFun (hf.symm.trans h) z

/-- An automorphism of the actual M23 fixing its heptad stabilizer pointwise
is the identity. -/
public theorem aut_eq_one_of_heptad_fixed
    (a : MulAut M23) (hfix : ∀ x ∈ heptadStabilizer, a x = x) : a = 1 := by
  have hne : outside ≠ 1 := by decide +kernel
  have hnmem : outside ∉ heptadStabilizer := by decide +kernel
  have hs : a outside = outside := by
    have hd := doubleCentralizer (a outside) (by
      intro y hy hc
      simpa only [map_mul, hfix y hy] using congrArg a hc)
    rcases hd with h | h
    · exact False.elim (hne (a.injective (h.trans (map_one a).symm)))
    · exact h
  let K := a.toMonoidHom.eqLocus (MonoidHom.id M23)
  have hle : heptadStabilizer ≤ K := hfix
  have hlt : heptadStabilizer < K := lt_of_le_of_ne hle (by
    intro h
    have hsK : outside ∈ K := hs
    exact hnmem (h.symm ▸ hsK))
  have htop : K = ⊤ := heptadStabilizer_isCoatom.lt_iff.mp hlt
  apply MulEquiv.ext
  intro x
  exact (show x ∈ K from htop.symm ▸ mem_top x)

end Sporadic.Mathieu.M23Geometry.OuterRestriction
