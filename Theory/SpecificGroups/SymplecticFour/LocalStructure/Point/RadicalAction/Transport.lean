module

public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Point.RadicalAction.Lattice
public import Theory.GroupTheory.SylowKernelCore

/-!
# Symplectic conjugation of the point-radical chief series

Pulling an arbitrary subgroup back by a matrix inner automorphism preserves
its core bound and relative parabolic normalization. The native binary
invariant lattice and strict chief series therefore apply to conjugate point
locals, with every subgroup embedding retained. The embedded-center identity
also relates these conjugates to their intrinsic local centers.

Source: Aschbacher--Smith 11.5.7 (!), printed pp.782--783.
-/

public noncomputable section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.PointRadicalAction
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable {n : ℕ} (hcard : Nat.card F = 2 ^ n) (hn : 1 < n)

omit [Field F] [Finite F] [CharP F 2] in
/-- An injective group map preserves the center with its actual subgroup embedding. -/
theorem map_embedded_center {H K : Type*} [Group H] [Group K]
    (B : Subgroup H) (f : H →* K) (hf : Function.Injective f) :
    ((center B).map B.subtype).map f = (center (B.map f)).map (B.map f).subtype := by
  apply le_antisymm
  · rintro _ ⟨x, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨⟨f x, mem_map_of_mem f x.property⟩, ?_, rfl⟩
    apply mem_center_iff.mpr
    rintro ⟨y, hy⟩
    obtain ⟨b, hb, rfl⟩ := hy
    apply Subtype.ext
    change f b * f x = f x * f b
    simpa only [Subgroup.coe_mul, map_mul] using congrArg (fun z : B => f z)
      (mem_center_iff.mp hx ⟨b, hb⟩)
  · rintro _ ⟨⟨x, hxB⟩, hx, rfl⟩
    obtain ⟨b, hb, rfl⟩ := hxB
    refine ⟨b, ⟨⟨b, hb⟩, ?_, rfl⟩, rfl⟩
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    apply hf
    simpa only [Subgroup.coe_mul, map_mul] using congrArg (fun z : B.map f => (z : K))
      (mem_center_iff.mp hx ⟨f y, mem_map_of_mem f y.property⟩)

include hcard hn in
/-- The exact binary invariant lattice at any symplectic conjugate point. -/
theorem invariant_lattice_conjugate (g : Sp F) (A : Subgroup (Sp F))
    (hA : A ≤ ((pointLocal (F := F)).map (MulAut.conj g).toMonoidHom).pCoreIn 2)
    (hP : pointParabolic.map (MulAut.conj g).toMonoidHom ≤ normalizer (A : Set (Sp F))) :
    A = ⊥ ∨
    A = ((center (pointLocal (F := F))).map pointLocal.subtype).map
      (MulAut.conj g).toMonoidHom ∨
    A = ((pointLocal (F := F)).map (MulAut.conj g).toMonoidHom).pCoreIn 2 := by
  let c := (MulAut.conj g).toMonoidHom
  have hm : (A.comap c).map c = A := map_comap_eq_self (by
    rw [MonoidHom.range_eq_top_of_surjective _ (MulAut.conj g).surjective]
    exact le_top)
  have hcore : ((pointLocal (F := F)).map c).pCoreIn 2 =
      ((pointLocal (F := F)).pCoreIn 2).map c :=
    (map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective).symm
  have ha : A.comap c ≤ (pointLocal (F := F)).pCoreIn 2 := by
    apply (map_le_map_iff_of_injective (f := c) (MulAut.conj g).injective).mp
    rw [hm, ← hcore]
    exact hA
  have hp : pointParabolic ≤ normalizer (A.comap c : Set (Sp F)) := by
    apply le_trans _ (A.le_normalizer_comap c)
    exact (map_le_iff_le_comap).mp hP
  rcases invariant_lattice hcard hn (A.comap c) ha hp with h | h | h
  · left
    rw [← hm, h, Subgroup.map_bot]
  · right; left
    rw [← hm, h]
  · right; right
    rw [← hm, h, ← hcore]

include hcard hn in
/-- Both factors remain nontrivial in the literal conjugate two-core. -/
theorem conjugate_chief_series (g : Sp F) :
    ⊥ < ((center (pointLocal (F := F))).map pointLocal.subtype).map
      (MulAut.conj g).toMonoidHom ∧
    ((center (pointLocal (F := F))).map pointLocal.subtype).map
      (MulAut.conj g).toMonoidHom <
      ((pointLocal (F := F)).map (MulAut.conj g).toMonoidHom).pCoreIn 2 := by
  have h := chief_series hcard hn
  constructor
  · simpa only [Subgroup.map_bot] using
      (map_lt_map_iff_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective).mpr h.1
  · rw [← map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective]
    exact (map_lt_map_iff_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective).mpr h.2

end Theory.SpecificGroups.SymplecticFour.PointRadicalAction
