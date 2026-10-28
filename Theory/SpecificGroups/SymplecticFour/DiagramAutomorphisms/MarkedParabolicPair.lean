module
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvariantParabolicPair
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.OuterQuotient.ParabolicClasses
public import Theory.SpecificGroups.SymplecticFour.Sylow.SolvableRootOrbit
public import Theory.SpecificGroups.SymplecticFour.Sylow.SolvableOvergroupGeometry

/-!
# Invariant parabolic pairs from a marked parabolic class

An automorphism preserving one of the two parabolic conjugacy classes preserves
the diagram. A preserved solvable Sylow overgroup has characteristic Sylow,
so the two incident parabolics are individually invariant. This is the model
argument used in Aschbacher–Smith, 15.3.20.
-/

public section
open Subgroup
open scoped Pointwise
namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
private theorem conjugacyClass_fixed_of_class_preserved
    (a : MulAut (Sp F)) (P : Subgroup (Sp F)) (hP : PreservesParabolicClass a P) :
    a • subgroupConjugacyClass P = subgroupConjugacyClass P := by
  obtain ⟨g,hg⟩ := hP
  change a • P = (MulAut.conj g) • P at hg
  have hconj (b : MulAut (Sp F)) (x : Sp F) :
      b • ((MulAut.conj x) • P) = (MulAut.conj (b x)) • (b • P) := by
    rw [← mul_smul, ← mul_smul]
    congr 1
    ext y
    simp
  ext Q
  constructor
  · rintro ⟨D,⟨x,rfl⟩,rfl⟩
    refine ⟨a x * g,?_⟩
    dsimp only
    rw [hconj,hg,← mul_smul,← map_mul]
  · rintro ⟨x,rfl⟩
    refine ⟨(MulAut.conj (a.symm (x*g⁻¹))) • P,⟨a.symm (x*g⁻¹),rfl⟩,?_⟩
    dsimp only
    rw [hconj,a.apply_symm_apply,hg,← mul_smul,← map_mul,inv_mul_cancel_right]

/-- Fixing either parabolic type fixes the two-point diagram. -/
theorem preservesDiagram_of_one_parabolic_class
    (hF : 2 < Nat.card F) (a : MulAut (Sp F))
    (h : PreservesParabolicClass a pointParabolic ∨
      PreservesParabolicClass a planeParabolic) : PreservesDiagram a := by
  let X := parabolicClasses hF
  let p : X := ⟨subgroupConjugacyClass pointParabolic,Or.inl rfl⟩
  let q : X := ⟨subgroupConjugacyClass planeParabolic,Or.inr rfl⟩
  let f := parabolicClassAction hF a
  have hcover (x : X) : x = p ∨ x = q := by
    rcases x.property with hx | hx
    · exact Or.inl (Subtype.ext hx)
    · exact Or.inr (Subtype.ext hx)
  have hfix : f p = p ∨ f q = q := by
    rcases h with hp | hq
    · exact Or.inl (Subtype.ext (conjugacyClass_fixed_of_class_preserved a _ hp))
    · exact Or.inr (Subtype.ext (conjugacyClass_fixed_of_class_preserved a _ hq))
  have hboth : f p = p ∧ f q = q := by
    rcases hfix with hp | hq
    · refine ⟨hp,?_⟩
      rcases hcover (f q) with he | he
      · exact he.trans (f.injective (he.trans hp.symm)).symm
      · exact he
    · refine ⟨?_,hq⟩
      rcases hcover (f p) with he | he
      · exact he
      · exact he.trans (f.injective (he.trans hq.symm)).symm
  apply (mem_parabolicClassAction_ker_iff hF a).mp
  apply Equiv.ext
  intro x
  rcases hcover x with rfl | rfl
  · exact hboth.1
  · exact hboth.2

/-- The marked parabolic of C.2.7 supplies diagram preservation; the
actual Sylow then supplies both invariant parabolics used in 15.3.20. -/
theorem parabolic_pair_map_of_unipotent_and_marked_class {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n) (a : MulAut (Sp F))
    (hU : unipotent.map a.toMonoidHom = unipotent)
    (hP : PreservesParabolicClass a pointParabolic ∨
      PreservesParabolicClass a planeParabolic) :
    pointParabolic.map a.toMonoidHom = pointParabolic ∧
      planeParabolic.map a.toMonoidHom = planeParabolic := by
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact (show 2 ^ 1 < 2 ^ n from Nat.pow_lt_pow_right (by decide) hn)
  exact parabolic_pair_map_of_unipotent_map hF hn a
    (preservesDiagram_of_one_parabolic_class hq a hP) hU
/-- A preserved solvable Sylow overgroup has a characteristic Sylow.
Together with one marked parabolic type this fixes the whole incident pair. -/
theorem parabolic_pair_map_of_solvable_marked_overgroup {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (B : Subgroup (Sp F)) (hsol : Group.IsSolvable B) (hUB : unipotent ≤ B)
    (a : MulAut (Sp F)) (hB : B.map a.toMonoidHom = B)
    (hP : PreservesParabolicClass a pointParabolic ∨
      PreservesParabolicClass a planeParabolic) :
    pointParabolic.map a.toMonoidHom = pointParabolic ∧
      planeParabolic.map a.toMonoidHom = planeParabolic := by
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact (show 2 ^ 1 < 2 ^ n from Nat.pow_lt_pow_right (by decide) hn)
  let U := unipotentSylow hF hn.le
  have hN : B ≤ normalizer (U : Set (Sp F)) :=
    solvable_overgroups_of_orthogonal_root_orbits hF hn
      (fun D hs hu => solvable_unipotent_point_orbit_orthogonal hq D hs hu) U B hsol hUB
  let T := U.subtype hUB
  have hT : (T : Subgroup B).Normal :=
    (normal_subgroupOf_iff_le_normalizer hUB).mpr hN
  let : (T : Subgroup B).Characteristic := T.characteristic_of_normal hT
  let b : MulAut B := (a.subgroupMap B).trans (MulEquiv.subgroupCongr hB)
  have hb : (T : Subgroup B).map b.toMonoidHom = T := characteristic_iff_map_eq.mp inferInstance b
  have hmapT : (T : Subgroup B).map B.subtype = unipotent := by
    change (unipotent.subgroupOf B).map B.subtype = unipotent
    exact map_subgroupOf_eq_of_le hUB
  have hU : unipotent.map a.toMonoidHom = unipotent := by
    calc
      _ = ((T : Subgroup B).map B.subtype).map a.toMonoidHom := by
        rw [hmapT]
      _ = ((T : Subgroup B).map b.toMonoidHom).map B.subtype := by
        rw [map_map,map_map]
        rfl
      _ = unipotent := by rw [hb,hmapT]
  exact parabolic_pair_map_of_unipotent_and_marked_class hF hn a hU hP
end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
