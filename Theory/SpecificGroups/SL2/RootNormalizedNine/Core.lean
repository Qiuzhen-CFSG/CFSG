module

public import Theory.SpecificGroups.SL2.RootNormalizedNine.Triangular
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Mathlib.Data.ZMod.Basic

/-!
# Core and cube placement in two rank-one factors

The upper root group is an actual Sylow two-subgroup. A two-subgroup
normalized by it lies inside it, by Sylow maximality of their product.
Applying this to both coordinate images places the embedded two-core of
any root-normalized subgroup C in the root product. An actual E₉ quotient
then puts every cube in that product, and the matrix calculation in
`Triangular` places C in the product Borel.

Source application: Aschbacher–Smith, `refs/quasithin.pdf`, printed p.1164,
proof of 15.4.20, ordinary even-field component case.
-/

open Matrix
open scoped MatrixGroups commutatorElement
namespace Matrix.SpecialLinearGroup.RootNormalizedNine
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
local notation "E" => SL(2, F) × SL(2, F)
local notation "S" => Subgroup.prod (upperUnipotent F) (upperUnipotent F)
local notation "B" => Subgroup.prod (rankOneBorel F) (rankOneBorel F)

public theorem core_le_root (C : Subgroup E) (hn : S ≤ Subgroup.normalizer (C : Set E)) :
    C.pCoreIn 2 ≤ S := by
  have hN : S ≤ Subgroup.normalizer (C.pCoreIn 2 : Set E) :=
    hn.trans (Subgroup.normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  have hproj (f : E →* SL(2, F)) (hf : upperUnipotent F ≤ (S).map f) :
      (C.pCoreIn 2).map f ≤ upperUnipotent F := by
    have hnorm : upperUnipotent F ≤ Subgroup.normalizer ((C.pCoreIn 2).map f : Set _) :=
      hf.trans ((Subgroup.map_mono hN).trans (Subgroup.le_normalizer_map f))
    have hP := (Subgroup.isPGroup_pCoreIn 2 C).map f
    exact sup_eq_left.mp ((upperUnipotentSylow F 2).is_maximal'
      ((upperUnipotentSylow F 2).isPGroup'.to_sup_of_normal_right' hP hnorm) le_sup_left)
  apply Subgroup.le_prod_iff.mpr
  constructor
  · apply hproj (MonoidHom.fst _ _)
    intro a ha
    exact ⟨(a, 1), ⟨ha, (upperUnipotent F).one_mem⟩, rfl⟩
  · apply hproj (MonoidHom.snd _ _)
    intro a ha
    exact ⟨(1, a), ⟨(upperUnipotent F).one_mem, ha⟩, rfl⟩

public theorem nine_cube (x : Multiplicative (ZMod 3 × ZMod 3)) : x ^ 3 = 1 := by
  apply Multiplicative.toAdd.injective
  simp only [toAdd_pow, toAdd_one]
  have h3 : (3 : ZMod 3) = 0 := rfl
  ext <;> simp [nsmul_eq_mul, h3]

omit [Finite F] [CharP F 2] in
public theorem cubes_mem_core (C : Subgroup E)
    (e : (C ⧸ pCore 2 C) ≃* Multiplicative (ZMod 3 × ZMod 3))
    (c : C) : c ^ 3 ∈ pCore 2 C := by
  apply (QuotientGroup.eq_one_iff _).mp
  change QuotientGroup.mk' (pCore 2 C) (c ^ 3) = 1
  apply e.injective
  simpa only [map_pow, map_one] using nine_cube (e (QuotientGroup.mk' (pCore 2 C) c))

public theorem subgroup_le_borel (C : Subgroup E) (hq : 2 < Nat.card F)
    (hn : S ≤ Subgroup.normalizer (C : Set E))
    (e : (C ⧸ pCore 2 C) ≃* Multiplicative (ZMod 3 × ZMod 3)) : C ≤ B := by
  have hp := core_le_root C hn
  have hproj (f : E →* SL(2, F)) (hf : upperUnipotent F ≤ (S).map f)
      (hS : (S).map f ≤ upperUnipotent F) : C.map f ≤ rankOneBorel F := by
    apply le_borel_of_cubes _ hq
    · exact hf.trans ((Subgroup.map_mono hn).trans (Subgroup.le_normalizer_map f))
    · rintro g ⟨c, hc, rfl⟩
      have hcube : c ^ 3 ∈ C.pCoreIn 2 :=
        ⟨(⟨c, hc⟩ : C)^3, cubes_mem_core C e ⟨c, hc⟩, rfl⟩
      rw [← map_pow]
      exact hS ⟨c ^ 3, hp hcube, rfl⟩
  apply Subgroup.le_prod_iff.mpr
  constructor
  · apply hproj (MonoidHom.fst _ _)
    · intro a ha; exact ⟨(a, 1), ⟨ha, (upperUnipotent F).one_mem⟩, rfl⟩
    · rintro a ⟨x, hx, rfl⟩; exact hx.1
  · apply hproj (MonoidHom.snd _ _)
    · intro a ha; exact ⟨(1, a), ⟨(upperUnipotent F).one_mem, ha⟩, rfl⟩
    · rintro a ⟨x, hx, rfl⟩; exact hx.2

end Matrix.SpecialLinearGroup.RootNormalizedNine
