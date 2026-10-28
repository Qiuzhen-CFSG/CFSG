module

public import Theory.SpecificGroups.SL2.RootNormalizedNine.Core
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Diagonal quotients of root-normalized subgroups

For a subgroup of two upper triangular SL₂ groups in characteristic two,
the joint diagonal map has two-group kernel. If the full root product
normalizes the subgroup, Sylow maximality identifies this kernel with its
two-core. An elementary abelian quotient of order nine then forces each
diagonal coordinate to be nontrivial: otherwise that quotient would embed
in the cyclic multiplicative group of the field.

Also, every subgroup between the root product and the product Borel is
normalized by the Borel, since the joint diagonal image is abelian.

Source application: Aschbacher–Smith, `refs/quasithin.pdf`, printed p.1164,
proof of 15.4.20, ordinary even-field component case.
-/

open Matrix
open scoped MatrixGroups commutatorElement
namespace Matrix.SpecialLinearGroup.RootNormalizedNine
variable {F : Type*} [Field F]
local notation "E" => SL(2, F) × SL(2, F)
local notation "S" => Subgroup.prod (upperUnipotent F) (upperUnipotent F)
local notation "B" => Subgroup.prod (rankOneBorel F) (rankOneBorel F)
local notation "u" => transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one

private def diagonalEntryHom : rankOneBorel F →* Fˣ where
  toFun g := Units.mk0 (g.val.val 0 0) (by
    have hd : g.val.val 0 0 * g.val.val 1 1 = 1 := by
      simpa only [det_fin_two, (mem_rankOneBorel_iff _).mp g.property,
        mul_zero, sub_zero] using g.val.property
    exact left_ne_zero_of_mul_eq_one hd)
  map_one' := by ext; rfl
  map_mul' g h := by
    ext
    simp [mul_apply, Fin.sum_univ_two, (mem_rankOneBorel_iff _).mp h.property]

private theorem diagonalEntry_eq_one_iff (g : rankOneBorel F) :
    diagonalEntryHom g = 1 ↔ g.val ∈ upperUnipotent F := by
  constructor
  · intro hg
    have h00 : g.val.val 0 0 = 1 := congrArg Units.val hg
    have h10 := (mem_rankOneBorel_iff _).mp g.property
    have h11 : g.val.val 1 1 = 1 := by
      simpa only [det_fin_two, h00, h10, one_mul, mul_zero, sub_zero] using g.val.property
    refine (mem_upperUnipotent F _).mpr ⟨g.val.val 0 1, ?_⟩
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [transvection_coe, h00, h10, h11]
  · intro hg
    obtain ⟨t, ht⟩ := (mem_upperUnipotent F _).mp hg
    apply Units.ext
    change g.val.val 0 0 = 1
    rw [← ht]
    simp [transvection_coe]

private def diagonalPairHom (C : Subgroup E) (hB : C ≤ B) : C →* Fˣ × Fˣ :=
  (diagonalEntryHom.comp
    ((MonoidHom.fst _ _).comp C.subtype |>.codRestrict (rankOneBorel F)
      (fun c => (hB c.property).1))).prod
  (diagonalEntryHom.comp
    ((MonoidHom.snd _ _).comp C.subtype |>.codRestrict (rankOneBorel F)
      (fun c => (hB c.property).2)))

private theorem mem_diagonalPair_ker (C : Subgroup E) (hB : C ≤ B) (c : C) :
    c ∈ (diagonalPairHom C hB).ker ↔ c.val ∈ S := by
  change (_, _) = (1, 1) ↔ _
  rw [Prod.mk.injEq]
  change (diagonalEntryHom ⟨c.val.1, (hB c.property).1⟩ = 1 ∧
    diagonalEntryHom ⟨c.val.2, (hB c.property).2⟩ = 1) ↔ _
  rw [diagonalEntry_eq_one_iff, diagonalEntry_eq_one_iff]
  rfl

variable [Finite F] [CharP F 2]

omit [Finite F] in
private theorem root_square (g : SL(2, F)) (hg : g ∈ upperUnipotent F) : g^2 = 1 := by
  obtain ⟨t, rfl⟩ := (mem_upperUnipotent F g).mp hg
  rw [pow_two, ← transvection_add]
  have ht : t + t = 0 := by
    have := CharP.cast_eq_zero F 2
    linear_combination t * this
  rw [ht, transvection_coeff_zero]

private theorem diagonalPair_ker (C : Subgroup E) (hB : C ≤ B)
    (hn : S ≤ Subgroup.normalizer (C : Set E)) :
    (diagonalPairHom C hB).ker = pCore 2 C := by
  apply le_antisymm
  · apply le_sSup
    refine ⟨inferInstance, ?_⟩
    intro c
    refine ⟨1, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    have hc := (mem_diagonalPair_ker C hB c.val).mp c.property
    exact Prod.ext (root_square _ hc.1) (root_square _ hc.2)
  · intro c hc
    apply (mem_diagonalPair_ker C hB c).mpr
    exact core_le_root C hn ⟨c, hc, rfl⟩

private theorem not_cyclic_nine : ¬ IsCyclic (Multiplicative (ZMod 3 × ZMod 3)) := by
  intro h
  have hd := Monoid.exponent_dvd_of_forall_pow_eq_one nine_cube
  rw [IsCyclic.exponent_eq_card] at hd
  norm_num at hd

omit [CharP F 2] in
private theorem diagonal_ker_ne_core (C : Subgroup E)
    (e : (C ⧸ pCore 2 C) ≃* Multiplicative (ZMod 3 × ZMod 3))
    (f : C →* Fˣ) : f.ker ≠ pCore 2 C := by
  intro hf
  let g := QuotientGroup.lift (pCore 2 C) f hf.ge
  have hg : Function.Injective g :=
    (QuotientGroup.injective_lift_iff _ _ _).mpr hf.symm
  exact not_cyclic_nine (isCyclic_of_injective (g.comp e.symm.toMonoidHom)
    (hg.comp e.symm.injective))

/-- Both diagonal coordinates are nontrivial when the core quotient is E₉. -/
public theorem exists_diagonal_ne_one (C : Subgroup E) (hB : C ≤ B)
    (hn : S ≤ Subgroup.normalizer (C : Set E))
    (e : (C ⧸ pCore 2 C) ≃* Multiplicative (ZMod 3 × ZMod 3)) :
    (∃ c ∈ C, c.1.val 0 0 ≠ 1) ∧ (∃ c ∈ C, c.2.val 0 0 ≠ 1) := by
  classical
  let d := diagonalPairHom C hB
  have hd := diagonalPair_ker C hB hn
  constructor
  · by_contra h
    push Not at h
    apply diagonal_ker_ne_core C e ((MonoidHom.snd _ _).comp d)
    rw [← hd]
    ext c
    change (d c).2 = 1 ↔ d c = 1
    have hc : (d c).1 = 1 := Units.ext (h c.val c.property)
    exact ⟨fun h => Prod.ext hc h, fun h => congrArg Prod.snd h⟩
  · by_contra h
    push Not at h
    apply diagonal_ker_ne_core C e ((MonoidHom.fst _ _).comp d)
    rw [← hd]
    ext c
    change (d c).1 = 1 ↔ d c = 1
    have hc : (d c).2 = 1 := Units.ext (h c.val c.property)
    exact ⟨fun h => Prod.ext h hc, fun h => congrArg Prod.fst h⟩

omit [Finite F] [CharP F 2] in
public theorem borel_normalizes_of_root_le (C : Subgroup E) (hSC : S ≤ C) (hCB : C ≤ B) :
    B ≤ Subgroup.normalizer (C : Set E) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro b hb c hc
  let b' : B := ⟨b, hb⟩
  let c' : B := ⟨c, hCB hc⟩
  have hm : ⁅b', c'⁆ ∈ (diagonalPairHom B le_rfl).ker := by
    change diagonalPairHom B le_rfl ⁅b', c'⁆ = 1
    simp [commutatorElement_def]
  have hS : ⁅b, c⁆ ∈ S := (mem_diagonalPair_ker B le_rfl _).mp hm
  have hmem := C.mul_mem (hSC hS) hc
  simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one] using hmem

end Matrix.SpecialLinearGroup.RootNormalizedNine
