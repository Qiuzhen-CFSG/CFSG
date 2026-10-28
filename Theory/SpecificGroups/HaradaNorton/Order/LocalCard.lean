module

public import Theory.SpecificGroups.HaradaNorton.Order.LocalCard.Certificate
public import Theory.SpecificGroups.HaradaNorton.Order.LocalCard.Generation
public import Theory.SpecificGroups.HaradaNorton.Order.LocalCard.Relations
public import Theory.Alternating.Theorem523A6
import Mathlib.Tactic.NormNum

/-!
# Identifying the concrete HN word subgroup from a presentation certificate

A generating family satisfying Suzuki's relations gives a surjection from
`A₁₂` onto the actual word subgroup. The subgroup contains the nonidentity
matrix generator `a`, so simplicity makes the surjection injective. Its
cardinality is consequently `12! / 2`.

The abstract presentation theorem is Suzuki (2.15), as formalized in
`Theory.Alternating.Theorem523A6`. The concrete subgroup and its provenance
are in `Order.LocalSubgroup`. The checked matrix relations and recovery words
in `LocalCard.Relations` and `LocalCard.Generation` supply the concrete
`LocalSuzukiCertificate`, identifying this subgroup with `A₁₂`.
-/

namespace HaradaNorton.OrderCertificate

open GLS3.Chapter5.SchurPresentation
open scoped commutatorElement

private theorem local_a_ne_one : (⟨a, a_mem_localSubgroup⟩ : localSubgroup) ≠ 1 := by
  intro h
  have ha : a = 1 := congrArg Subtype.val h
  apply aMatrix_mul_bMatrix_ne
  have hab : a * b = b * a := by rw [ha, one_mul, mul_one]
  simpa only [map_mul, matrixHom_a, matrixHom_b] using congrArg matrixHom hab

private theorem certificate_relator (c : LocalSuzukiCertificate) (r : SuzukiRelator 7) :
    FreeGroup.lift c.gen r.word = 1 := by
  cases r with
  | rootCube =>
      simpa [SuzukiRelator.word, suzukiFreeGenerator] using c.root_cube
  | tailSquare i hi =>
      simpa [SuzukiRelator.word, suzukiFreeGenerator] using c.tail_square i hi
  | rootAdjacentCube =>
      simpa [SuzukiRelator.word, suzukiFreeGenerator] using c.root_adjacent_cube
  | tailAdjacentCube i hi =>
      simpa [SuzukiRelator.word, suzukiFreeGenerator] using c.tail_adjacent_cube i hi
  | rootFarSquare j hj =>
      simpa [SuzukiRelator.word, suzukiFreeGenerator] using c.root_far_square j hj
  | tailFarCommutator i j hi hj hfar =>
      simp only [SuzukiRelator.word, map_commutatorElement,
        suzukiFreeGenerator, FreeGroup.lift_apply_of]
      exact commutatorElement_eq_one_iff_commute.mpr (c.tail_far_commute i j hi hj hfar)

/-- A checked concrete presentation certificate identifies the actual subgroup. -/
public noncomputable def localSubgroupEquivOfSuzuki (c : LocalSuzukiCertificate) :
    localSubgroup ≃* alternatingGroup (Fin 12) := by
  classical
  letI : IsSimpleGroup (alternatingGroup (Fin 12)) :=
    alternatingGroup.isSimpleGroup (by simp)
  let h : SuzukiPresentedGroup 7 →* localSubgroup := PresentedGroup.toGroup (by
    rintro _ ⟨r, rfl⟩
    exact certificate_relator c r)
  have hsurj : Function.Surjective h := by
    rw [← MonoidHom.range_eq_top]
    apply top_unique
    rw [← c.generates, Subgroup.closure_le]
    rintro x ⟨i, rfl⟩
    exact ⟨PresentedGroup.of i, PresentedGroup.toGroup.of _⟩
  let e : SuzukiPresentedGroup 7 ≃* alternatingGroup (Fin 12) :=
    MulEquiv.ofBijective (suzukiPresentedProjection 7)
      ⟨suzukiPresentedProjection_injective 7, suzukiPresentedProjection_surjective 7⟩
  let f : alternatingGroup (Fin 12) →* localSubgroup := h.comp e.symm.toMonoidHom
  have fsurj : Function.Surjective f := hsurj.comp e.symm.surjective
  have finj : Function.Injective f := by
    rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with hbot | htop
    · exact f.ker_eq_bot_iff.mp hbot
    · obtain ⟨x, hx⟩ := fsurj ⟨a, a_mem_localSubgroup⟩
      have hone : f x = 1 := MonoidHom.mem_ker.mp (by rw [htop]; trivial)
      exact (local_a_ne_one (hx.symm.trans hone)).elim
  exact (MulEquiv.ofBijective f ⟨finj, fsurj⟩).symm

/-- The concrete certificate suffices for the requested cardinality. -/
public theorem localSubgroup_card_of_suzuki (c : LocalSuzukiCertificate) :
    Nat.card localSubgroup = 239500800 := by
  rw [Nat.card_congr (localSubgroupEquivOfSuzuki c).toEquiv,
    Nat.card_eq_fintype_card, card_alternatingGroup]
  norm_num [Nat.factorial]

/-- The fixed matrix words satisfy Suzuki's presentation and generate the subgroup. -/
public noncomputable def localSuzukiCertificate : LocalSuzukiCertificate where
  gen := localSuzukiGen
  root_cube := localSuzukiGen_root_cube
  tail_square := localSuzukiGen_tail_square
  root_adjacent_cube := localSuzukiGen_root_adjacent_cube
  tail_adjacent_cube := localSuzukiGen_tail_adjacent_cube
  root_far_square := localSuzukiGen_root_far_square
  tail_far_commute := localSuzukiGen_tail_far_commute
  generates := localSuzukiGen_generates

/-- The actual ATLAS word subgroup in the fixed HN matrix carrier is `A₁₂`. -/
public noncomputable def localSubgroupEquiv :
    localSubgroup ≃* alternatingGroup (Fin 12) :=
  localSubgroupEquivOfSuzuki localSuzukiCertificate

/-- The actual ATLAS word subgroup has order `12! / 2 = 239500800`. -/
public theorem localSubgroup_card : Nat.card localSubgroup = 239500800 :=
  localSubgroup_card_of_suzuki localSuzukiCertificate

end HaradaNorton.OrderCertificate
