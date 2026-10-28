module

public import Theory.SpecificGroups.Tits.AmalgamRigidity.LocalRestrictions.Witnesses
public import Theory.SpecificGroups.Tits.R1CosetCover
public import Theory.SpecificGroups.Tits.R1DihedralBound
public import Theory.SpecificGroups.Tits.ReeLocalBlockOrders


/-!
# An additional automorphism of the first Tits parabolic

The local nine-generator presentation maps isomorphically onto the actual
first parabolic: its certified coset bound and the marked subgroup's order
are both 10240. The parity that is odd on s3, s5, s7 and even on the other
six generators satisfies all 28 local relators, hence transports through
this marked isomorphism to a character of the first parabolic.

The central involution z = r5 = s1*s5² has even parity. Multiplying each
odd element by z therefore defines an involutive automorphism. Applying the
same construction to the Sylow subgroup gives its literal restriction,
whose images of s3 and s8 have normal-form indices 69 and 1024.

This proves the first witness contract used by the endpoint restriction
count. All word calculations are algebraic, apart from checks in the
two-element character group.

Source: Parrott, “A Characterization of the Tits' Simple Group” (1972), §5,
p.683; Aschbacher--Smith F.1.11--12, printed pp.262--263. The proposed pair
is recorded in LocalRestrictions/source/extension-images.json.
-/

open Tits Tits.ExceptionalParabolics

namespace Tits.AmalgamRigidity.FirstExtension
noncomputable section

private theorem local_bound : Finite ParrottR1Group ∧ Nat.card ParrottR1Group ≤ 10240 := by
  obtain ⟨hfinite, hcard⟩ := parrottR1DihedralSubgroup_finite_card_le
  let := hfinite
  obtain ⟨hlocal, hbound⟩ := parrottR1CosetCover.finite_card_le
    parrottR1_closure_range_generator
  exact ⟨hlocal, hbound.trans (by simpa using Nat.mul_le_mul_right 1024 hcard)⟩

private def localEquiv : ParrottR1Group ≃* parrottR1Subgroup := by
  let := local_bound.1
  exact MulEquiv.ofBijective parrottR1ToSubgroup
    (parrottR1ToSubgroup_surjective.bijective_of_nat_card_le
      (by rw [ReeLocalBlockOrders.r1_card]; exact local_bound.2))

private abbrev C2 := Multiplicative (ZMod 2)
private def parityGenerator : ParrottR1Generator → C2
  | .s3 | .s5 | .s7 => Multiplicative.ofAdd 1
  | _ => 1

private theorem parity_relations (i : ParrottR1RelatorIndex) :
    FreeGroup.lift parityGenerator (parrottR1Relator i) = 1 := by
  cases i <;>
    simp [parrottR1Relator, parrottR1RelatorInclusion, parrottRelator,
      parrottCommutator, parrottR3, parrottR5, parrottR7, parrottR1Delete,
      parityGenerator] <;> decide

private def markedEquiv : ParrottR1Group ≃* first :=
  localEquiv.trans ((parrottFiniteImageEquiv.subgroupMap parrottR1Subgroup).trans
    (MulEquiv.subgroupCongr ReeLocalBlockOrders.first_map))

private theorem markedEquiv_generator_val (i : ParrottR1Generator) :
    (markedEquiv (parrottR1Generator i)).val =
      atlas1600ParrottAssignment (parrottR1GeneratorInclusion i) := by
  change parrottFiniteImageEquiv (parrottR1ToParrott (parrottR1Generator i)) = _
  rw [parrottR1ToParrott_generator, parrottFiniteImageEquiv_generator]

private def localParity : ParrottR1Group →* C2 :=
  PresentedGroup.toGroup (by rintro _ ⟨i, rfl⟩; exact parity_relations i)

private def parity : first →* C2 := localParity.comp markedEquiv.symm.toMonoidHom

private theorem parity_generator (i : ParrottR1Generator) :
    parity (markedEquiv (parrottR1Generator i)) = parityGenerator i := by
  simp only [parity, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply]
  exact PresentedGroup.toGroup.of _

end
end Tits.AmalgamRigidity.FirstExtension

namespace Tits.AmalgamRigidity.FirstExtension
private theorem c2_mul_eq_one (a b : C2) : a * b = 1 ↔ (a = 1 ↔ b = 1) := by
  exact (by decide +kernel : ∀ a b : C2, a * b = 1 ↔ (a = 1 ↔ b = 1)) a b

private noncomputable def centralTwist {G : Type*} [Group G] (χ : G →* C2) (z : G)
    (hz : z ∈ Subgroup.center G) (hz2 : z * z = 1) (hχ : χ z = 1) : MulAut G := by
  classical
  let t : G → G := fun x => if χ x = 1 then x else z * x
  have hmul (x y : G) : t (x * y) = t x * t y := by
    have hc : x * z = z * x := Subgroup.mem_center_iff.mp hz x
    have hp := c2_mul_eq_one (χ x) (χ y)
    by_cases hx : χ x = 1 <;> by_cases hy : χ y = 1
    · simp [t, map_mul, hx, hy]
    · simp [t, map_mul, hx, hy, ← mul_assoc, hc]
    · simp [t, map_mul, hx, hy, mul_assoc]
    · have hxy : χ x * χ y = 1 := hp.mpr (by simp [hx, hy])
      simp only [t, map_mul, hxy, if_true, hx, hy, if_false]
      calc x * y = (z * z) * (x * y) := by rw [hz2, one_mul]
        _ = z * (z * x) * y := by simp only [mul_assoc]
        _ = z * (x * z) * y := by rw [hc]
        _ = (z * x) * (z * y) := by simp only [mul_assoc]
  have hinv : Function.Involutive t := by
    intro x
    by_cases hx : χ x = 1
    · simp [t, hx]
    · simp [t, hx, map_mul, hχ, ← mul_assoc, hz2]
  exact { toFun := t, invFun := t, left_inv := hinv, right_inv := hinv, map_mul' := hmul }
end Tits.AmalgamRigidity.FirstExtension

namespace Tits.AmalgamRigidity.FirstExtension
open ExceptionalParabolics SharpOuterBound.LocalImageBound
noncomputable section

private abbrev inclusion : S →* first := Subgroup.inclusion sylow_le_first

private def z : S := ⟨atlas1600R5, atlas1600R5_mem_sylowTwo⟩

private theorem z_center : z ∈ Subgroup.center S := atlas1600R5_mem_center_sylowTwo

private theorem z_square : z * z = 1 := by
  have hs := (atlas1600SylowTwo_mem_center_iff (z * z)).mp
    ((Subgroup.center S).mul_mem z_center z_center)
  change atlas1600R5 * atlas1600R5 = 1 ∨ atlas1600R5 * atlas1600R5 = atlas1600R5 at hs
  apply Subtype.ext
  rcases hs with h | h
  · exact h
  · have he : atlas1600R5 * atlas1600R5 = atlas1600R5 * 1 := by simpa using h
    exact (atlas1600R5_ne_one (mul_left_cancel he)).elim

private theorem first_z_center : inclusion z ∈ Subgroup.center first := by
  apply Subgroup.mem_center_iff.mpr
  intro x
  apply Subtype.ext
  exact Subgroup.mem_centralizer_singleton_iff.mp (first_le_centralizer x.property)

private theorem parity_z : parity (inclusion z) = 1 := by
  have hw : inclusion z = markedEquiv (parrottR1Generator .s1) *
      markedEquiv (parrottR1Generator .s5) ^ 2 := by
    apply Subtype.ext
    change atlas1600R5 = _ * _ ^ 2
    rw [markedEquiv_generator_val, markedEquiv_generator_val]
    exact atlas1600R5_eq
  rw [hw, map_mul, map_pow, parity_generator, parity_generator]
  decide

private theorem parity_sylow_generator (i : Fin 8) :
    parity (inclusion (sylowGenerator i)) =
      parityGenerator (![.s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8] i) := by
  have he : inclusion (sylowGenerator i) = markedEquiv
      (parrottR1Generator (![.s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8] i)) := by
    apply Subtype.ext
    rw [markedEquiv_generator_val]
    fin_cases i <;> rfl
  rw [he, parity_generator]

private def endpointAut : MulAut first := centralTwist parity (inclusion z) first_z_center
  (by rw [← map_mul, z_square, map_one]) parity_z

private def sylowAut : MulAut S := centralTwist (parity.comp inclusion) z z_center z_square parity_z

private theorem extension_agrees (s : S) : endpointAut (sylowAmalgam.left s) =
    sylowAmalgam.left (sylowAut s) := by
  change (if parity (inclusion s) = 1 then inclusion s else inclusion z * inclusion s) =
    inclusion (if parity (inclusion s) = 1 then s else z * s)
  split <;> simp only [map_mul]

private theorem sylowAut_s3 : sylowAut (sylowGenerator 2) = atlas1600SylowTwoEquiv 69 := by
  change (if parity (inclusion (sylowGenerator 2)) = 1 then sylowGenerator 2
    else z * sylowGenerator 2) = _
  rw [parity_sylow_generator]
  norm_num [parityGenerator]
  apply Subtype.ext
  rw [atlas1600SylowTwoEquiv_apply]
  change atlas1600R5 * atlas1600ParrottAssignment .s3 = atlas1600SylowTwoNormalForm 69
  have h13 : Commute (atlas1600ParrottAssignment .s1) (atlas1600ParrottAssignment .s3) := by
    apply Commute.inv_inv_iff.mp
    apply commutatorElement_eq_one_iff_commute.mp
    simpa only [commutatorElement_def, inv_inv, parrottRelator, parrottCommutator,
      map_mul, map_inv, FreeGroup.lift_apply_of] using
      atlas1600ParrottAssignment_relations .ii_s1_s3
  have h3z : atlas1600ParrottAssignment .s3 * atlas1600R5 =
      atlas1600R5 * atlas1600ParrottAssignment .s3 :=
    congrArg Subtype.val (Subgroup.mem_center_iff.mp z_center (sylowGenerator 2))
  rw [← h3z, atlas1600R5_eq, atlas1600SylowTwoNormalForm_eq]
  norm_num
  rw [← mul_assoc, h13.eq]

private theorem sylowAut_s8 : sylowAut (sylowGenerator 7) = atlas1600SylowTwoEquiv 1024 := by
  change (if parity (inclusion (sylowGenerator 7)) = 1 then sylowGenerator 7
    else z * sylowGenerator 7) = _
  rw [parity_sylow_generator]
  norm_num [parityGenerator]
  apply Subtype.ext
  rw [atlas1600SylowTwoEquiv_apply, atlas1600SylowTwoNormalForm_eq]
  norm_num
  rfl

end
end Tits.AmalgamRigidity.FirstExtension

namespace Tits.AmalgamRigidity
open FirstExtension SharpOuterBound.LocalImageBound

/-- An actual first-parabolic automorphism restricts to the pair (69,1024). -/
public theorem firstExtraExtension : FirstExtraExtension := by
  refine ⟨sylowAut, ⟨endpointAut, extension_agrees⟩, ?_⟩
  simp only [generatorPair, sylowAut_s3, sylowAut_s8, Equiv.symm_apply_apply]
end Tits.AmalgamRigidity
