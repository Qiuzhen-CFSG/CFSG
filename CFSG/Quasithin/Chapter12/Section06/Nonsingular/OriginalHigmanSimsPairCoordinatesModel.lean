module
public import Theory.Representation.BinaryPermutation.EightNonsingularStabilizer
public import Theory.Representation.BinaryPermutation.EightFormOrbits
public import Theory.Representation.BinaryPermutation.OffenderFixedSpace
public import Theory.Representation.BinaryOffender.PermutationConjugacy
public import Mathlib.GroupTheory.Sylow

/-!
# The fixed plane of a nonsingular point Sylow

Three commuting even involutions have coordinate orbits of sizes two,
four and two. Each fixes a coordinate, so a fixed natural class has a
fixed representative. Modulo constants its fixed space has at most four
elements. Transport this actual elementary subgroup into a Sylow of the
stabilizer of any nonsingular vector, using the original A8 action.

This is the coordinate calculation used after the original HS pair has
returned to V. It assumes no module structure on that returned pair.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
namespace CFSG.Quasithin.Chapter12.Section06.OriginalHigmanSimsPairCoordinates

private abbrev A := alternatingGroup (Fin 8)
private abbrev W := natural (Fin 8)
private abbrev K := Multiplicative (ZMod 2 × ZMod 2 × ZMod 2)
private abbrev ρ := alternatingNaturalRepresentation (Fin 8)
private def x : A := ⟨Equiv.swap 2 3 * Equiv.swap 4 5, by
  rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩
private def y : A := ⟨Equiv.swap 2 4 * Equiv.swap 3 5, by
  rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩
private def z : A := ⟨Equiv.swap 0 1 * Equiv.swap 6 7, by
  rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩
private def cube : K →* A where
  toFun a := (if a.toAdd.1 = 0 then 1 else x) *
    (if a.toAdd.2.1 = 0 then 1 else y) * (if a.toAdd.2.2 = 0 then 1 else z)
  map_one' := by decide +kernel
  map_mul' := by decide +kernel
private theorem cube_two : IsPGroup 2 K := by
  intro a
  exact ⟨1,(by decide : ∀ a : K, a ^ 2 = 1) a⟩
private def base : W := coreToNatural (Fin 8) (EightNonsingular.pair 0 1)
private theorem cube_base (a : K) : ρ (cube a) base = base := by
  change naturalRepresentation (Fin 8) (cube a).val
    (coreToNatural (Fin 8) (EightNonsingular.pair 0 1)) = _
  rw [←coreToNatural_equivariant]
  exact congrArg (coreToNatural (Fin 8))
    ((by decide +kernel : ∀ a : K, alternatingCoreRepresentation (Fin 8) (cube a)
      (EightNonsingular.pair 0 1) = EightNonsingular.pair 0 1) a)
private theorem base_form : TerminalOrthogonal.Eight.form base = 1 := by
  rw [base, EightGeometry.nonsingular_core_iff]
  left
  decide +kernel
private def block (a b : ZMod 2) : W :=
  coreToNatural (Fin 8) ⟨![0,0,a,a,a,a,b,b], by
    rw [mem_core]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    simp [CharTwo.add_self_eq_zero]⟩

private theorem fixed_shape (v : W) (hx : ρ x v = v) (hy : ρ y v = v)
    (hz : ρ z v = v) : ∃ a b : ZMod 2, v = block a b := by
  obtain ⟨w,hw,hrep⟩ := v.property
  have full_fixed (g : A) (i : Fin 8) (hi : g.val i = i) (hf : ρ g v = v) :
      representation (Fin 8) g.val w = w := by
    apply (deleted_fixed_iff_of_fixed_point g.val w i hi).mp
    rw [hrep]
    exact congrArg Subtype.val hf
  have hfx := full_fixed x 0 (by decide) hx
  have hfy := full_fixed y 0 (by decide) hy
  have hfz := full_fixed z 2 (by decide) hz
  have h23 : w 3 = w 2 := congrFun hfx 2
  have h45 : w 5 = w 4 := congrFun hfx 4
  have h24 : w 4 = w 2 := congrFun hfy 2
  have h01 : w 1 = w 0 := congrFun hfz 0
  have h67 : w 7 = w 6 := congrFun hfz 6
  refine ⟨w 2 - w 0,w 6 - w 0,?_⟩
  apply Subtype.ext
  change v.val = (constants (Fin 8)).mkQ _
  rw [←hrep]
  apply (Submodule.Quotient.eq _).mpr
  refine (mem_constants_iff _).mpr ⟨w 0,fun i => ?_⟩
  change w i - (![0,0,w 2-w 0,w 2-w 0,w 2-w 0,w 2-w 0,w 6-w 0,w 6-w 0] :
    Full (Fin 8)) i = w 0
  fin_cases i <;> simp [h01,h23,h45,h24,h67]

private theorem cube_fixed_card : Nat.card (fixedSpace ρ cube.range) ≤ 4 := by
  have hs (v : fixedSpace ρ cube.range) : ∃ a b : ZMod 2, v.val = block a b := by
    apply fixed_shape v.val
    · exact v.property ⟨x,Multiplicative.ofAdd (1,0,0),by decide +kernel⟩
    · exact v.property ⟨y,Multiplicative.ofAdd (0,1,0),by decide +kernel⟩
    · exact v.property ⟨z,Multiplicative.ofAdd (0,0,1),by decide +kernel⟩
  choose a b hab using hs
  let f : fixedSpace ρ cube.range → ZMod 2 × ZMod 2 := fun v => (a v,b v)
  have hf : Function.Injective f := by
    intro v w he
    apply Subtype.ext
    rw [hab v,hab w,show a v = a w from congrArg Prod.fst he,
      show b v = b w from congrArg Prod.snd he]
  simpa using Nat.card_le_card_of_injective f hf

/-- The literal natural fixed space of any nonsingular point-stabilizer Sylow
has at most four vectors. -/
theorem nonsingular_stabilizer_sylow_fixed_card_le_four (v : natural (Fin 8))
    (hv : TerminalOrthogonal.Eight.form v ≠ 0)
    (P : Sylow 2 (EightNonsingular.stabilizer v)) :
    Nat.card (fixedSpace (alternatingNaturalRepresentation (Fin 8)) ((P : Subgroup _).map
      (EightNonsingular.stabilizer v).subtype)) ≤ 4 := by
  have hb : base ≠ 0 := by
    intro he
    have hh := base_form
    rw [he,map_zero] at hh
    exact zero_ne_one hh
  have hv0 : v ≠ 0 := by
    intro he
    exact hv (he ▸ map_zero _)
  have hform : TerminalOrthogonal.Eight.form base = TerminalOrthogonal.Eight.form v := by
    rw [base_form]
    exact ((by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hv).symm
  obtain ⟨g,hg⟩ := EightGeometry.exists_alternating_of_form_eq base v hb hv0 hform
  let f₀ := (MulAut.conj g).toMonoidHom.comp cube
  have hf (a : K) : f₀ a ∈ EightNonsingular.stabilizer v := by
    change ρ (g*cube a*g⁻¹) v = v
    rw [←hg]
    have hi : ρ g⁻¹ (ρ g base) = base := by
      rw [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply]
    simp only [map_mul,Module.End.mul_apply,hi,cube_base]
  let f : K →* EightNonsingular.stabilizer v := f₀.codRestrict _ hf
  obtain ⟨Q,hQ⟩ := (cube_two.of_surjective f.rangeRestrict f.rangeRestrict_surjective).exists_le_sylow
  obtain ⟨c,hc⟩ := MulAction.exists_smul_eq (EightNonsingular.stabilizer v) Q P
  let s : A := c.val*g
  have hs : cube.range.map (MulAut.conj s).toMonoidHom ≤
      (P : Subgroup _).map (EightNonsingular.stabilizer v).subtype := by
    rintro _ ⟨_,⟨a,rfl⟩,rfl⟩
    have ha : c*f a*c⁻¹ ∈ (P : Subgroup _) := by
      rw [←hc]
      exact mem_map_of_mem (MulAut.conj c).toMonoidHom (hQ ⟨a,rfl⟩)
    have hh := mem_map_of_mem (EightNonsingular.stabilizer v).subtype ha
    simpa [s,f,f₀,MulAut.conj_apply,mul_assoc] using hh
  have hle : fixedSpace ρ ((P : Subgroup _).map (EightNonsingular.stabilizer v).subtype) ≤
      fixedSpace ρ (cube.range.map (MulAut.conj s).toMonoidHom) :=
    fun _ hw a => hw ⟨a.val,hs a.property⟩
  have hcard := Nat.card_le_card_of_injective (Submodule.inclusion hle)
    (Submodule.inclusion_injective hle)
  rw [←Nat.card_congr (fixedSpaceConjEquiv ρ cube.range s).toEquiv] at hcard
  exact hcard.trans cube_fixed_card

end CFSG.Quasithin.Chapter12.Section06.OriginalHigmanSimsPairCoordinates
