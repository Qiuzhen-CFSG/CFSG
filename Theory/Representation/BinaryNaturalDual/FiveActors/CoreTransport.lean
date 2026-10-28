module

public import Theory.Representation.BinaryNaturalDual.RadicalCore
public import Theory.Representation.BinaryNaturalDual.FiveActors.Basic

/-!
# Fixed spaces and generated cores of actual degree-five actors

Surjective transport carries the natural-plus-dual action of a linear
subgroup to the action of its inner image. Simultaneous conjugation of an
actor and its module coordinates preserves the generated core. Consequently,
placement inside a conjugate of a three-space radical gives the full core.
The same inner-image comparison identifies the radical's literal fixed
subspace as the product of the three-space and its dual annihilator.

The conjugate-placement premise is explicit. Exhaustive placement of the
high-rank elementary actors is a separate theorem, required to assemble
H.9.2(5). No subgroup classification is asserted here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), H.9.2(4–5),
printed pp.390–391 (PDF pp.401–402), and Definition E.3.30, printed p.237.
-/

public section

namespace BinaryNaturalDual

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]

theorem generatedCore_conjugate
    (ρ : Representation (ZMod 2) G V) (A : Subgroup G) (a : G) (k : ℕ) :
    (generatedCore (ρ.comp A.subtype) k).map (ρ a) =
      generatedCore (ρ.comp (A.map (MulAut.conj a).toMonoidHom).subtype) k := by
  let E := LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom a)
  let f := (MulAut.conj a).subgroupMap A
  apply generatedCore_map_surjective (ρ.comp A.subtype)
    (ρ.comp (A.map (MulAut.conj a).toMonoidHom).subtype)
    f.toMonoidHom f.surjective E
  intro g v
  change ρ a (ρ g.val v) = ρ (a * g.val * a⁻¹) (ρ a v)
  simp only [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel, mul_one]

theorem generatedCore_conjugate_eq_top_iff
    (ρ : Representation (ZMod 2) G V) (A : Subgroup G) (a : G) (k : ℕ) :
    generatedCore (ρ.comp (A.map (MulAut.conj a).toMonoidHom).subtype) k = ⊤ ↔
      generatedCore (ρ.comp A.subtype) k = ⊤ := by
  rw [← generatedCore_conjugate]
  let E := LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom a)
  change (generatedCore (ρ.comp A.subtype) k).map E.toLinearMap = ⊤ ↔ _
  simp

end BinaryNaturalDual

open BinaryLinear BinaryLinear.OuterCyclic
namespace BinaryNaturalDual.FiveActors
theorem generatedCore_inner_image (d : CoordinateAction 5) (A : Subgroup G) (k : ℕ) :
    generatedCore (d.representation.comp (A.map MulAut.conj).subtype) k =
      generatedCore (naturalDualRepresentation.comp A.subtype) k := by
  let f : A →* A.map (MulAut.conj : G →* M) := {
    toFun g := ⟨MulAut.conj g.val, Subgroup.mem_map_of_mem _ g.property⟩
    map_one' := Subtype.ext (map_one _)
    map_mul' g h := Subtype.ext (map_mul _ g.val h.val) }
  have hf : Function.Surjective f := by
    rintro ⟨_, g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩
  have he := generatedCore_map_surjective
    (naturalDualRepresentation.comp A.subtype)
    (d.representation.comp (A.map MulAut.conj).subtype) f hf
    (LinearEquiv.refl (ZMod 2) (CoordinateSpace 5))
    (fun g v => (d.on_inner g.val v).symm) k
  simpa using he.symm

theorem generatedCore_eq_top_of_inner_radical (d : CoordinateAction 5)
    (U : Submodule (ZMod 2) X) (hU : Module.finrank (ZMod 2) U = 3)
    (A : Subgroup G) (hA : A ≤ radical U) :
    generatedCore (d.representation.comp (A.map MulAut.conj).subtype) 3 = ⊤ := by
  rw [generatedCore_inner_image]
  exact generatedCore_five_radical (by simp [X]) U hU A hA

theorem generatedCore_eq_top_of_le_radicalActor (d : CoordinateAction 5)
    (U : Submodule (ZMod 2) X) (hU : Module.finrank (ZMod 2) U = 3)
    (A : Subgroup M) (hA : A ≤ radicalActor U) :
    generatedCore (d.representation.comp A.subtype) 3 = ⊤ := by
  let B := A.comap (MulAut.conj : G →* M)
  have hmap : B.map (MulAut.conj : G →* M) = A :=
    Subgroup.map_comap_eq_self (hA.trans (radicalActor_le_inner U))
  have hB : B ≤ radical U := by
    apply (Subgroup.map_le_map_iff_of_injective
      (MulAut.conj_injective_of_center_eq_bot center_eq_bot)).mp
    rw [hmap]
    exact hA
  rw [← hmap]
  exact generatedCore_eq_top_of_inner_radical d U hU B hB

theorem generatedCore_eq_top_of_conjugate_radical (d : CoordinateAction 5)
    (U : Submodule (ZMod 2) X) (hU : Module.finrank (ZMod 2) U = 3)
    (A : Subgroup M) (a : M)
    (hA : A.map (MulAut.conj a).toMonoidHom ≤ radicalActor U) :
    generatedCore (d.representation.comp A.subtype) 3 = ⊤ := by
  apply (generatedCore_conjugate_eq_top_iff d.representation A a 3).mp
  exact generatedCore_eq_top_of_le_radicalActor d U hU _ hA

theorem representation_on_inner (d : CoordinateAction 5) :
    d.representation.comp (MulAut.conj : G →* M) = naturalDualRepresentation := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  exact d.on_inner g v

theorem fixedSpace_inner_image (d : CoordinateAction 5) (A : Subgroup G) :
    Representation.BinaryOffender.fixedSpace d.representation (A.map MulAut.conj) =
      Representation.BinaryOffender.fixedSpace naturalDualRepresentation A := by
  rw [← Representation.BinaryOffender.fixedSpace_comp_map, representation_on_inner]

theorem fixedSpace_radicalActor (d : CoordinateAction 5)
    (U : Submodule (ZMod 2) X) (hU : U ≠ ⊥) (hUt : U ≠ ⊤) :
    Representation.BinaryOffender.fixedSpace d.representation (radicalActor U) =
      U.prod U.dualAnnihilator := by
  rw [radicalActor, fixedSpace_inner_image]
  simpa only [Representation.BinaryOffender.fixedSpace_comp_map,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype] using fixedSpace_radical U hU hUt

theorem finrank_fixedSpace_radicalActor (d : CoordinateAction 5)
    (U : Submodule (ZMod 2) X) (hU : U ≠ ⊥) (hUt : U ≠ ⊤) :
    Module.finrank (ZMod 2)
      (Representation.BinaryOffender.fixedSpace d.representation (radicalActor U)) = 5 := by
  rw [fixedSpace_radicalActor d U hU hUt, finrank_prod_dualAnnihilator]
  simp

end BinaryNaturalDual.FiveActors
