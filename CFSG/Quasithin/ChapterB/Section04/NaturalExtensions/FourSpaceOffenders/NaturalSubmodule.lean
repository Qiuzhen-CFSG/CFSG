module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FourSpaceOffenders.AxisGeometry
public import Theory.Representation.BinaryOffender.SectionLinear

/-!
# Offenders on the four-space with a natural commutator submodule

Every nontrivial elementary actor has its fixed space inside the specified
natural submodule. Its fixed dimension therefore agrees with that of the
marked natural action. The fixed-plane criterion identifies best offenders
with the full common-axis groups. An explicit coordinate hyperplane supplies
an offender, giving quadratic ratio one; all best offenders are quadratic.
Source: Aschbacher–Smith, B.4.8(3), printed p.91 (1 March 2004).
-/

public section
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.ChapterB.NaturalExtensions
open BinaryLinearThree FourSpaceOffenders
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) BinaryLinearThree.Group V)
  (N : Subrepresentation ρ) (e : Representation.Equiv N.toRepresentation W)
  (hm : Coinvariants.ker ρ ≤ N.toSubmodule)
  (hind : ∀ A B : Submodule (ZMod 2) V,
      (∀ g v, v ∈ A → ρ g v ∈ A) →
      (∀ g v, v ∈ B → ρ g v ∈ B) → IsCompl A B → A = ⊥ ∨ B = ⊥)
  (hdim : Module.finrank (ZMod 2) V = 4)
include e hm hind hdim

theorem natural_submodule_fixed_finrank {A : Subgroup BinaryLinearThree.Group}
    (hA : IsElementaryTwo A) :
    Module.finrank (ZMod 2) (fixedSpace ρ A) =
      Module.finrank (ZMod 2) (fixedSpace W A) := by
  let _ : IsElementaryAbelian 2 A := hA.2
  obtain ⟨a, ha, hne⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  have ho : orderOf a = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian a ha) hne
  have hle : fixedSpace ρ A ≤ N.toSubmodule :=
    (fixedSpace_antitone ρ (zpowers_le.mpr ha)).trans
      (natural_submodule_involutions ρ N e hm hind hdim a ho).2.2
  have hdimN := (subrepresentationFixedEquiv ρ N A).finrank_eq
  rw [inf_eq_right.mpr hle] at hdimN
  have hmap := fixedSpace_map_equivariant N.toRepresentation W (MonoidHom.id _)
    e.toLinearEquiv (fun g v => LinearMap.congr_fun (e.isIntertwining' g) v) A
  rw [Subgroup.map_id] at hmap
  rw [← hdimN, ← hmap, LinearEquiv.finrank_map_eq]

theorem natural_best_iff_fullAxis (A : Subgroup BinaryLinearThree.Group) :
    IsBestOffender ρ A ↔ IsFullAxisGroup BinaryField.two 3 A := by
  have hi := natural_submodule_involutions ρ N e hm hind hdim
  rw [best_iff ρ hdim (fun a ha => (hi a ha).2.1), fullAxis_iff_fixed_plane]
  constructor
  · rintro ⟨hA,hr,hf⟩
    exact ⟨hA,hr,(natural_submodule_fixed_finrank ρ N e hm hind hdim hA).symm.trans hf⟩
  · rintro ⟨hA,hr,hf⟩
    exact ⟨hA,hr,(natural_submodule_fixed_finrank ρ N e hm hind hdim hA).trans hf⟩

theorem natural_quadraticRatio : quadraticRatio ρ = 1 := by
  let f : BinaryLinearThree.Vector →ₗ[ZMod 2] ZMod 2 := LinearMap.proj (2 : Fin 3)
  have hs : Function.Surjective f := fun x => ⟨fun _ => x, rfl⟩
  have hP : Module.finrank (ZMod 2) (BinaryLinearThree.Vector ⧸ f.ker) = 1 := by
    rw [(LinearMap.quotKerEquivOfSurjective f hs).finrank_eq]
    exact Module.finrank_self (ZMod 2)
  have hA := (natural_best_iff_fullAxis ρ N e hm hind hdim (axisGroup f.ker)).mpr
    (axisGroup_full f.ker hP)
  exact quadraticRatio_eq_one_of_no_strong ρ ⟨axisGroup f.ker, hA.isOffender ρ⟩
    (no_strong ρ hdim (fun a ha =>
      (natural_submodule_involutions ρ N e hm hind hdim a ha).2.1))

theorem natural_fullAxis_quadratic {A : Subgroup BinaryLinearThree.Group}
    (hA : IsFullAxisGroup BinaryField.two 3 A) : IsQuadratic ρ A :=
  best_quadratic ρ hdim (fun a ha =>
    ⟨(natural_submodule_involutions ρ N e hm hind hdim a ha).1,
      (natural_submodule_involutions ρ N e hm hind hdim a ha).2.1⟩)
    ((natural_best_iff_fullAxis ρ N e hm hind hdim A).mpr hA)
end CFSG.Quasithin.ChapterB.NaturalExtensions
