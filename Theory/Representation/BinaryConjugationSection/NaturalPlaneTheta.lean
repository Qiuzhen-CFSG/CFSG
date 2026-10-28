module
public import Theory.Representation.BinaryConjugationSection.NaturalNormalizer
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models
public import Theory.GroupTheory.PResidual.SymmetricThreeProductTheta

/-!
# Cubic generation of a natural plane normalizer

For a binary four-dimensional conjugation section with two-group action
kernel, the relative normalizer of a two-dimensional image maps to its
plane stabilizer. The diagonal actions on the plane and its quotient
identify the stabilizer modulo its two-core with S₃ × S₃. The composite
has two-group kernel, so cubic elements generate the entire two-residual
of the original relative normalizer. Surjectivity of the natural action
is unnecessary.

This is the lifting step used with the original theta bound in
Aschbacher--Smith 13.8.32, The Classification of Quasithin Groups,
combined manuscript of 1 March 2004, printed p.965.
-/

public noncomputable section
open Subgroup
namespace Representation.BinaryConjugationSection
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.SmallParabolicLevi
variable {G : Type*} [Group G] [Finite G]
  {H U Z : Subgroup G} {ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2)}
  (d : BinaryConjugationSection H U Z ρ)

/-- The actual relative normalizer has cubic-generated two-residual. -/
theorem natural_plane_normalizer_cubic_closure
    (π : H →* LinearGroup 4) (hact : ∀ h w, ρ h w = π h w)
    (hk : IsPGroup 2 π.ker)
    (B : Subgroup G) (hBU : B ≤ U) (hZB : Z ≤ B)
    (hd : Module.finrank (ZMod 2) (d.imageSpace B) = 2) :
    closure {x : (H ⊓ normalizer (B:Set G) : Subgroup G) | orderOf x = 3} =
      pResidual 2 (H ⊓ normalizer (B:Set G) : Subgroup G) := by
  let P := H ⊓ normalizer (B:Set G)
  let W := d.imageSpace B
  let j : P →* H := inclusion inf_le_left
  let f : P →* parabolic W := (π.comp j).codRestrict (parabolic W)
    (fun x => (d.natural_normalizer_iff π hact B hBU hZB _).mp x.property.2)
  have hf : IsPGroup 2 f.ker := by
    dsimp only [f]
    rw [MonoidHom.ker_codRestrict,←MonoidHom.comap_ker]
    exact hk.comap_of_injective j (inclusion_injective _)
  have hdq : Module.finrank (ZMod 2) ((Fin 4 → ZMod 2) ⧸ W) = 2 := by
    have hh := W.finrank_quotient_add_finrank
    change Module.finrank (ZMod 2) W = 2 at hd
    rw [hd,Module.finrank_fin_fun] at hh
    omega
  let a : W ≃ₗ[ZMod 2] Space 2 := LinearEquiv.ofFinrankEq _ _ (by simpa [Space] using hd)
  let b : ((Fin 4 → ZMod 2) ⧸ W) ≃ₗ[ZMod 2] Space 2 :=
    LinearEquiv.ofFinrankEq _ _ (by simpa [Space] using hdq)
  let e := (quotientTwoCoreEquivOfCoordinates W a b).trans
    (linearTwoEquivSymmetricThree.prodCongr linearTwoEquivSymmetricThree)
  let q := e.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 (parabolic W))).comp f)
  have hq : IsPGroup 2 q.ker := by
    dsimp only [q]
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,
      ←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_ker_isPGroup f hf
  exact SymmetricThreeProductResidual.cubic_closure_eq_twoResidual q hq

end Representation.BinaryConjugationSection
