module
public import Theory.Representation.BinaryConjugationSection.NormalizingActors
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Stellmacher.CentralizerQuotientRepresentation
public import Stellmacher.ElementaryAbelianMaxJMap

/-!
# Thompson fixedness from a non-FF action on the original subgroup

A zero-kernel conjugation marking identifies the original elementary
subgroup with its coordinate space. If the extended normalizer action has
no FF offender, the maximum elementary subgroups centralize the original
subgroup: a nontrivial image would be an offender by the maximum-order
inequality. The proof transports the actual coordinate map and its kernel;
it makes no inference from an action on a chief quotient.

Source application: Aschbacher–Smith 10.1.2(1) and 10.2.9,
printed pp.742 and751, using B.2.5–7, printed pp.76–77.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace Representation.BinaryConjugationSection
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  {H W P S : Subgroup G} [IsElementaryAbelian 2 W]
  {ρ : Representation (ZMod 2) H V}

set_option backward.isDefEq.respectTransparency false in
theorem thompson_centralizes_of_nonFF_extension
    (c : BinaryConjugationSection H W ⊥ ρ)
    (hPW : P ≤ normalizer (W : Set G)) (hWS : W ≤ S) (hSP : S ≤ P)
    (η : Representation (ZMod 2) P V)
    (hη : ∀ (p : P) (w : W), η p (c.coordinates w).toAdd =
      (c.coordinates (W.normalizerMonoidHom (inclusion hPW p) w)).toAdd)
    (hno : ¬ IsFFModule (imageRepresentation η)) :
    elementaryAbelianMaxJ S ≤ centralizer (W : Set G) := by
  let U := W.subgroupOf P
  have hWP : W ≤ P := hWS.trans hSP
  let : U.Normal := normal_subgroupOf_of_le_normalizer hPW
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hWP
  have hi : Function.Injective c.coordinates := (MonoidHom.ker_eq_bot_iff _).mp (by
    rw [c.kernel_eq,bot_subgroupOf])
  let b : U ≃* Multiplicative V := (subgroupOfEquivOfLe hWP).trans
    (MulEquiv.ofBijective c.coordinates ⟨hi,c.onto⟩)
  let E : Additive U ≃ₗ[ZMod 2] V :=
    LinearEquiv.ofBijective (b.toMonoidHom.toAdditiveLeft.toZModLinearMap 2) b.bijective
  let q := actionHom η
  have hq : Function.Surjective q := η.asGroupHom.rangeRestrict_surjective
  have hk : q.ker = centralizer (U : Set P) := by
    ext p
    constructor
    · intro hp w hw
      have he : η p = 1 := congrArg (fun a : actionImage η => a.val.val) hp
      have h := hη p ⟨w,hw⟩
      rw [he,Module.End.one_apply] at h
      have hx := congrArg Subtype.val (hi (Multiplicative.toAdd.injective h.symm))
      apply Subtype.ext
      exact (mul_inv_eq_iff_eq_mul.mp hx).symm
    · intro hp
      apply Subtype.ext
      apply Units.ext
      apply LinearMap.ext
      intro v
      obtain ⟨w,rfl⟩ := c.onto (Multiplicative.ofAdd v)
      change η p (c.coordinates w).toAdd = (c.coordinates w).toAdd
      rw [hη]
      apply congrArg (fun z : W => (c.coordinates z).toAdd)
      apply Subtype.ext
      have hc := congrArg P.subtype (hp ⟨w,hWP w.property⟩ w.property)
      exact mul_inv_eq_iff_eq_mul.mpr hc.symm
  let τ := NormalElementaryQuotient.representation U q hq hk
  have hE (a : actionImage η) (u : Additive U) :
      E (τ a u) = imageRepresentation η a (E u) := by
    obtain ⟨p,rfl⟩ := hq a
    change E (τ (q p) u) = η p (E u)
    have he := NormalElementaryQuotient.representation_apply U q hq hk p u
    change (c.coordinates ((subgroupOfEquivOfLe hWP) (τ (q p) u).toMul)).toAdd =
      η p (c.coordinates ((subgroupOfEquivOfLe hWP) u.toMul)).toAdd
    rw [hη]
    apply congrArg (fun z : W => (c.coordinates z).toAdd)
    apply Subtype.ext
    exact congrArg P.subtype he
  have hc : elementaryAbelianMaxJ (S.subgroupOf P) ≤ q.ker := by
    by_contra hn
    have hf := NormalElementaryQuotient.isFFModule_of_thompson_not_le U q hq hk
      (S.subgroupOf P) (comap_mono hWS) hn
    apply hno
    exact hf.map_equivariant τ (imageRepresentation η) (MonoidHom.id _) (fun _ _ h => h) E hE
  have hm : (elementaryAbelianMaxJ (S.subgroupOf P)).map P.subtype = elementaryAbelianMaxJ S := by
    rw [←elementaryAbelianMaxJ_map_injective P.subtype P.subtype_injective,
      map_subgroupOf_eq_of_le hSP]
  rw [←hm]
  rintro _ ⟨p,hp,rfl⟩ w hw
  exact congrArg P.subtype ((hk ▸ hc hp) ⟨w,hWP hw⟩ hw)
end Representation.BinaryConjugationSection
