module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.PointCases.Binary
public import Theory.Representation.BinaryOffender.QuadraticQuotient
public import Theory.GroupTheory.PCoreImage

/-!
# Point cores under central quotients

If an equivariant quotient has pointwise fixed kernel, the stabilizer of a
lift is normal in the stabilizer of its image. Their intrinsic two-cores
therefore have the required containment. The projected point is nonzero
whenever the original stabilizer is proper. Fixed codimension decreases
under a surjective intertwiner, so the binary natural point-core calculation
excludes strong offenders on every such central extension.

This covers the natural and nonsplit central-extension alternatives in
B.5.1 for L₃(2), without assuming a point-core bound or a position for the
projected vector. Source: Aschbacher–Smith, combined manuscript, printed
pp.99–103 and p.1145.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination
open ModelExclusions
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.PointCases.Quotients
variable {K D V W : Type*} [Group K] [Group D]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]

theorem strong_map_quotient [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) K V) (σ : Representation (ZMod 2) D W)
    (e : K ≃* D) (f : V →ₗ[ZMod 2] W) (hfs : Function.Surjective f)
    (hf : ∀ g v, f (ρ g v) = σ (e g) (f v))
    {A : Subgroup K} (hs : IsStrongOffender ρ A) :
    IsStrongOffender σ (A.map e.toMonoidHom) := by
  have hq : IsStrongOffender (σ.comp e.toMonoidHom) A :=
    ⟨hs.1, (fixedCodim_le_of_equivariant_surjection ρ (σ.comp e.toMonoidHom)
      f hfs hf A).trans_lt hs.2⟩
  exact strong_map_equivariant (σ.comp e.toMonoidHom) σ e.toMonoidHom e.injective
    (LinearEquiv.refl _ _) (fun _ _ => rfl) hq

theorem image_point_ne_zero_of_central_kernel
    (ρ : Representation (ZMod 2) K V) (f : V →ₗ[ZMod 2] W)
    (hker : ∀ v, f v = 0 → ∀ g, ρ g v = v)
    (z : V) (hp : pointStabilizer ρ z ≠ ⊤) : f z ≠ 0 := by
  intro hz
  apply hp
  exact top_unique (fun g _ => hker z hz g)

/-- The stabilizer of a lift is normal in the stabilizer of its image
when the quotient kernel is fixed pointwise. This is relative normality. -/
theorem point_core_le_quotient_core
    (ρ : Representation (ZMod 2) K V) (σ : Representation (ZMod 2) K W)
    (f : V →ₗ[ZMod 2] W) (hf : ∀ g v, f (ρ g v) = σ g (f v))
    (hc : ∀ v, f v = 0 → ∀ g, ρ g v = v) (z : V) :
    localTwoCore (pointStabilizer ρ z) ≤ localTwoCore (pointStabilizer σ (f z)) := by
  let P := pointStabilizer ρ z
  let Q := pointStabilizer σ (f z)
  have hPQ : P ≤ Q := by
    intro a ha
    change σ a (f z) = f z
    rw [← hf]
    exact congrArg f ha
  have hfix (b : K) (hb : b ∈ Q) (a : K) (ha : a ∈ P) :
      ρ a (ρ b z) = ρ b z := by
    have hd : f (ρ b z - z) = 0 := by
      rw [map_sub,hf]
      exact sub_eq_zero.mpr hb
    have hh := hc _ hd a
    change ρ a z = z at ha
    simpa only [map_sub,ha,sub_left_inj] using hh
  have hn : Q ≤ normalizer (P : Set K) := by
    apply le_normalizer_iff.mpr
    intro g hg a ha
    change ρ (g*a*g⁻¹) z = z
    rw [map_mul,map_mul,Module.End.mul_apply,Module.End.mul_apply,
      hfix g⁻¹ (Q.inv_mem hg) a ha]
    rw [← Module.End.mul_apply,← map_mul,mul_inv_cancel,map_one]
    rfl
  exact Subgroup.pCoreIn_mono_of_normalizes hPQ hn

theorem binary_central_quotient_exclusion [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) K V) (e : K ≃* Matrix.PSL3Two.SL)
    (f : V →ₗ[ZMod 2] PointCases.Binary.Vector) (hfs : Function.Surjective f)
    (hf : ∀ g v, f (ρ g v) = PointCases.Binary.natural (e g) (f v))
    (hc : ∀ v, f v = 0 → ∀ g, ρ g v = v)
    (z : V) (hp : pointStabilizer ρ z ≠ ⊤)
    {A : Subgroup K} (hA : A ≤ localTwoCore (pointStabilizer ρ z)) :
    ¬ IsStrongOffender ρ A := by
  intro hs
  have hz := image_point_ne_zero_of_central_kernel ρ f hc z hp
  have hcore := point_core_le_quotient_core ρ
    (PointCases.Binary.natural.comp e.toMonoidHom) f hf hc z
  have hm := Subgroup.map_mono (f := e.toMonoidHom) (hA.trans hcore)
  rw [localTwoCore_map_equiv, pointStabilizer_map_equivariant
    (PointCases.Binary.natural.comp e.toMonoidHom) PointCases.Binary.natural e
    (LinearEquiv.refl _ _) (fun _ _ => rfl)] at hm
  exact PointCases.Binary.not_strong_point (f z) hz hm
    (strong_map_quotient ρ PointCases.Binary.natural e f hfs hf hs)

variable [FiniteDimensional (ZMod 2) V]

theorem binary_central_natural_exclusion
    (ρ : Representation (ZMod 2) K V) (e : K ≃* Matrix.PSL3Two.SL)
    (C : Subrepresentation ρ) (hc : C.toSubmodule ≤ fixedSpace ρ ⊤)
    (E : (V ⧸ C.toSubmodule) ≃ₗ[ZMod 2] PointCases.Binary.Vector)
    (hE : ∀ g v, E (C.quotientRepresentation g v) = PointCases.Binary.natural (e g) (E v))
    (z : V) (hp : pointStabilizer ρ z ≠ ⊤)
    {A : Subgroup K} (hA : A ≤ localTwoCore (pointStabilizer ρ z)) :
    ¬ IsStrongOffender ρ A := by
  let f := E.toLinearMap.comp C.toSubmodule.mkQ
  have he : ∀ g v, f (ρ g v) = PointCases.Binary.natural (e g) (f v) :=
    fun g v => hE g (C.toSubmodule.mkQ v)
  have hs : Function.Surjective f := E.surjective.comp C.toSubmodule.mkQ_surjective
  apply binary_central_quotient_exclusion ρ e f hs he _ z hp hA
  intro v hv g
  have hq : C.toSubmodule.mkQ v = 0 := E.injective (hv.trans (map_zero E).symm)
  exact hc ((Submodule.Quotient.mk_eq_zero _).mp hq) ⟨g,mem_top g⟩

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.PointCases.Quotients
