module

public import Theory.Representation.BinaryOffender.CubicRatio
public import Theory.Representation.BinaryOffender.PermutationConjugacy

/-!
# Conjugacy of binary quadratic and cubic actors

The representation operator at a group element intertwines displacement by an
actor and its conjugate. Thus conjugation preserves quadraticity, cubicity,
and the action ratio. These transport lemmas support the Sylow reduction of
Aschbacher–Smith K.3.1.2, printed p.454.
-/

public section
namespace Representation.OrthogonalFourMinus.RankOne.InnerTransport
open Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (A : Subgroup G) (g : G)

theorem quadratic_conj_iff :
    IsQuadratic ρ (A.map (MulAut.conj g).toMonoidHom) ↔ IsQuadratic ρ A := by
  constructor
  · intro h a ha b hb v
    have hh := h (g * a * g⁻¹) ⟨a, ha, rfl⟩ (g * b * g⁻¹) ⟨b, hb, rfl⟩ (ρ g v)
    simpa only [map_mul, Module.End.mul_apply, map_sub, ρ.inv_self_apply] using
      congrArg (ρ g⁻¹) hh
  · rintro h _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ v
    change ρ (g * a * g⁻¹) (ρ (g * b * g⁻¹) v - v) = ρ (g * b * g⁻¹) v - v
    simpa only [map_mul, Module.End.mul_apply, map_sub, ρ.inv_self_apply,
      ρ.self_inv_apply] using congrArg (ρ g) (h a ha b hb (ρ g⁻¹ v))

theorem cubic_conj_iff :
    IsCubic ρ (A.map (MulAut.conj g).toMonoidHom) ↔ IsCubic ρ A := by
  constructor
  · intro h a ha b hb c hc v
    have hh := h (g * a * g⁻¹) ⟨a, ha, rfl⟩ (g * b * g⁻¹) ⟨b, hb, rfl⟩
      (g * c * g⁻¹) ⟨c, hc, rfl⟩ (ρ g v)
    simpa only [displacement, LinearMap.sub_apply, LinearMap.id_apply, map_mul,
      Module.End.mul_apply, map_sub, ρ.inv_self_apply, map_zero] using congrArg (ρ g⁻¹) hh
  · rintro h _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩ v
    change displacement ρ (g * a * g⁻¹)
      (displacement ρ (g * b * g⁻¹) (displacement ρ (g * c * g⁻¹) v)) = 0
    simpa only [displacement, LinearMap.sub_apply, LinearMap.id_apply, map_mul,
      Module.End.mul_apply, map_sub, ρ.inv_self_apply, ρ.self_inv_apply, map_zero] using
        congrArg (ρ g) (h a ha b hb c hc (ρ g⁻¹ v))

theorem ratio_conj [FiniteDimensional (ZMod 2) V] :
    actionRatio ρ (A.map (MulAut.conj g).toMonoidHom) = actionRatio ρ A := by
  rw [actionRatio, fixedCodim_map_conj, rank_map_conj, actionRatio]

end Representation.OrthogonalFourMinus.RankOne.InnerTransport
