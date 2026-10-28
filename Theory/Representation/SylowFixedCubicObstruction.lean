module
public import Theory.GroupTheory.CubicClosureTwoKernel
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# Transporting a Sylow fixed-space cubic obstruction

Conjugacy of Sylow subgroups transports a subgroup fixing the standard
Sylow fixed space to one fixing the supplied Sylow fixed space. The map
is the literal conjugation homomorphism, so cubic-closure nonsolvability
transports without choosing new representation coordinates.
Source application: Aschbacher–Smith13.7.6(5), printed p.939.
-/

@[expose] public section
open Subgroup Representation.BinaryOffender Theory.GroupTheory
namespace Representation
variable {A E : Type*} [Group A] [Finite A] [AddCommGroup E] [Module (ZMod 2) E]

/-- One standard Sylow point fixer supplies the obstruction for every Sylow. -/
theorem cubic_sylow_fixer_not_solvable_of_standard
    (σ : Representation (ZMod 2) A E) (S₀ : Sylow 2 A) (D : Subgroup A)
    (hD : ∀ a ∈ D, ∀ v ∈ fixedSpace σ (S₀ : Subgroup A), σ a v = v)
    (hn : ¬ Group.IsSolvable (closure {a : D | orderOf a = 3}))
    (S : Sylow 2 A) :
    ¬ Group.IsSolvable
      (closure {a : subspaceKernel σ (fixedSpace σ (S : Subgroup A)) ⊤ | orderOf a = 3}) := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq A S S₀
  have hS : (S : Subgroup A).map (MulAut.conj g).toMonoidHom = (S₀ : Subgroup A) := by
    change ((g • S : Sylow 2 A) : Subgroup A) = _
    rw [hg]
  let P := subspaceKernel σ (fixedSpace σ (S : Subgroup A)) ⊤
  let f : D →* P := ((MulAut.conj g⁻¹).toMonoidHom.comp D.subtype).codRestrict P (by
    intro a
    refine ⟨mem_top _,?_⟩
    intro v hv
    have hgv : σ g v ∈ fixedSpace σ (S₀ : Subgroup A) := by
      intro s
      have hm : s.val ∈ (S : Subgroup A).map (MulAut.conj g).toMonoidHom := by
        rw [hS]; exact s.property
      obtain ⟨t,ht,he⟩ := hm
      change σ s.val (σ g v) = σ g v
      rw [←he]
      have hf : σ t v = v := hv ⟨t,ht⟩
      change σ (g*t*g⁻¹) (σ g v) = σ g v
      calc
        σ (g*t*g⁻¹) (σ g v) = σ ((g*t*g⁻¹)*g) v :=
          (LinearMap.congr_fun (σ.map_mul (g*t*g⁻¹) g) v).symm
        _ = σ (g*t) v := by rw [mul_assoc (g*t),inv_mul_cancel,mul_one]
        _ = σ g (σ t v) := LinearMap.congr_fun (σ.map_mul g t) v
        _ = σ g v := congrArg (σ g) hf
    have hf := hD a a.property (σ g v) hgv
    simp only [MonoidHom.comp_apply, Subgroup.subtype_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, inv_inv]
    change σ (g⁻¹*a*g) v = v
    simp only [map_mul,Module.End.mul_apply]
    rw [hf,←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply])
  intro hs
  apply hn
  exact solvable_cubic_closure_of_injective f (by
    intro a b he
    apply Subtype.ext
    exact (MulAut.conj g⁻¹).injective (congrArg (fun x : P => x.val) he)) hs
end Representation
