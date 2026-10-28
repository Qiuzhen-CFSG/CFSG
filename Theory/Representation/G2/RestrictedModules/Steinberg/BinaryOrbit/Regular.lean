module

public import Theory.Representation.TwoDimensionalOddOrder

/-!
# The nonzero norm criterion for a regular orbit

For a finite p-group in characteristic p, a cyclic orbit whose norm is nonzero
is linearly independent. Indeed, a nonzero kernel in the regular representation
would contain a nonzero fixed vector; all regular fixed vectors are constant.
The same orbit map identifies the fixed vectors in its image with the norm line.
This is the modular regular-representation argument used for the binary G₂ orbit.

Source context: GLS3, 2.8.7 and Example 2.8.10(g). The p-group fixed-vector
input is proved in `Theory.Representation.TwoDimensionalOddOrder`.
-/

public noncomputable section
open scoped BigOperators
namespace Atlas.G2.Restricted.Steinberg.BinaryOrbit.Regular
variable {F G V : Type*} [Field F] [Group G] [Fintype G]
  [AddCommGroup V] [Module F V]

private def regular : Representation F G (G → F) where
  toFun g :=
    { toFun := fun f x => f (g⁻¹ * x)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_one' := by ext f x; simp
  map_mul' g h := by ext f x; simp [mul_assoc]

private def orbitMap (ρ : Representation F G V) (v : V) : (G → F) →ₗ[F] V where
  toFun f := ∑ g, f g • ρ g v
  map_add' f h := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a f := by simp [Finset.smul_sum, mul_smul]

private theorem orbitMap_regular (ρ : Representation F G V) (v : V) (g : G) (f : G → F) :
    orbitMap ρ v (regular g f) = ρ g (orbitMap ρ v f) := by
  simp only [orbitMap, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul]
  apply Fintype.sum_equiv (Equiv.mulLeft g⁻¹)
  intro x
  change f (g⁻¹ * x) • ρ x v = f (g⁻¹ * x) • ρ g (ρ (g⁻¹ * x) v)
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

omit [Fintype G] in
private theorem fixed_regular_constant (f : G → F) (hf : ∀ g, regular g f = f) :
    f = fun _ => f 1 := by
  funext g
  have h := congrFun (hf g) g
  simpa [regular] using h.symm

private theorem orbitMap_injective (hc : ringChar F ≠ 0) (hp : IsPGroup (ringChar F) G)
    (ρ : Representation F G V) (v : V) (hn : (∑ g, ρ g v) ≠ 0) :
    Function.Injective (orbitMap ρ v) := by
  classical
  let W : Subrepresentation (regular (F := F) (G := G)) :=
    { toSubmodule := (orbitMap ρ v).ker
      apply_mem_toSubmodule := by
        intro g f hf
        change orbitMap ρ v (regular g f) = 0
        rw [orbitMap_regular, show orbitMap ρ v f = 0 from hf, map_zero] }
  apply LinearMap.ker_eq_bot.mp
  by_contra hne
  have hW : W.toSubmodule ≠ ⊥ := hne
  let : Nontrivial W.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hW
  obtain ⟨f, hf, hfix⟩ := Representation.pGroup_fix_nonzero_vector hc hp W.toRepresentation
  have hcst := fixed_regular_constant f.val (fun g => congrArg Subtype.val (hfix g))
  have hz : f.val 1 = 0 := by
    have hk : orbitMap ρ v f.val = 0 := f.property
    rw [hcst] at hk
    change (∑ g, f.val 1 • ρ g v) = 0 at hk
    rw [← Finset.smul_sum] at hk
    exact (smul_eq_zero.mp hk).resolve_right hn
  apply hf
  apply Subtype.ext
  change f.val = (0 : G → F)
  exact hcst.trans (funext fun _ => hz)

theorem independent_orbit (hc : ringChar F ≠ 0) (hp : IsPGroup (ringChar F) G)
    (ρ : Representation F G V) (v : V) (hn : (∑ g, ρ g v) ≠ 0) :
    LinearIndependent F (fun g => ρ g v) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro f hf g
  have he : orbitMap ρ v f = orbitMap ρ v 0 := by simpa [orbitMap] using hf
  exact congrFun (orbitMap_injective hc hp ρ v hn he) g


theorem fixed_span_orbit (hc : ringChar F ≠ 0) (hp : IsPGroup (ringChar F) G)
    (ρ : Representation F G V) (v : V) (hn : (∑ g, ρ g v) ≠ 0)
    (w : V) (hw : w ∈ Submodule.span F (Set.range fun g => ρ g v))
    (hfix : ∀ g, ρ g w = w) : ∃ c : F, w = c • ∑ g, ρ g v := by
  classical
  obtain ⟨f, hf⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hw
  have he : orbitMap ρ v f = w := hf
  have hreg : ∀ g, regular g f = f := by
    intro g
    apply orbitMap_injective hc hp ρ v hn
    rw [orbitMap_regular, he, hfix]
  have hconst := fixed_regular_constant f hreg
  refine ⟨f 1, ?_⟩
  rw [← he, hconst]
  simp only [orbitMap, LinearMap.coe_mk, AddHom.coe_mk, Finset.smul_sum]
end Atlas.G2.Restricted.Steinberg.BinaryOrbit.Regular
