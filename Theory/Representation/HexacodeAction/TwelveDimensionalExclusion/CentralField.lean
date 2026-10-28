module

public import Theory.Representation.HexacodeAction.TerminalIrreducible
public import Theory.Representation.SubrepresentationLattice

/-!
# The central field for arbitrary irreducible even-cover modules

The central cubic has no fixed vectors on a faithful irreducible binary
module. Its quadratic relation equips that same additive group with F₄
scalars. The action remains faithful and irreducible, and binary dimension
is twice field dimension. No extension to the odd cover, absolute
irreducibility, or field-of-definition assumption is required.

This is the intrinsic scalar reduction for the degree exclusion used in
Aschbacher–Smith K.1.3, printed p.453. The quadratic-field construction follows
`SixDimensionalRecognition/CentralField`, but works on the even cover alone
and in arbitrary dimension. The concrete carrier and central mark are the
licensed ATLAS ports reexported by `HexacodeAction.Field`.
-/

@[expose] public section

open Atlas.Codes
namespace Representation.Hexacode.TwelveDimensional

variable {V : Type*} [AddCommGroup V] [Module Bit V]
  (ρ : Representation Bit HexEvenAutomorphisms V)

/-- Centrality on the actual even-cover carrier. -/
theorem central_commutes (g : HexEvenAutomorphisms) : hexEvenZ * g = g * hexEvenZ := by
  apply Subtype.ext
  exact (mul_inv_eq_iff_eq_mul.mp (hex_conjugation_even g.val g.property)).symm

/-- Every even operator commutes with the cubic operator. -/
theorem scalar_commutes (g : HexEvenAutomorphisms) (v : V) :
    ρ hexEvenZ (ρ g v) = ρ g (ρ hexEvenZ v) := by
  simpa only [map_mul, Module.End.mul_apply] using
    congrArg (fun x => ρ x v) (central_commutes g)

/-- Schur's lemma makes the nontrivial central cubic fixed-point free. -/
theorem scalar_fixed_iff (hf : Function.Injective ρ) [IsIrreducible ρ] (v : V) :
    ρ hexEvenZ v = v ↔ v = 0 := by
  let f : IntertwiningMap ρ ρ :=
    { toLinearMap := ρ hexEvenZ - 1
      isIntertwining' := by
        intro g
        ext w
        change ρ hexEvenZ (ρ g w) - ρ g w = ρ g (ρ hexEvenZ w - w)
        rw [map_sub, scalar_commutes] }
  have hn : f ≠ 0 := by
    intro h
    have hz : hexEvenZ = 1 := hf (by
      ext w
      exact (sub_eq_zero.mp (congrArg (fun q : IntertwiningMap ρ ρ => q w) h)).trans
        (by simp))
    have ho := hexEvenZ_order
    rw [hz, orderOf_one] at ho
    contradiction
  have hi := (IsIrreducible.injective_or_eq_zero f).resolve_right hn
  constructor
  · intro hv
    apply hi
    change ρ hexEvenZ v - v = ρ hexEvenZ 0 - 0
    simp only [hv, map_zero, sub_self]
  · rintro rfl
    exact map_zero _

/-- The actual central operator satisfies the defining relation of F₄. -/
theorem scalar_quadratic (hf : Function.Injective ρ) [IsIrreducible ρ] :
    ρ hexEvenZ ^ 2 + ρ hexEvenZ + 1 = 0 := by
  have hp : ρ hexEvenZ ^ 3 = 1 := by
    rw [← map_pow, ← hexEvenZ_order, pow_orderOf_eq_one, map_one]
  have hc (v : V) : ρ hexEvenZ (ρ hexEvenZ (ρ hexEvenZ v)) = v := by
    simpa only [pow_succ, pow_zero, one_mul, Module.End.mul_apply,
      Module.End.one_apply] using LinearMap.congr_fun hp v
  ext v
  apply (scalar_fixed_iff ρ hf _).mp
  change ρ hexEvenZ (ρ hexEvenZ (ρ hexEvenZ v) + ρ hexEvenZ v + v) =
    ρ hexEvenZ (ρ hexEvenZ v) + ρ hexEvenZ v + v
  rw [map_add, map_add, hc]
  abel

variable (hq : ρ hexEvenZ ^ 2 + ρ hexEvenZ + 1 = 0)

/-- Evaluate the quadratic field at the central operator. -/
noncomputable def scalarMap : F →ₐ[Bit] Module.End Bit V :=
  QuadraticAlgebra.lift ⟨ρ hexEvenZ, by
    have he : ρ hexEvenZ ^ 2 = -(ρ hexEvenZ + 1) := by
      apply eq_neg_of_add_eq_zero_left
      simpa only [add_assoc] using hq
    have hn (f : Module.End Bit V) : -f = f := by
      rw [← neg_one_smul Bit, show (-1 : Bit) = 1 by decide, one_smul]
    simpa only [pow_two, hn, one_smul, add_comm] using he⟩

/-- F₄ scalars on the original additive group. -/
@[instance_reducible] noncomputable def fieldModule : Module F V :=
  Module.compHom V (scalarMap ρ hq).toRingHom

/-- The new scalars extend the given binary scalars. -/
theorem fieldTower : letI := fieldModule ρ hq
    IsScalarTower Bit F V := by
  let := fieldModule ρ hq
  constructor
  intro r a v
  change scalarMap ρ hq (r • a) v = r • (scalarMap ρ hq a v)
  rw [map_smul]
  rfl

/-- The original even operators are linear for the recovered field. -/
noncomputable def fieldRepresentation : letI := fieldModule ρ hq
    Representation F HexEvenAutomorphisms V := by
  let := fieldModule ρ hq
  refine { toFun := fun g => { (ρ g).toAddHom with map_smul' := ?_ }
           map_one' := ?_, map_mul' := ?_ }
  · intro a v
    change ρ g (a.re • v + a.im • ρ hexEvenZ v) =
      a.re • ρ g v + a.im • ρ hexEvenZ (ρ g v)
    rw [map_add, map_smul, map_smul, scalar_commutes]
  · ext v
    exact LinearMap.congr_fun ρ.map_one v
  · intro g h
    ext v
    exact LinearMap.congr_fun (ρ.map_mul g h) v

/-- The recovered representation has the prescribed central character. -/
theorem fieldRepresentation_scalar (v : V) : letI := fieldModule ρ hq
    fieldRepresentation ρ hq hexEvenZ v = omega • v := by
  change ρ hexEvenZ v = (0 : Bit) • v + (1 : Bit) • ρ hexEvenZ v
  simp only [zero_smul, one_smul, zero_add]

/-- Faithfulness is unchanged by recovering scalars. -/
theorem fieldRepresentation_injective (hf : Function.Injective ρ) :
    letI := fieldModule ρ hq
    Function.Injective (fieldRepresentation ρ hq) := by
  let := fieldModule ρ hq
  intro g h he
  apply hf
  ext v
  exact LinearMap.congr_fun he v

/-- Irreducibility is unchanged in the direction needed for the exclusion. -/
theorem fieldRepresentation_irreducible [IsIrreducible ρ] :
    letI := fieldModule ρ hq
    IsIrreducible (fieldRepresentation ρ hq) := by
  let := fieldModule ρ hq
  let := fieldTower ρ hq
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro h
    exact bot_ne_top (congrArg Subrepresentation.toSubmodule h)
  intro P
  let Q : Subrepresentation ρ :=
    { toSubmodule := P.toSubmodule.restrictScalars Bit
      apply_mem_toSubmodule := fun g _ hv => P.apply_mem_toSubmodule g hv }
  rcases eq_bot_or_eq_top Q with h | h
  · left
    ext v
    change v ∈ Q ↔ v ∈ (⊥ : Subrepresentation (fieldRepresentation ρ hq))
    rw [h]
    rfl
  · right
    ext v
    change v ∈ Q ↔ v ∈ (⊤ : Subrepresentation (fieldRepresentation ρ hq))
    rw [h]
    rfl

/-- The binary and recovered field dimensions have their exact tower ratio. -/
theorem field_finrank : letI := fieldModule ρ hq
    2 * Module.finrank F V = Module.finrank Bit V := by
  let := fieldModule ρ hq
  let := fieldTower ρ hq
  have h := Module.finrank_mul_finrank Bit F V
  rwa [QuadraticAlgebra.finrank_eq_two] at h

/-- Binary finite dimension implies finite dimension for the recovered field. -/
theorem field_finite [Module.Finite Bit V] : letI := fieldModule ρ hq
    Module.Finite F V := by
  let := fieldModule ρ hq
  let := fieldTower ρ hq
  exact Module.Finite.of_restrictScalars_finite Bit F V

end Representation.Hexacode.TwelveDimensional
