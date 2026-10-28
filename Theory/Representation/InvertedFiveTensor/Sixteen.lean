module
public import Theory.Representation.InvertedFiveTensor.Scalars

/-!
# Sixteen-element scalars from a fixed-point-free fifth rotation

The recovered four-element field acts through r+r⁻¹. Adjoining a root of
X²+ωX+1 extends these scalars on the same additive carrier, with that root
acting as the original rotation r. The concrete quadratic polynomial has
no root in F₄. Its root generates the resulting field of order sixteen,
and an eight-dimensional binary carrier has dimension two over this field.

The Hermitian containing-component application uses this scalar marking to
refine its actual conjugation action on P/U. This supplies the field input
in the final paragraph of Aschbacher–Smith 8.2.8(1), printed p.719,
refs/quasithin.pdf (1 March 2004 manuscript).
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public section
namespace InvertedFiveTensor.Sixteen
abbrev Field := QuadraticAlgebra F 1 omega
instance noRoot : Fact (∀ r : F, r ^ 2 ≠ 1 + omega * r) := ⟨by decide +kernel⟩
instance fieldFintype : Fintype Field :=
  Fintype.ofEquiv (F × F) (QuadraticAlgebra.equivProd 1 omega).symm
instance fieldCharP : CharP Field 2 :=
  charP_of_injective_algebraMap (algebraMap F Field).injective 2
abbrev root : Field := ⟨0,1⟩
theorem card_field : Nat.card Field = 16 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

/-- The marked rotation generates all recovered scalars. -/
theorem root_generates : Subring.closure ({root} : Set Field) = ⊤ := by
  have hex : ∀ a : Field, ∃ b c d e : Fin 2,
      a = (b.val : Field) + (c.val : Field) * root +
        (d.val : Field) * root^2 + (e.val : Field) * root^3 := by decide +kernel
  apply top_unique
  intro a _
  obtain ⟨b,c,d,e,rfl⟩ := hex a
  let S := Subring.closure ({root} : Set Field)
  have hr : root ∈ S := Subring.subset_closure (Set.mem_singleton root)
  exact S.add_mem (S.add_mem (S.add_mem (natCast_mem S b.val)
    (S.mul_mem (natCast_mem S c.val) hr))
    (S.mul_mem (natCast_mem S d.val) (S.pow_mem hr 2)))
    (S.mul_mem (natCast_mem S e.val) (S.pow_mem hr 3))

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable (σ : Representation (ZMod 2) D V) (hf : ∀ v, σ rot v = v → v = 0)

def scalarMap : letI := fieldModule σ hf
    Field →ₐ[F] Module.End F V := by
  let := fieldModule σ hf
  let r := fieldRepresentation σ hf rot
  refine QuadraticAlgebra.lift ⟨r, ?_⟩
  ext v
  simp only [one_smul, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
  change σ rot (σ rot v) = v + omega • σ rot v
  rw [omega_smul]
  have hpow : (σ rot ^ 4) (σ rot v) = v := by
    change (σ rot ^ 4 * σ rot) v = v
    rw [←pow_succ, ←map_pow,rot_fifth,map_one]
    rfl
  rw [hpow]
  have htwo : v + v = 0 := by
    simpa only [show (1 : ZMod 2) + 1 = 0 by decide, zero_smul, one_smul] using
      (add_smul (1 : ZMod 2) 1 v).symm
  symm
  calc
    _ = σ rot (σ rot v) + (v + v) := by abel
    _ = _ := by rw [htwo,add_zero]

@[instance_reducible] def moduleSixteen : Module Field V :=
  letI := fieldModule σ hf
  Module.compHom _ (scalarMap σ hf).toRingHom

/-- The scalar generator acts as the original fifth rotation. -/
theorem root_smul (v : V) : letI := moduleSixteen σ hf
    root • v = σ rot v := by
  let := fieldModule σ hf
  change (0 : F) • v + (1 : F) • σ rot v = _
  simp only [zero_smul,one_smul,zero_add]

/-- The source eight-space is a plane over the recovered field. -/
theorem finrank_two [Finite V] (hv : Nat.card V = 2^8) :
    letI := moduleSixteen σ hf; Module.finrank Field V = 2 := by
  let := moduleSixteen σ hf
  have hh := Module.natCard_eq_pow_finrank (K := Field) (V := V)
  rw [card_field,hv] at hh
  exact (Nat.pow_right_injective (by decide : 1 < 16)) (show 16 ^ Module.finrank Field V = 16^2 from hh.symm)
end InvertedFiveTensor.Sixteen
