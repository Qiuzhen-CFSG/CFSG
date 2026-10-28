module
public import Theory.Representation.BinaryPermutation.EightPointSylow
public import Theory.Representation.BinaryPermutation.OrbitSizeSeparation

/-!
# Pair parity on an A₈ point-stabilizer fixed space

A weight-two stabilizer contains the product of four disjoint transpositions.
Conjugate this involution into the supplied Sylow. A word fixed by it is
constant on four pairs, and the sum of the four pair values is one for weights
two and six. Transporting that sum gives a linear functional on the original
coordinates. No order or dimension of the whole fixed space is assumed.

Source application: the corrected terminal argument in Aschbacher--Smith
12.2.16, printed p.800. This replaces the printed hyperplane assertion by
parity on the literal point-fixed core.
-/

public section
open Subgroup Representation
open scoped Pointwise
namespace BinaryPermutation.EightPointSylowParity
abbrev Ω := Fin 8
abbrev S8 := Equiv.Perm Ω
private def switches : S8 := Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5 * Equiv.swap 6 7
private def base : Full Ω := ![1,1,0,0,0,0,0,0]
private def parity : Full Ω →ₗ[ZMod 2] ZMod 2 :=
  LinearMap.proj (R := ZMod 2) (φ := fun _ : Ω => ZMod 2) 0 +
    LinearMap.proj 2 + LinearMap.proj 4 + LinearMap.proj 6
private theorem base_weight : wordWeight base = 2 := by decide +kernel
private theorem switches_even : switches ∈ alternatingGroup Ω := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide +kernel
private theorem switches_square : switches ^ 2 = 1 := by decide +kernel
private theorem switches_base : representation Ω switches base = base := by decide +kernel
private theorem parity_of_weight (w : Full Ω)
    (hf : representation Ω switches w = w)
    (hw : wordWeight w = 2 ∨ wordWeight w = 6) : parity w = 1 := by
  have h01 : w 1 = w 0 := congrFun hf 0
  have h23 : w 3 = w 2 := congrFun hf 2
  have h45 : w 5 = w 4 := congrFun hf 4
  have h67 : w 7 = w 6 := congrFun hf 6
  have he : w = ![w 0,w 0,w 2,w 2,w 4,w 4,w 6,w 6] := by
    ext i
    fin_cases i <;> simp [h01,h23,h45,h67]
  have hp : ∀ a b c d : ZMod 2,
      (wordWeight ![a,a,b,b,c,c,d,d] = 2 ∨ wordWeight ![a,a,b,b,c,c,d,d] = 6) →
      a + b + c + d = 1 := by decide +kernel
  exact hp _ _ _ _ (he ▸ hw)
private theorem inv_action (g : S8) (w : Full Ω) :
    representation Ω g⁻¹ (representation Ω g w) = w := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
private theorem conjugate_fixed (g a : S8) (w : Full Ω)
    (hw : representation Ω (g * a * g⁻¹) w = w) :
    representation Ω a (representation Ω g⁻¹ w) = representation Ω g⁻¹ w := by
  have hh := congrArg (representation Ω g⁻¹) hw
  simpa only [map_mul, Module.End.mul_apply, inv_action] using hh

/-- On point-stabilizer Sylow fixed words, weights two and six have odd pair parity. -/
theorem exists_weight_parity (v : Full Ω) (hw : wordWeight v = 2)
    (P : Sylow 2 (EightPointSylow.stabilizer v)) :
    ∃ f : Full Ω →ₗ[ZMod 2] ZMod 2,
      ∀ w : Full Ω, w ∈ Representation.BinaryOffender.fixedSpace
        (alternatingRepresentation Ω)
        ((P : Subgroup (EightPointSylow.stabilizer v)).map
          (EightPointSylow.stabilizer v).subtype) →
        (wordWeight w = 2 ∨ wordWeight w = 6) → f w = 1 := by
  obtain ⟨g,hg⟩ := exists_permutation_of_weight base v (base_weight.trans hw.symm)
  let a : alternatingGroup Ω := ⟨g * switches * g⁻¹,
    (inferInstance : (alternatingGroup Ω).Normal).conj_mem switches switches_even g⟩
  have ha : a ∈ EightPointSylow.stabilizer v := by
    change representation Ω (g * switches * g⁻¹) v = v
    rw [← hg]
    simp only [map_mul, Module.End.mul_apply, inv_action, switches_base]
  let b : EightPointSylow.stabilizer v := ⟨a,ha⟩
  have hb2 : b ^ 2 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    change (g * switches * g⁻¹) ^ 2 = 1
    rw [← MulAut.conj_apply, ← map_pow, switches_square, map_one]
  have hp : IsPGroup 2 (zpowers b) :=
    (IsElementaryAbelian.zpowers_of_pow_eq_one hb2).isPGroup 2 _
  obtain ⟨Q,hQ⟩ := hp.exists_le_sylow
  obtain ⟨c,hc⟩ := MulAction.exists_smul_eq (EightPointSylow.stabilizer v) Q P
  have hcb : c * b * c⁻¹ ∈ (P : Subgroup _) := by
    rw [← hc]
    exact mem_map_of_mem (MulAut.conj c).toMonoidHom (hQ (mem_zpowers b))
  let k : S8 := c.val.val * g
  refine ⟨parity.comp (representation Ω k⁻¹), ?_⟩
  intro w hfix hweight
  have hf := hfix ⟨(c * b * c⁻¹).val, mem_map_of_mem _ hcb⟩
  have he : (c * b * c⁻¹).val.val = k * switches * k⁻¹ := by
    change c.val.val * (g * switches * g⁻¹) * c.val.val⁻¹ = _
    dsimp [k]
    group
  change representation Ω (c * b * c⁻¹).val.val w = w at hf
  rw [he] at hf
  exact parity_of_weight _ (conjugate_fixed k switches w hf)
    (by simpa only [wordWeight_permute] using hweight)
end BinaryPermutation.EightPointSylowParity
