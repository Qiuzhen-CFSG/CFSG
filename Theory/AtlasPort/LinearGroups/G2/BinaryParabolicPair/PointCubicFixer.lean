module
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.ResidualCentralizer
public import Theory.ElementaryAbelian.Basic
import all Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.ResidualCentralizer

/-!
# The binary point parabolic has no involution fixing its derived cubics

Conjugate a two-element of the point parabolic into its actual unipotent
Sylow subgroup. Conjugation preserves the hypothesis that it centralizes
all order-three elements of the derived point parabolic. The checked
pair of explicit cubics then has trivial common centralizer there.

This is an intentional internal extension of `ResidualCentralizer`:
`import all` reuses its private two-cubic coordinate certificate without
repeating that finite calculation or exposing its implementation.
`G2BinaryPointCubicFixer` transports the result to the original natural action.
Source: Aschbacher--Smith 14.3.32, printed pp.1003--1004. The concrete
root model retains the licensed ATLAS attribution; see LICENSES/ATLAS.txt.
-/

public section
open Subgroup
namespace Atlas.G2.BinaryParabolicPair
open BinaryCore SevenSylowOvergroups

/-- A point-parabolic involution cannot centralize all its derived cubics. -/
theorem point_involution_eq_one_of_cubic_fixer
    (z : Model (ZMod 2)) (hz : z ∈ secondParabolic) (hz2 : z^2=1)
    (hfix : ∀ a : Model (ZMod 2), a ∈ secondParabolic →
      a ∈ commutator (Model (ZMod 2)) → a^3=1 → z*a=a*z) : z=1 := by
  let P := commonSylow.subtype (show (commonSylow : Subgroup (Model (ZMod 2))) ≤
    secondParabolic from unipotent_le_parabolic)
  let zz : secondParabolic := ⟨z,hz⟩
  let : IsElementaryAbelian 2 (zpowers zz) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (show zz^2=1 from Subtype.ext hz2)
  have hp : IsPGroup 2 (zpowers zz) := IsElementaryAbelian.isPGroup 2 _
  obtain ⟨S,hS⟩ := hp.exists_le_sylow
  obtain ⟨c,hc⟩ := MulAction.exists_smul_eq secondParabolic S P
  have hconj : c*zz*c⁻¹ ∈ (P : Subgroup secondParabolic) := by
    rw [← hc]
    exact show c*zz*c⁻¹ ∈ ((c • S : Sylow 2 secondParabolic) : Subgroup secondParabolic) from ⟨zz,hS (mem_zpowers zz),rfl⟩
  let z' : Model (ZMod 2) := c.val*z*c.val⁻¹
  have hzu : z' ∈ unipotent := hconj
  have hcfix (a : Model (ZMod 2)) (ha : a∈secondParabolic)
      (had : a∈commutator (Model (ZMod 2))) (ha3 : a^3=1) : z'*a=a*z' := by
    have hconjP := secondParabolic.mul_mem
      (secondParabolic.mul_mem (secondParabolic.inv_mem c.property) ha) c.property
    have hconjD := (inferInstance : (commutator (Model (ZMod 2))).Normal).conj_mem
      a had c.val⁻¹
    have he := hfix (c.val⁻¹*a*c.val) hconjP (by simpa using hconjD) (by
      simpa only [map_pow,map_one,MulAut.conj_apply,inv_inv] using
        congrArg (MulAut.conj c.val⁻¹) ha3)
    dsimp [z']
    have he' := congrArg (fun x : Model (ZMod 2) => c.val*x*c.val⁻¹) he
    simpa only [mul_assoc,inv_mul_cancel_left,mul_inv_cancel_left,mul_inv_cancel,mul_one] using he'
  have he : z'=1 := unipotent_two_cubic_fixer hzu
    (hcfix movingActor movingActor_mem movingActor_mem_derived movingActor_cube)
    (hcfix conjugateMovingActor
      (secondParabolic.mul_mem (secondParabolic.mul_mem
        (unipotent_le_parabolic sylowGenerator_mem.1) movingActor_mem)
          (secondParabolic.inv_mem (unipotent_le_parabolic sylowGenerator_mem.1)))
      conjugateMovingActor_mem_derived (by
        unfold conjugateMovingActor
        rw [conj_pow,movingActor_cube,mul_one,mul_inv_cancel]))
  exact (MulAut.conj c.val).injective (he.trans (map_one _).symm)
end Atlas.G2.BinaryParabolicPair
