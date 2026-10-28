module
public import Theory.Representation.Mathieu.M22James.Ambient
public import Theory.LinearAlgebra.BinaryTriangularPGroup
public import Theory.Representation.TwoDimensionalOddOrder
public import Theory.Representation.SylowInvariantDimension
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# The fixed line of a Sylow subgroup on the triple Mathieu module

Four explicit words in the certified ATLAS generators preserve a complete
binary flag. The faithful triangular action therefore puts them in a
two-subgroup. Eleven independent rows of their displacement matrices bound
its fixed space by one dimension. A Sylow overgroup has a nonzero fixed
vector in characteristic two; Sylow conjugacy gives the same fixed dimension
for every Sylow subgroup of the genuine covering extension 3.M₂₂.2.

The word evaluations, basis inverses, triangularity and rank minor are
kernel-checked finite certificates. No enumeration of the whole matrix group
or assumption about its Sylow fixed space is used. The original ATLAS matrices
and attribution are retained in the imported LinearModel/source/ files.
Source: Aschbacher–Smith H.12.1(9), printed p.394, used in 14.7.36,
printed p.1059; refs/quasithin.pdf.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Janko4.InvolutionCentralizers.First.QuotientExtension
open scoped Matrix
namespace Sporadic.Mathieu.M22TripleCover.SylowFixed
open Ambient
private def c : actionGroup := ⟨unitC,unitC_mem_actionGroup⟩
private def d : actionGroup := ⟨unitD,unitD_mem_actionGroup⟩
private def a : actionGroup := d⁻¹*c*d^2*c*d
private def b : actionGroup := d*c*d⁻¹*(c*d)^3*d*(c*d⁻¹)^2*c*d*c*(d*c*d)^2*d
private def z : actionGroup := (d*c*d)^3*c*d*c*d⁻¹*c*(d*c*d)^3
private def t : actionGroup := (d*c*d)^2*(c*d)^2*d*c*d⁻¹*c*d*(d*c)^2*d^2*(c*d⁻¹)^2*c*d^2*c*d⁻¹*c
private def words : Fin 4 → actionGroup := ![a,b,z,t]
private def matrices : Fin 4 → Matrix12 := ![
  fromRows ![509,1513,4,256,148,164,64,128,8,624,147,3095],
  fromRows ![916,1735,1130,556,1265,175,858,922,1505,1761,1818,3781],
  fromRows ![1310,1382,1376,558,1530,174,1913,678,786,654,1217,2671],
  fromRows ![916,1735,1129,558,472,174,1648,14,1432,38,1888,3819]]
private theorem words_matrix (i : Fin 4) : ((words i : Matrix12ˣ) : Matrix12) = matrices i := by
  fin_cases i <;> decide +kernel

private def basis : Matrix12 := fromRows ![293,100,1842,192,1072,768,1704,1696,128,1024,512,2048]
private def basisInv : Matrix12 := fromRows ![1323,52,1674,192,1424,1920,264,256,1056,1024,512,2048]
private def basisUnit : Matrix12ˣ where
  val := basis
  inv := basisInv
  val_inv := by decide +kernel
  inv_val := by decide +kernel

private def coordinates : actionGroup →* Matrix12 :=
  (Units.coeHom Matrix12).comp ((MulAut.conj basisUnit⁻¹).toMonoidHom.comp actionGroup.subtype)
private theorem coordinates_injective : Function.Injective coordinates :=
  Units.val_injective.comp ((MulAut.conj basisUnit⁻¹).injective.comp actionGroup.subtype_injective)
private def lowerMonoid : Submonoid actionGroup :=
  (Matrix.blockTriangularSubsemiring (ZMod 2) (OrderDual.toDual : Fin 12 → OrderDual (Fin 12))).toSubmonoid.comap coordinates
private def lower : Subgroup actionGroup where
  carrier := lowerMonoid
  one_mem' := lowerMonoid.one_mem
  mul_mem' := lowerMonoid.mul_mem
  inv_mem' := by
    intro a ha
    change a⁻¹ ∈ lowerMonoid
    rw [←one_mul a⁻¹,←pow_one a,←pow_orderOf_eq_one a,←pow_sub a (orderOf_pos a)]
    exact lowerMonoid.pow_mem ha _
private theorem lower_two : IsPGroup 2 lower := by
  apply IsPGroup.of_injective_binary_lowerTriangular (coordinates.comp lower.subtype)
    (coordinates_injective.comp lower.subtype_injective)
  intro g i j hij
  exact g.property hij
private theorem words_mem (i : Fin 4) : words i ∈ lower := by
  change (basisInv * (((words i : actionGroup) : Matrix12ˣ) : Matrix12) * basis).BlockTriangular
    (OrderDual.toDual : Fin 12 → OrderDual (Fin 12))
  rw [words_matrix]
  revert i
  decide +kernel

private def which : Fin 12 → Fin 4 := ![0,0,0,0,1,1,1,1,2,2,3,0]
private def row : Fin 12 → Fin 12 := ![0,1,3,4,0,1,2,3,4,11,11,0]
private def joint : Matrix12 := fun i j => (matrices (which i) - 1) (row i) j
private def operations : Matrix (Fin 11) (Fin 12) (ZMod 2) :=
  fun i j => if (![258,166,695,332,1304,1917,616,703,328,1354,1544] : Fin 11 → ℕ) i |>.testBit j.val then 1 else 0
private theorem rank_joint : 11 ≤ joint.rank := by
  have hp : (operations * joint).submatrix id (fun i : Fin 11 => i.castSucc) = 1 := by
    decide +kernel
  calc
    11 = (1 : Matrix (Fin 11) (Fin 11) (ZMod 2)).rank := by simp
    _ = ((operations * joint).submatrix id (fun i : Fin 11 => i.castSucc)).rank := congrArg Matrix.rank hp.symm
    _ ≤ (operations * joint).rank := Matrix.rank_submatrix_le _ _ _
    _ ≤ joint.rank := Matrix.rank_mul_le_right _ _

private theorem lower_fixed_bound : Module.finrank (ZMod 2) (fixedSpace binaryAction lower) ≤ 1 := by
  have hk : fixedSpace binaryAction lower ≤ LinearMap.ker (Matrix.toLin' joint) := by
    intro v hv
    change joint *ᵥ v = 0
    funext i
    have hi := hv ⟨words (which i),words_mem (which i)⟩
    change (((words (which i) : Matrix12ˣ) : Matrix12) *ᵥ v) = v at hi
    rw [words_matrix] at hi
    have hz : (matrices (which i) - 1) *ᵥ v = 0 := by
      rw [Matrix.sub_mulVec,hi,Matrix.one_mulVec,sub_self]
    exact congrFun hz (row i)
  have hle := Submodule.finrank_mono hk
  have hr := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' joint)
  have hrank : Module.finrank (ZMod 2) (LinearMap.range (Matrix.toLin' joint)) = joint.rank := rfl
  rw [hrank] at hr
  have hd : Module.finrank (ZMod 2) (Fin 12 → ZMod 2) = 12 := by simp
  rw [hd] at hr
  change Module.finrank (ZMod 2) (fixedSpace binaryAction lower) ≤
    Module.finrank (ZMod 2) (LinearMap.ker (Matrix.toLin' joint)) at hle
  have := rank_joint
  omega

/-- Every Sylow two-subgroup of the genuine matrix covering extension has
exactly a line of fixed vectors in the binary twelve-dimensional module. -/
theorem sylow_fixed_finrank (S : Sylow 2 actionGroup) :
    Module.finrank (ZMod 2) (fixedSpace binaryAction (S : Subgroup actionGroup)) = 1 := by
  obtain ⟨P,hP⟩ := lower_two.exists_le_sylow
  have he : Module.finrank (ZMod 2) (fixedSpace binaryAction (S : Subgroup actionGroup)) =
      Module.finrank (ZMod 2) (fixedSpace binaryAction (P : Subgroup actionGroup)) :=
    Representation.finrank_invariants_sylow_eq binaryAction 2 S P
  have hle : fixedSpace binaryAction (P : Subgroup actionGroup) ≤ fixedSpace binaryAction lower :=
    fun v hv x => hv ⟨x,hP x.property⟩
  have hu : Module.finrank (ZMod 2) (fixedSpace binaryAction (P : Subgroup actionGroup)) ≤ 1 :=
    (Submodule.finrank_mono hle).trans lower_fixed_bound
  obtain ⟨v,hv,hfix⟩ := pGroup_fix_nonzero_vector
    (by rw [ZMod.ringChar_zmod_n]; decide : ringChar (ZMod 2) ≠ 0)
    (by simpa only [ZMod.ringChar_zmod_n] using S.isPGroup') (binaryAction.comp (S : Subgroup actionGroup).subtype)
  have hn : fixedSpace binaryAction (S : Subgroup actionGroup) ≠ ⊥ := by
    intro hh
    have hm : v ∈ fixedSpace binaryAction (S : Subgroup actionGroup) := hfix
    rw [hh] at hm
    exact hv hm
  have hl : Module.finrank (ZMod 2) (fixedSpace binaryAction (S : Subgroup actionGroup)) ≠ 0 :=
    fun hz => hn (Submodule.finrank_eq_zero.mp hz)
  omega
end Sporadic.Mathieu.M22TripleCover.SylowFixed
