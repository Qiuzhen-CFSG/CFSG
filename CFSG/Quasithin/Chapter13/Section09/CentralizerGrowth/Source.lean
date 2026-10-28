module
public import CFSG.Quasithin.Chapter13.Section09.CentralizerGrowth.AxisFusion
public import CFSG.Quasithin.Chapter13.Section09.CentralizerGrowth.SecondFactor
public import CFSG.Quasithin.Chapter13.Section09.CentralizerGrowth.ResidualFusion
public import CFSG.Quasithin.Chapter13.Section09.LocalGeometry.LocalCentralizer
import all Theory.GroupTheory.WreathDiagonalCentralizer

/-!
# Strict centralizer growth in source 13.9.5

Assuming C_G(z)=T constructs the full orthogonal normalizer action on the
original B. Its nonsingular orbit gives the precise axis fusion in J(T), and
its cubic actor places the second dihedral factor in O²(C_G(t)). The residual
transfer theorem then fuses every involution of that residual with t. Thompson
transfer applied to the original swapping involution contradicts the diagonal
involution in O²(C_M(s)). Consequently T<C_G(z), and C_G(z) is not contained in M.

The internal diagonal import identifies its literal image with the original z;
this keeps the established diagonal module's public boundary unchanged.
Source: Aschbacher--Smith, 13.9.5, printed pp.970--971 (PDF pp.987--988).
-/

public section
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup SymmetricFourWreath
variable {G : Type*} [Group G] [Finite G] {d : Configuration G} (m : Marking d)

omit [Finite G] in
private theorem local_z_mem_residual_s :
    m.z∈(pResidual 2 (d.M⊓centralizer ({m.s}:Set G):Subgroup G)).map
      (d.M⊓centralizer ({m.s}:Set G)).subtype := by
  let c:S4:=Equiv.swap 1 2
  let f:=Theory.GroupTheory.WreathDiagonal.localDiagonal d.M m.equiv (m.equiv.symm swap)
    turn (m.equiv.apply_symm_apply _)
  have hz : square (DihedralGroup.r 2)=
      c*Theory.GroupTheory.WreathDiagonal.doubleTransposition*c⁻¹ := by decide +kernel
  have hr : square (DihedralGroup.r 2)∈pResidual 2 S4 := by
    rw [hz]
    exact (inferInstance : (pResidual 2 S4).Normal).conj_mem _
      Theory.GroupTheory.WreathDiagonal.doubleTransposition_mem_twoResidual c
  have hm := map_pResidual_le 2 f (mem_map_of_mem f hr)
  refine ⟨f (square (DihedralGroup.r 2)),hm,?_⟩
  change (m.equiv.symm (Theory.GroupTheory.WreathDiagonal.diagonal (square (DihedralGroup.r 2))):G)=m.z
  have he : Theory.GroupTheory.WreathDiagonal.diagonal (square (DihedralGroup.r 2))=
      SymmetricFourWreath.z := by
    apply RegularWreathProduct.ext
    · funext i
      exact (SymmetricFourWreath.z_left i).symm
    · decide +kernel
  rw [he]
  rfl

theorem centralizer_growth {𝒦 : GroupClass} (hG:IsSimpleQTKE 𝒦 G) :
    (d.T:Subgroup G)<centralizer ({m.z}:Set G) ∧ ¬centralizer ({m.z}:Set G)≤d.M := by
  have hne : (d.T:Subgroup G)≠centralizer ({m.z}:Set G) := by
    intro he
    have hC:=he.symm
    have haxes:=m.axis_fusion_of_centralizer_eq hG hC
    have hsecond:=m.second_factor_le_residual_of_centralizer_eq hG hC
    apply CentralizerGrowth.false_of_centralizer_residual_fusion hG d m.dihedralBase
      m.dihedralBase_index m.s_mem_sylow
      (orderOf_eq_prime (by simpa only [pow_two] using m.s_sq) m.s_ne_one)
      m.not_isConj_t_z (m.not_isConj_z_s_of_centralizer_eq hC)
    · exact m.dihedral_involution_two_classes hG hC
    · exact ⟨m.z,m.local_z_mem_residual_s,m.z_order,IsConj.refl _⟩
    · exact m.residual_involution_fusion_of_axes haxes hsecond
  have hlt:=lt_of_le_of_ne m.z_central_sylow hne
  refine ⟨hlt,?_⟩
  intro hCM
  exact (not_le_of_gt hlt) (m.local_centralizer_z ▸ le_inf le_rfl hCM)
end CFSG.Quasithin.Chapter13.Section09.Marking
