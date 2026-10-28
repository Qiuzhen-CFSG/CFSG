module

public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.TwoA.KernelDisplacement

/-!
# Squares are fixed modulo the marked involution by their actor stabilizers

An actor preserving the point-radical image of q changes q by an octad
translation. Such a translation has square one and its commutator with q
lies in the original involution line. Thus the actor fixes q-squared
modulo that line. This retains the literal quotient action and is the
group-theoretic input to the natural/dual fixed-space calculation.
-/

public noncomputable section
open Subgroup
open scoped commutatorElement
namespace Sporadic.Mathieu.M24InvolutionCentralizers.TwoA

private theorem translation_square (c : translationKernel) : c^2=1 := by
  apply translationCoordinates.injective
  rw [map_pow,map_one,pow_two]
  apply Multiplicative.toAdd.injective
  change (translationCoordinates c).toAdd+(translationCoordinates c).toAdd=0
  rw [←two_smul (ZMod 2),show (2:ZMod 2)=0 from rfl,zero_smul]

public theorem kernel_square_actor_stabilizer (q : kernel) (g : centralizer2A)
    (hg : pointAction (g*q.val*g⁻¹)=pointAction q.val) :
    (g*(q.val)^2*g⁻¹)*((q.val)^2)⁻¹∈
      zpowers (⟨involution2A,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer2A) := by
  let c := (g*q.val*g⁻¹)*(q.val)⁻¹
  have hc : c∈translationKernel := by
    rw [←pointAction_ker,MonoidHom.mem_ker]
    change pointAction ((g*q.val*g⁻¹)*(q.val)⁻¹)=1
    rw [map_mul,map_inv,hg,mul_inv_cancel]
  have hc2 : c^2=1 := congrArg Subtype.val (translation_square ⟨c,hc⟩)
  have hci : c⁻¹=c := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hc2)
  have hcomm : ⁅c,q.val⁆∈
      zpowers (⟨involution2A,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer2A) := by
    rw [←commutatorElement_inv]
    exact inv_mem (kernel_translation_commutator_le_marked
      (commutator_mem_commutator q.property hc))
  have he : (g*(q.val)^2*g⁻¹)*((q.val)^2)⁻¹=⁅c,q.val⁆ := by
    have hcg : g*q.val*g⁻¹=c*q.val := by dsimp [c]; group
    calc
      (g*(q.val)^2*g⁻¹)*((q.val)^2)⁻¹=
          (g*q.val*g⁻¹)^2*((q.val)^2)⁻¹ := by simp only [pow_two]; group
      _ = (c*q.val)^2*((q.val)^2)⁻¹ := by rw [hcg]
      _ = ⁅c,q.val⁆ := by rw [commutatorElement_def,hci]; simp only [pow_two]; group
  exact he ▸ hcomm

end Sporadic.Mathieu.M24InvolutionCentralizers.TwoA
