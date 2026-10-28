module
public import Theory.SpecificGroups.AlternatingFiveInvolutionCover
public import Theory.GroupTheory.PResidual.SimpleQuotientNormalGeneration
public import Theory.GroupTheory.PResidual.PerfectLift

/-!
# Detecting a two-core through an involution in an A₅ cover

For a two-perfect group covering A₅ with two-group kernel, a subgroup
with nontrivial image normally generates. If its commutators with the
kernel and its squares lie in a normal subgroup A of the kernel, the
induced cover modulo A is central and perfect. The checked involution
obstruction for SL₂(5) makes that cover injective, identifying the kernel
with A. All quotient maps are the original prescribed maps.

Source application: Aschbacher–Smith 14.2.16, printed p.986; the central
cover comparison is the A₅ instance of C.5.6(7), printed p.159.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace alternatingGroup
variable {D:Type*} [Group D] [Finite D]

theorem kernel_eq_of_square_normal_generator
    (f:D→*alternatingGroup (Fin 5)) (hf:Function.Surjective f)
    (hk:IsPGroup 2 f.ker) (hp:IsPPerfect 2 D)
    (A R:Subgroup D) [A.Normal] (hA:A≤f.ker)
    (hR:R.map f≠⊥) (hcomm:⁅f.ker,R⁆≤A)
    (hsq:∀r∈R,r^2∈A) : f.ker=A := by
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect D := hp.isPerfect_of_surjective_pGroup_kernel f hf hk
  have hgen:normalClosure (R:Set D)=⊤ := normalClosure_eq_top_of_pPerfect_simple_image hp f hf hk R hR
  have hc:⁅f.ker,⊤⁆≤A := by
    rw [←hgen]
    exact commutator_normalClosure_le_of_normal f.ker R A hcomm
  let q:=QuotientGroup.mk' A
  let g:=QuotientGroup.lift A f hA
  have hg:Function.Surjective g := by
    intro a
    obtain ⟨d,rfl⟩:=hf a
    exact ⟨q d,rfl⟩
  have hgker:g.ker=f.ker.map q := QuotientGroup.ker_lift A f hA
  have hgcentral:g.ker≤center (D⧸A) := by
    rw [hgker]
    rintro _ ⟨a,ha,rfl⟩
    apply mem_center_iff.mpr
    intro y
    obtain ⟨b,rfl⟩:=QuotientGroup.mk'_surjective A y
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [←map_commutatorElement]
    apply (QuotientGroup.eq_one_iff _).mpr
    rw [commutator_comm] at hc
    exact hc (commutator_mem_commutator (mem_top b) ha)
  let : Group.IsPerfect (D⧸A) := Group.IsPerfect.ofSurjective (f:=q) (QuotientGroup.mk'_surjective A)
  have hi : Function.Injective g := by
    by_contra hn
    apply hR
    apply (map_eq_bot_iff R).mpr
    intro r hr
    by_contra hrn
    apply hn
    exact injective_of_central_two_kernel_of_involution g hg hgcentral
      (hgker ▸ hk.map q) (q r) (by
        rw [←map_pow]
        exact (QuotientGroup.eq_one_iff _).mpr (hsq r hr)) hrn
  have hzero : g.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr hi
  apply le_antisymm ?_ hA
  intro x hx
  have hqx:q x∈g.ker := hx
  have hqone:q x=1 := mem_bot.mp (hzero ▸ hqx)
  exact (QuotientGroup.eq_one_iff _).mp hqone
end alternatingGroup
