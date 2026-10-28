module
public import Theory.SpecificGroups.AlternatingSix.TwoPrimaryInvolutionData
public import Theory.GroupTheory.PResidual.SimpleQuotientNormalGeneration
public import Theory.GroupTheory.PResidual.PerfectLift

/-!
# A square-generated two-primary cover of A₆

If a two-perfect group maps onto A₆ with two-group kernel and the kernel
commutes modulo a normal subgroup A with a nontrivial square-one image R,
then the whole kernel is A. Simplicity makes R normally generate; the
resulting perfect central cover of A₆ cannot be a double cover because its
noncentral involutions would contradict the two-primary involution theorem.

This is the covering-group step in Aschbacher–Smith 14.3.19(4).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace AlternatingSix
variable {D:Type*} [Group D] [Finite D]

theorem kernel_eq_of_square_normal_generator
    (f:D→*alternatingGroup (Fin 6)) (hf:Function.Surjective f)
    (hk:IsPGroup 2 f.ker) (hp:IsPPerfect 2 D)
    (A R:Subgroup D) [A.Normal] (hA:A≤f.ker)
    (hR:R.map f≠⊥) (hcomm:⁅f.ker,R⁆≤A)
    (hsq:∀r∈R,r^2∈A) : f.ker=A := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
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
  let c:PerfectCentralCovering.Cover (D⧸A) (alternatingGroup (Fin 6)) := {
    toMonoidHom:=g
    surjective:=hg
    isPerfect:=inferInstance
    ker_le_center:=hgcentral }
  have hzero:g.ker=⊥ := by
    rcases twoPrimaryInvolutionData (D⧸A) c (hgker ▸ hk.map q) with hz|⟨_,hinv⟩
    · exact hz
    · apply (hR ?_).elim
      apply (map_eq_bot_iff R).mpr
      intro r hr
      exact hinv (q r) (by
        rw [←map_pow]
        exact (QuotientGroup.eq_one_iff _).mpr (hsq r hr))
  apply le_antisymm ?_ hA
  intro x hx
  have hqx:q x∈g.ker := hx
  have hqone:q x=1 := mem_bot.mp (hzero ▸ hqx)
  exact (QuotientGroup.eq_one_iff _).mp hqone
end AlternatingSix
